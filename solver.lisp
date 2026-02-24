; solver.lisp  —  CDCL SAT Solver
;
; Heuristics implemented:
;   - Two Watched Literals (2WL) with blocking literals
;   - Unit propagation (BCP)
;   - Conflict analysis with 1-UIP clause learning
;   - Backtracking to asserting level
;   - Variable Move-To-Front (VMTF) decision heuristic
;   - Phase saving
;   - EMA-based restarts (Glucose-style)
;   - Clause deletion by LBD / activity (no GC, mark-and-skip)
;
; Literal encoding:
;   pos-lit(v) = 2*v      (positive occurrence of variable v, v >= 1)
;   neg-lit(v) = 2*v + 1  (negative occurrence)
;   lit-var(l) = l >> 1
;   lit-sign(l)= l  & 1   (0 = positive, 1 = negative)
;   negate(l)  = l XOR 1
;
; Stobj field accessor naming (ACL2 convention):
;   Scalar  foo  -> (foo solver),          (update-foo v solver)
;   Array   bar  -> (bari i solver),       (update-bari i v solver),
;                   (bar-length solver),   (resize-bar n solver)

(in-package "ACL2")

;;;; ============================================================
;;;; 1.  Solver Stobj
;;;; ============================================================

(defstobj solver

  ;; ---- Problem size ----------------------------------------
  (nv        :type (integer 0 4000000)  :initially 0)   ; num vars
  (nc        :type (integer 0 4000000)  :initially 0)   ; num orig clauses

  ;; ---- Clause database (parallel arrays, indexed by cid) ---
  ;; Literals stored flat: clause cid occupies
  ;;   ldata[cl-start[cid] .. cl-start[cid]+cl-len[cid]-1]
  ;; ldata[cl-start[cid]]   = watched literal 0
  ;; ldata[cl-start[cid]+1] = watched literal 1  (if len >= 2)
  (ldata     :type (array (unsigned-byte 30) (0))  :resizable t :initially 0)
  (cl-start  :type (array (unsigned-byte 30) (0))  :resizable t :initially 0)
  (cl-len    :type (array (unsigned-byte 30) (0))  :resizable t :initially 0)
  (cl-lbd    :type (array (unsigned-byte 30) (0))  :resizable t :initially 0)
  (cl-act    :type (array rational        (0))     :resizable t :initially 0)
  (cl-del    :type (array bit             (0))     :resizable t :initially 0)
  (ndb       :type (integer 0 20000000) :initially 0)   ; total clauses in db
  (ltop      :type (integer 0 200000000) :initially 0)  ; next free in ldata

  ;; ---- Variable state (1-indexed, size nv+1) ---------------
  (asgn      :type (array (signed-byte 8)  (0))   :resizable t :initially 0)
  ;; asgn[v]: 0=unassigned, 1=true(pos-lit satisfied), -1=false(neg-lit satisfied)
  (alev      :type (array (unsigned-byte 30) (0)) :resizable t :initially 0)
  (arsn      :type (array (signed-byte 32) (0))   :resizable t :initially -2)
  ;; arsn[v]: -2=unassigned, -1=decision, >=0 = clause id (reason)

  ;; ---- Trail -----------------------------------------------
  (trail     :type (array (unsigned-byte 30) (0)) :resizable t :initially 0)
  (trail-sz  :type (unsigned-byte 30) :initially 0)      ; fill pointer
  ;; tlim[d] = trail size just BEFORE the (d+1)-th decision was pushed
  ;;         = trail size including all of level d (but not level d+1)
  ;; tlim-sz = current decision level (number of entries in tlim)
  (tlim      :type (array (unsigned-byte 30) (0)) :resizable t :initially 0)
  (tlim-sz   :type (unsigned-byte 30) :initially 0)
  (prop-q    :type (unsigned-byte 30) :initially 0)      ; BCP queue head (index into trail)
  (dlev      :type (unsigned-byte 30) :initially 0)      ; current decision level

  ;; ---- Watch lists -----------------------------------------
  ;; watch[lit] = list of (cid . blocker-lit)
  (watch     :type (array t (0))                  :resizable t :initially nil)

  ;; ---- VMTF doubly-linked list -----------------------------
  ;; Variables 1..nv are nodes; 0 is the null/sentinel pointer.
  (vmtf-nxt  :type (array (unsigned-byte 30) (0)) :resizable t :initially 0)
  (vmtf-prv  :type (array (unsigned-byte 30) (0)) :resizable t :initially 0)
  (vmtf-hd   :type (unsigned-byte 30) :initially 0)      ; head (highest priority)
  (vmtf-stmp :type (array (unsigned-byte 30) (0)) :resizable t :initially 0)
  (vmtf-clk  :type (unsigned-byte 30) :initially 0)      ; monotone counter

  ;; ---- Phase saving ----------------------------------------
  ;; phasebits[v]: 0 = save negative, 1 = save positive
  (phasebits :type (array bit             (0))     :resizable t :initially 0)

  ;; ---- EMA restarts (Glucose-style) -----------------------
  (ema-f     :type rational :initially 0)   ; fast EMA of LBD
  (ema-s     :type rational :initially 0)   ; slow EMA of LBD
  (csr       :type (unsigned-byte 30) :initially 0) ; conflicts since restart

  ;; ---- Clause deletion ------------------------------------
  (del-lim   :type (unsigned-byte 30) :initially 1000) ; trigger threshold
  (nlrn      :type (unsigned-byte 30) :initially 0)    ; number of learned clauses
  (act-inc   :type rational :initially 1)         ; activity bump amount

  ;; ---- Temporary: seen array for conflict analysis --------
  (seen      :type (array bit             (0))     :resizable t :initially 0))

;;;; ============================================================
;;;; 2.  Literal Arithmetic  (inline-friendly macros)
;;;; ============================================================

(defmacro lit-var  (l)   `(ash ,l -1))
(defmacro lit-sign (l)   `(logand ,l 1))
(defmacro pos-lit  (v)   `(ash ,v 1))
(defmacro neg-lit  (v)   `(logior (ash ,v 1) 1))
(defmacro nlit     (l)   `(logxor ,l 1))   ; negate literal

(defun lit-val (l solver)
  ;; Return 1 if l is TRUE, -1 if FALSE, 0 if unassigned.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((v   (lit-var l))
         (av  (asgni v solver)))
    (if (= (lit-sign l) 0) av (- av))))

(defun lit-true-p (l solver)
  (declare (xargs :stobjs (solver) :mode :program))
  (= (lit-val l solver) 1))

(defun lit-false-p (l solver)
  (declare (xargs :stobjs (solver) :mode :program))
  (= (lit-val l solver) -1))

(defun lit-undef-p (l solver)
  (declare (xargs :stobjs (solver) :mode :program))
  (= (lit-val l solver) 0))

;;;; ============================================================
;;;; 3.  Clause Literal Access / Swap Helpers
;;;; ============================================================

(defun cl-lit (cid k solver)
  ;; Return the k-th literal of clause cid.
  (declare (xargs :stobjs (solver) :mode :program))
  (ldatai (+ (cl-starti cid solver) k) solver))

(defun set-cl-lit (cid k val solver)
  ;; Set the k-th literal of clause cid to val.
  (declare (xargs :stobjs (solver) :mode :program))
  (update-ldatai (+ (cl-starti cid solver) k) val solver))

(defun swap-cl-lits (cid i j solver)
  ;; Swap literals at positions i and j within clause cid.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((li (cl-lit cid i solver))
         (lj (cl-lit cid j solver))
         (solver  (set-cl-lit cid i lj solver))
         (solver  (set-cl-lit cid j li solver)))
    solver))

;;;; ============================================================
;;;; 4.  Array Initialization Helpers
;;;; ============================================================

(defun clear-asgn (v n solver)
  ;; Set asgn[v..n] := 0.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (> v n)
      solver
    (let ((solver (update-asgni v 0 solver)))
      (clear-asgn (1+ v) n solver))))

(defun clear-arsn (v n solver)
  ;; Set arsn[v..n] := -2.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (> v n)
      solver
    (let ((solver (update-arsni v -2 solver)))
      (clear-arsn (1+ v) n solver))))

(defun clear-watch (l len solver)
  ;; Set watch[l..len-1] := nil.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (>= l len)
      solver
    (let ((solver (update-watchi l nil solver)))
      (clear-watch (1+ l) len solver))))

(defun clear-seen (v n solver)
  ;; Set seen[v..n] := 0.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (> v n)
      solver
    (let ((solver (update-seeni v 0 solver)))
      (clear-seen (1+ v) n solver))))

;;;; ============================================================
;;;; 5.  VMTF Operations
;;;; ============================================================

; The VMTF list is doubly-linked.  0 is the null/end sentinel.
; vmtf-hd = highest-priority variable (or 0 if empty).
; vmtf-nxt[v] = next variable (lower priority), 0 if v is the tail.
; vmtf-prv[v] = previous variable (higher priority), 0 if v is the head.

(defun vmtf-link-init (v n solver)
  ;; Build initial chain: 1 <-> 2 <-> ... <-> n  (head=1, tail=n)
  (declare (xargs :stobjs (solver) :mode :program))
  (if (> v n)
      solver
    (let* ((prv  (if (= v 1) 0 (1- v)))
           (nxt  (if (= v n) 0 (1+ v)))
           (solver    (update-vmtf-nxti v nxt solver))
           (solver    (update-vmtf-prvi v prv solver))
           (solver    (update-vmtf-stmpi v 0 solver)))
      (vmtf-link-init (1+ v) n solver))))

(defun vmtf-detach (v solver)
  ;; Remove variable v from its current position in the list.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((prv (vmtf-prvi v solver))
         (nxt (vmtf-nxti v solver))
         (solver   (if (> prv 0)
                  (update-vmtf-nxti prv nxt solver)
                solver))
         (solver   (if (> nxt 0)
                  (update-vmtf-prvi nxt prv solver)
                solver))
         (solver   (if (= (vmtf-hd solver) v)
                  (update-vmtf-hd nxt solver)
                solver)))
    solver))

(defun vmtf-push-front (v solver)
  ;; Insert v at the head of the VMTF list (highest priority).
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((old-hd (vmtf-hd solver))
         (solver      (update-vmtf-nxti v old-hd solver))
         (solver      (update-vmtf-prvi v 0 solver))
         (solver      (if (> old-hd 0)
                     (update-vmtf-prvi old-hd v solver)
                   solver))
         (solver      (update-vmtf-hd v solver))
         ;; Update stamp
         (tick   (1+ (vmtf-clk solver)))
         (solver      (update-vmtf-clk tick solver))
         (solver      (update-vmtf-stmpi v tick solver)))
    solver))

(defun vmtf-move-to-front (v solver)
  ;; Move variable v to the front of the VMTF list.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (= v (vmtf-hd solver))
      solver  ; already at front
    (let* ((solver (vmtf-detach v solver))
           (solver (vmtf-push-front v solver)))
      solver)))

(defun vmtf-bump-list (lits solver)
  ;; Move all variables in the literal list 'lits' to the front.
  ;; Called after conflict analysis with the learned clause literals.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (endp lits)
      solver
    (let ((solver (vmtf-move-to-front (lit-var (car lits)) solver)))
      (vmtf-bump-list (cdr lits) solver))))

(defun vmtf-next-unassigned (v solver)
  ;; Walk VMTF list from v; return first unassigned variable, or 0.
  (declare (xargs :stobjs (solver) :mode :program))
  (cond
    ((= v 0) 0)
    ((= (asgni v solver) 0) v)          ; unassigned
    (t (vmtf-next-unassigned (vmtf-nxti v solver) solver))))

;;;; ============================================================
;;;; 6.  Trail and Assignment (enqueue)
;;;; ============================================================

(defun enqueue (lit reason solver)
  ;; Assign literal 'lit' with given reason (clause-id or -1 for decision).
  ;; Does NOT check for prior assignment — caller must ensure lit is unassigned.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((v   (lit-var lit))
         (val (if (= (lit-sign lit) 0) 1 -1))
         (solver   (update-asgni  v val solver))
         (solver   (update-alevi  v (dlev solver) solver))
         (solver   (update-arsni  v reason solver))
         (te  (trail-sz solver))
         (solver   (update-traili te lit solver))
         (solver   (update-trail-sz (1+ te) solver)))
    solver))

;;;; ============================================================
;;;; 7.  Watch List Helpers
;;;; ============================================================

(defun push-watch (lit cid blocker solver)
  ;; Add a watch entry for 'lit': when lit becomes FALSE, check clause cid.
  (declare (xargs :stobjs (solver) :mode :program))
  (update-watchi lit (cons (cons cid blocker) (watchi lit solver)) solver))

(defun install-watches (cid solver)
  ;; Install 2WL for clause cid (must have length >= 2).
  ;; Watches: watch[lits[0]] and watch[lits[1]].
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((l0 (cl-lit cid 0 solver))
         (l1 (cl-lit cid 1 solver))
         (solver  (push-watch l0 cid l1 solver))
         (solver  (push-watch l1 cid l0 solver)))
    solver))

;;;; ============================================================
;;;; 8.  Solver Initialization
;;;; ============================================================

(defun count-lits (clauses acc)
  ;; Total number of literals across all clauses.
  (declare (xargs :mode :program))
  (if (endp clauses)
      acc
    (count-lits (cdr clauses) (+ acc (length (car clauses))))))

(defun add-clause-lits (lits-list base-idx solver)
  ;; Write literals from lits-list into ldata starting at base-idx.
  ;; Returns (mv unsat solver) where unsat=t if lits-list is empty (empty clause).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (endp lits-list)
      (mv nil solver)
    (let* ((solver (update-ldatai base-idx (car lits-list) solver)))
      (add-clause-lits (cdr lits-list) (1+ base-idx) solver))))

(defun load-clause (lits-list cid solver)
  ;; Add clause with given literals to the database at position cid.
  ;; Returns (mv result solver) where result is :unsat, :unit-enqueued, or :ok.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((len (length lits-list)))
    (cond
      ;; Empty clause -> immediate UNSAT
      ((= len 0)
       (mv :unsat solver))
      ;; Unit clause at root level: enqueue directly
      ((= len 1)
       (let* ((l   (car lits-list))
              (top (ltop solver))
              (solver   (update-cl-starti cid top solver))
              (solver   (update-cl-leni   cid 1   solver))
              (solver   (update-cl-lbdi   cid 1   solver))
              (solver   (update-cl-acti   cid 0 solver))
              (solver   (update-cl-deli   cid 0   solver))
              (solver   (update-ldatai top l solver))
              (solver   (update-ltop (1+ top) solver))
              (solver   (update-ndb (1+ (ndb solver)) solver)))
         (if (lit-false-p l solver)
           (mv :unsat solver)
         (if (lit-undef-p l solver)
             (let ((solver (enqueue l -1 solver)))
               (mv :unit-enqueued solver))
            (mv :ok solver)))))
      ;; General clause (length >= 2)
      (t
       (let* ((top (ltop solver))
              (solver   (update-cl-starti cid top solver))
              (solver   (update-cl-leni   cid len solver))
              (solver   (update-cl-lbdi   cid 0   solver))
              (solver   (update-cl-acti   cid 0 solver))
              (solver   (update-cl-deli   cid 0   solver)))
         (mv-let (ignore solver)
           (add-clause-lits lits-list top solver)
           (declare (ignore ignore))
           (let* ((solver (update-ltop (+ top len) solver))
                  (solver (update-ndb (1+ (ndb solver)) solver))
                  (solver (install-watches cid solver)))
             (mv :ok solver))))))))

(defun load-clauses (clauses cid solver)
  ;; Load list of clauses (each a list of literals) into the solver.
  ;; Returns (mv :unsat-or-ok solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (endp clauses)
      (mv :ok solver)
    (mv-let (res solver)
      (load-clause (car clauses) cid solver)
      (if (eq res :unsat)
          (mv :unsat solver)
        (load-clauses (cdr clauses) (1+ cid) solver)))))

(defun init-solver (n clauses solver)
  ;; n       = number of variables
  ;; clauses = list of lists of (unsigned-byte 30) literals
  ;; Returns (mv :sat/:unsat/:ok solver)
  ;;   :ok means initialized, ready to run CDCL
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((nc-orig  (length clauses))
         (nl-total (count-lits clauses 0))
         ;; Reserve extra space for learned clauses
         (db-cap   (+ nc-orig 200000))
         (ld-cap   (+ nl-total 2000000))
         (var-cap  (+ n 1))
         (lit-cap  (* 2 (+ n 1)))

         ;; Set problem size
         (solver (update-nv n solver))
         (solver (update-nc nc-orig solver))

         ;; Resize clause database arrays
         (solver (resize-ldata    ld-cap  solver))
         (solver (resize-cl-start db-cap  solver))
         (solver (resize-cl-len   db-cap  solver))
         (solver (resize-cl-lbd   db-cap  solver))
         (solver (resize-cl-act   db-cap  solver))
         (solver (resize-cl-del   db-cap  solver))
         (solver (update-ndb 0 solver))
         (solver (update-ltop 0 solver))

         ;; Resize and clear variable arrays
         (solver (resize-asgn var-cap solver))
         (solver (resize-alev var-cap solver))
         (solver (resize-arsn var-cap solver))
         (solver (clear-asgn 1 n solver))
         (solver (clear-arsn 1 n solver))

         ;; Resize and clear trail
         (solver (resize-trail (1+ n) solver))
         (solver (update-trail-sz 0 solver))
         (solver (resize-tlim (1+ n) solver))
         (solver (update-tlim-sz 0 solver))
         (solver (update-prop-q 0 solver))
         (solver (update-dlev 0 solver))

         ;; Resize and clear watch lists
         (solver (resize-watch lit-cap solver))
         (solver (clear-watch 0 lit-cap solver))

         ;; Resize and init VMTF
         (solver (resize-vmtf-nxt  var-cap solver))
         (solver (resize-vmtf-prv  var-cap solver))
         (solver (resize-vmtf-stmp var-cap solver))
         (solver (update-vmtf-hd 1 solver))
         (solver (update-vmtf-clk 0 solver))
         (solver (vmtf-link-init 1 n solver))

         ;; Resize phase and seen
         (solver (resize-phasebits var-cap solver))
         (solver (resize-seen  var-cap solver))
         (solver (clear-seen   1 n solver))

         ;; Reset EMA and deletion state
         (solver (update-ema-f 0 solver))
         (solver (update-ema-s 0 solver))
         (solver (update-csr 0 solver))
         (solver (update-del-lim (+ nc-orig 1000) solver))
         (solver (update-nlrn 0 solver))
         (solver (update-act-inc 1 solver)))

    ;; Load all clauses
    (load-clauses clauses 0 solver)))

;;;; ============================================================
;;;; 9.  Unit Propagation (BCP with 2WL)
;;;; ============================================================

; Returns (mv conflict-cid solver) where conflict-cid = -1 means no conflict.

(defun find-new-watcher (cid start len solver)
  ;; Search clause cid'solver literals from position 'start' for a non-false one.
  ;; Returns index (>= 0) or -1.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (>= start len)
      -1
    (if (not (lit-false-p (cl-lit cid start solver) solver))
        start
      (find-new-watcher cid (1+ start) len solver))))

(defun process-watch-list (ws fp kept conflict solver)
  ;; Process the watch list 'ws' for false literal fp.
  ;; fp  = the literal that just became FALSE (it was being watched by each clause in ws).
  ;; kept = accumulator (in reverse order) of watch entries to keep in watch[fp].
  ;; conflict = -1 or the conflicting clause id (stops propagation, drains rest).
  ;; Returns (mv kept conflict solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (atom ws)
      (mv kept conflict solver)
    (let* ((w    (car ws))
           (rest (cdr ws))
           (cid  (car w))
           (blkr (cdr w)))
      (cond
        ;; Deleted clause: discard entry silently
        ((= (cl-deli cid solver) 1)
         (process-watch-list rest fp kept conflict solver))

        ;; Already have a conflict: just drain remaining watches unchanged
        ((not (= conflict -1))
         (mv (revappend rest (cons w kept)) conflict solver))

        ;; Fast path: blocker literal is TRUE -> clause satisfied
        ((lit-true-p blkr solver)
         (process-watch-list rest fp (cons w kept) conflict solver))

        ;; Need to examine the clause
        (t
         (let* ((len (cl-leni cid solver)))
           ;; Ensure ldata[cl-start[cid] + 1] = fp  (make fp the second watcher)
           ;; so that ldata[cl-start[cid] + 0] is the "other" watcher.
           (let* ((solver (if (= (cl-lit cid 0 solver) fp)
                              (swap-cl-lits cid 0 1 solver)
                            solver))
                  (other (cl-lit cid 0 solver)))  ; the non-fp watcher
             (cond
               ;; Other watcher is TRUE: clause satisfied
               ((lit-true-p other solver)
                (process-watch-list rest fp
                                    (cons (cons cid other) kept)
                                    conflict solver))
               ;; Search positions 2..len-1 for a non-false literal
               (t
                (let* ((k (find-new-watcher cid 2 len solver)))
                  (if (>= k 0)
                      ;; Found: move ldata[cl-start+k] to position 1 (new watcher)
                      (let* ((new-w (cl-lit cid k solver))
                             (solver (swap-cl-lits cid 1 k solver))
                             ;; new watcher = new-w (now at position 1)
                             ;; Add watch entry: when new-w becomes false, check cid
                             (solver (push-watch new-w cid other solver)))
                        ;; Do NOT keep entry in watch[fp] (moved to watch[new-w])
                        (process-watch-list rest fp kept conflict solver))
                    ;; No new watcher: clause is unit or conflicting
                    (let* ((kept2 (cons w kept)))
                      (if (lit-undef-p other solver)
                          ;; Unit: propagate 'other'
                          (let* ((solver (enqueue other cid solver)))
                            (process-watch-list rest fp kept2 -1 solver))
                        ;; Conflict: 'other' is also false
                        (mv (revappend rest kept2) cid solver))))))))))))))

(defun propagate-step (solver)
  ;; Process one literal from the BCP queue.
  ;; Returns (mv conflict-cid solver).  conflict-cid = -1 means no conflict yet.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((q    (traili (prop-q solver) solver))   ; dequeue literal q (TRUE)
         (solver    (update-prop-q (1+ (prop-q solver)) solver))
         (fp   (nlit q))               ; fp = neg(q) = literal that just became FALSE
         (old  (watchi fp solver))
         (solver    (update-watchi fp nil solver)))  ; temporarily clear; rebuild below
    (mv-let (new-kept conflict solver)
      (process-watch-list old fp nil -1 solver)
      ;; Prepend rebuilt list (reversed) to whatever was added during processing
      ;; (handles the edge case where new-w = neg(fp) = q was added to watch[fp])
      (let* ((solver (update-watchi fp (revappend new-kept (watchi fp solver)) solver)))
        (mv conflict solver)))))

(defun propagate (solver)
  ;; Run BCP until fixpoint or conflict.
  ;; Returns (mv conflict-cid solver).  conflict-cid = -1 means no conflict.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (= (prop-q solver) (trail-sz solver))
      (mv -1 solver)  ; queue empty, no conflict
    (mv-let (conflict solver)
      (propagate-step solver)
      (if (not (= conflict -1))
          (mv conflict solver)
        (propagate solver)))))

;;;; ============================================================
;;;; 10.  Conflict Analysis  (1-UIP)
;;;; ============================================================

; Returns (mv learned-lits bt-level lbd solver)
;   learned-lits: list of literals; [0] = asserting literal
;   bt-level    : backtrack level
;   lbd         : Literal Block Distance of learned clause

(defun process-reason-lits (lits k len cur-lev counter learned solver)
  ;; Iterate over literals of a clause (lits = list), mark seen, collect non-current-level.
  ;; Returns (mv counter learned solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (>= k len)
      (mv counter learned solver)
    (let* ((l (car lits))
           (v (lit-var l))
           (lv (alevi v solver)))
      (if (= (seeni v solver) 1)
          ;; Already seen
          (process-reason-lits (cdr lits) (1+ k) len cur-lev counter learned solver)
        (let* ((solver (update-seeni v 1 solver)))
          (if (= lv cur-lev)
              ;; At current level: increment counter (will be resolved)
              (process-reason-lits (cdr lits) (1+ k) len cur-lev (1+ counter) learned solver)
            ;; Below current level: add neg(l) to learned clause
            (if (> lv 0)
                (process-reason-lits (cdr lits) (1+ k) len cur-lev counter
                                     (cons (nlit l) learned) solver)
              ;; Level 0: skip (already unit-propagated permanently)
              (process-reason-lits (cdr lits) (1+ k) len cur-lev counter learned solver))))))))

; Because ACL2 doesn't support named let-loops, use a recursive helper:
(defun clause-lits-loop (k len st solver acc)
  (declare (xargs :stobjs (solver) :mode :program))
  (if (= k len)
      (reverse acc)
    (clause-lits-loop (1+ k) len st solver
                      (cons (ldatai (+ st k) solver) acc))))

(defun clause-lits-as-list (cid solver)
  (declare (xargs :stobjs (solver) :mode :program))
  (clause-lits-loop 0 (cl-leni cid solver) (cl-starti cid solver) solver nil))

(defun find-uip-step (trail-idx cur-lev counter learned solver)
  ;; Walk trail backwards from trail-idx to find the 1-UIP.
  ;; Returns (mv uip-lit learned solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (< trail-idx 0)
      ;; Should not happen in a correct solver
      (mv 0 learned solver)
    (let* ((l (traili trail-idx solver))
           (v (lit-var l)))
      (if (= (seeni v solver) 0)
          ;; Not seen: skip
          (find-uip-step (1- trail-idx) cur-lev counter learned solver)
        ;; Seen: this is a candidate
        (let* ((solver (update-seeni v 0 solver)))   ; clear seen
          (if (= counter 1)
              ;; counter=1: l is the 1-UIP
              (mv l learned solver)
            ;; Resolve: process reason of v
            (let* ((r (arsni v solver)))
              (if (= r -1)
                  ;; Decision literal (no reason clause): resolve done
                  (mv l learned solver)
                ;; Resolve against reason clause of v
                (let* ((reason-lits (clause-lits-as-list r solver)))
                  (mv-let (new-counter new-learned solver)
                    (process-reason-lits reason-lits 0 (length reason-lits)
                                         cur-lev (1- counter) learned solver)
                    (find-uip-step (1- trail-idx) cur-lev new-counter new-learned solver)))))))))))

(defun distinct-levels (lits solver acc)
  ;; Count distinct non-zero decision levels in lits.
  ;; acc = list of already-seen levels.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (endp lits)
      (length acc)
    (let* ((lv (alevi (lit-var (car lits)) solver)))
      (if (or (= lv 0) (member lv acc))
          (distinct-levels (cdr lits) solver acc)
        (distinct-levels (cdr lits) solver (cons lv acc))))))

(defun bt-level-of (lits solver best-lv best-idx cur-idx)
  ;; Find the literal in lits (skipping index 0 = asserting) with highest level.
  ;; Returns that level (for the second watcher position).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (endp lits)
      (mv best-lv best-idx)
    (let* ((lv (alevi (lit-var (car lits)) solver)))
      (if (> lv best-lv)
          (bt-level-of (cdr lits) solver lv cur-idx (1+ cur-idx))
        (bt-level-of (cdr lits) solver best-lv best-idx (1+ cur-idx))))))

(defun list-swap (lst i j)
  ;; Swap elements at positions i and j in list lst (0-indexed).
  (declare (xargs :mode :program))
  (let* ((a   (nth i lst))
         (b   (nth j lst))
         (lst (update-nth i b lst))
         (lst (update-nth j a lst)))
    lst))

(defun analyze (conflict-cid solver)
  ;; Analyze conflict at clause conflict-cid.
  ;; Returns (mv learned-lits bt-level lbd solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((cur-lev (dlev solver))
         ;; Seed: process conflict clause literals
         (conf-lits (clause-lits-as-list conflict-cid solver)))
    (mv-let (counter learned solver)
      (process-reason-lits conf-lits 0 (length conf-lits) cur-lev 0 nil solver)
      ;; Walk trail backwards to find 1-UIP
      (mv-let (uip learned solver)
        (find-uip-step (1- (trail-sz solver)) cur-lev counter learned solver)
        ;; Build learned clause: asserting literal is neg(uip), rest is learned
        (let* ((asserting  (nlit uip))
               (all-lits   (cons asserting learned))
               ;; Compute backtrack level = max level in all-lits[1..]
               ;; and reorder so that literal at bt-level is at position 1
               (lbd        (distinct-levels all-lits solver nil)))
          (if (endp learned)
              ;; Unit learned clause (empty implication graph)
              (mv all-lits 0 lbd solver)
            (mv-let (bt-lv bt-idx)
              (bt-level-of learned solver 0 0 1)  ; search learned (indices 1..)
              ;; Swap the bt-level literal to position 1 in all-lits
              (let* ((all-lits (list-swap all-lits 1 (1+ bt-idx))))  ; +1 because all-lits has asserting at 0
                (mv all-lits bt-lv lbd solver)))))))))

(defun clear-seen-for-lits (lits solver)
  ;; Clear seen[v] for each variable in lits.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (endp lits)
      solver
    (let ((solver (update-seeni (lit-var (car lits)) 0 solver)))
      (clear-seen-for-lits (cdr lits) solver))))

;;;; ============================================================
;;;; 11.  Backtracking  (with Phase Saving)
;;;; ============================================================

(defun unassign-trail-from (idx target-sz solver)
  ;; Undo trail assignments from position trail-sz-1 down to target-sz.
  ;; Also saves phase and clears assignment arrays.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (<= idx (1- target-sz))
      solver
    (let* ((l  (traili idx solver))
           (v  (lit-var l))
           ;; Save phase: positive lit -> phasebits=1, negative -> phasebits=0
           (ph (if (= (lit-sign l) 0) 1 0))
           (solver  (update-phasebitsi  v ph solver))
           ;; Unassign
           (solver  (update-asgni   v 0  solver))
           (solver  (update-arsni   v -2 solver))
           ;; Move to front in VMTF (re-prioritize for future decisions)
           (solver  (vmtf-move-to-front v solver)))
      (unassign-trail-from (1- idx) target-sz solver))))

(defun backtrack (target-lev solver)
  ;; Undo all assignments above target-lev.
  ;; Backtrack to level target-lev: keep trail[0..tlim[target-lev]-1].
  (declare (xargs :stobjs (solver) :mode :program))
  (let* (;; Target trail size: if target-lev = 0, keep root propagations.
         ;; tlim[d] = trail size at END of level d.
         ;; After push of level d+1 decision, we record tlim[d] = trail-sz.
         ;; Backtracking to level L: new trail-sz = tlim[L].
         ;; If L=0 and tlim-sz=0 (never made decisions), trail-sz stays 0.
         ;; Actually: let's clarify.
         ;; tlim[0] = trail size before 1st decision = end of level-0 propagations
         ;; tlim[1] = trail size before 2nd decision = end of level-1
         ;; To keep level L: we want trail[0..tlim[L]-1]
         ;;   = tlim[L] (0-based: tlim[L] = trail size after level L, before level L+1 decision)
         ;; But our tlim is 0-indexed: tlim[d] = trail size before decision d+1 = end of level d
         ;; Wait: tlim[0] set when making 1st decision = trail size at that moment = end of level 0
         ;; To backtrack to level 0: keep trail[0..tlim[0]-1]? No, tlim[0] includes level 0.
         ;; After backtrack to level 0: trail has root propagations = tlim[0] elements. ✓
         ;; To backtrack to level L: new trail-sz = tlim[L]. (tlim is 0-indexed, level L = tlim[L])
         ;; But tlim has tlim-sz entries: tlim[0..tlim-sz-1].
         ;; dlev = tlim-sz (they're kept in sync).
         ;; So to backtrack to L: if L < dlev, new-ts = tlim[L]; if L=0 & tlim-sz=0, new-ts=0.
         (tgt-ts2 (if (< target-lev (tlim-sz solver))
                      (tlimi target-lev solver)
                    0))
         (cur-ts  (trail-sz solver))
         (solver       (unassign-trail-from (1- cur-ts) tgt-ts2 solver))
         (solver       (update-trail-sz   tgt-ts2 solver))
         (solver       (update-prop-q     tgt-ts2 solver))
         (solver       (update-dlev       target-lev solver))
         (solver       (update-tlim-sz    target-lev solver)))
    solver))

;;;; ============================================================
;;;; 12.  Adding a Learned Clause
;;;; ============================================================

(defun add-clause-lits-to-db (lits-list base solver)
  ;; Write literals from lits-list starting at ldata[base].
  (declare (xargs :stobjs (solver) :mode :program))
  (if (endp lits-list)
      solver
    (let ((solver (update-ldatai base (car lits-list) solver)))
      (add-clause-lits-to-db (cdr lits-list) (1+ base) solver))))

(defun add-learned-clause (lits-list lbd solver)
  ;; lits-list: list of literals.  lits[0]=asserting, lits[1]=bt-level literal.
  ;; Returns (mv cid solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((len  (length lits-list))
         (cid  (ndb solver))
         (top  (ltop solver))
         ;; Write literals into ldata
         (solver    (add-clause-lits-to-db lits-list top solver))
         ;; Set clause metadata
         (solver    (update-cl-starti cid top solver))
         (solver    (update-cl-leni   cid len solver))
         (solver    (update-cl-lbdi   cid lbd solver))
         (solver    (update-cl-acti   cid (act-inc solver) solver))
         (solver    (update-cl-deli   cid 0 solver))
         (solver    (update-ltop  (+ top len) solver))
         (solver    (update-ndb   (1+ cid) solver))
         (solver    (update-nlrn  (1+ (nlrn solver)) solver))
         ;; Install watches (lits[0] and lits[1])
         (solver    (if (>= len 2)
                        (install-watches cid solver)
                      solver)))
    (mv cid solver)))

;;;; ============================================================
;;;; 13.  Decision
;;;; ============================================================

(defun decide (solver)
  ;; Pick next decision literal using VMTF + phase saving.
  ;; Returns (mv :sat solver) if all variables assigned, else (mv :continue solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((v (vmtf-next-unassigned (vmtf-hd solver) solver)))
    (if (= v 0)
        (mv :sat solver)   ; all variables assigned
      (let* (;; Phase saving: use saved phase
             (ph  (phasebitsi v solver))
             (lit (if (= ph 1) (pos-lit v) (neg-lit v)))
             ;; New decision level
             (lev (1+ (dlev solver)))
             ;; Record trail limit for this new level
             (tlsz (tlim-sz solver))
             (solver   (update-tlimi tlsz (trail-sz solver) solver))
             (solver   (update-tlim-sz (1+ tlsz) solver))
             (solver   (update-dlev lev solver))
             ;; Enqueue decision
             (solver   (enqueue lit -1 solver)))
        (mv :continue solver)))))

;;;; ============================================================
;;;; 14.  EMA-Based Restarts
;;;; ============================================================

(defconst *ema-fast-alpha* 3/100)   ; fast window ~33 conflicts
(defconst *ema-slow-alpha* 1/100000)   ; slow window ~100k conflicts
(defconst *restart-margin* 5/4)
(defconst *restart-min-conflicts* 50)

(defun update-ema (lbd solver)
  ;; Update fast and slow EMA with new LBD value.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((af  *ema-fast-alpha*)
         (as  *ema-slow-alpha*)
         (f   (+ (* (- 1 af) (ema-f solver)) (* af lbd)))
         (sl  (+ (* (- 1 as) (ema-s solver)) (* as lbd)))
         (solver   (update-ema-f f solver))
         (solver   (update-ema-s sl solver))
         (solver   (update-csr (1+ (csr solver)) solver)))
    solver))

(defun restart-p (solver)
  ;; Return t if a restart should be triggered.
  (declare (xargs :stobjs (solver) :mode :program))
  (and (> (csr solver) *restart-min-conflicts*)
       (> (ema-f solver) (* *restart-margin* (ema-s solver)))))

(defun do-restart (solver)
  ;; Execute a restart: backtrack to level 0, reset conflict counter.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((solver (backtrack 0 solver))
         (solver (update-csr 0 solver)))
    solver))

;;;; ============================================================
;;;; 15.  Clause Activity and Deletion
;;;; ============================================================

(defconst *act-decay* 999/1000)
(defconst *act-rescale* (/ 1 (expt 10 20)))
(defconst *act-max*    (expt 10 20))
(defconst *lbd-keep*   2)     ; keep clauses with LBD <= this (glue clauses)

(defun rescale-all-acts (cid end solver)
  ;; Multiply all clause activities by act-rescale, and scale act-inc.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (>= cid end)
      (update-act-inc (* (act-inc solver) *act-rescale*) solver)
    (let* ((solver (update-cl-acti cid (* (cl-acti cid solver) *act-rescale*) solver)))
      (rescale-all-acts (1+ cid) end solver))))

(defun bump-clause-act (cid solver)
  ;; Bump activity of clause cid by act-inc.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((new-a (+ (cl-acti cid solver) (act-inc solver)))
         (solver     (update-cl-acti cid new-a solver)))
    ;; Rescale all activities if overflow
    (if (> new-a *act-max*)
        (rescale-all-acts (nc solver) (ndb solver) solver)
      solver)))

(defun clause-locked-p (cid solver)
  ;; A clause is locked if it is the reason for some currently assigned variable.
  ;; Check: lits[0] is true AND arsn[lit-var(lits[0])] = cid.
  (declare (xargs :stobjs (solver) :mode :program))
  (let* ((l0  (cl-lit cid 0 solver))
         (v0  (lit-var l0)))
    (and (lit-true-p l0 solver)
         (= (arsni v0 solver) cid))))

(defun collect-deletable (cid end nc acc solver)
  ;; Collect learned clause ids that are candidates for deletion.
  ;; Returns list of (cid . score) where score = (lbd . neg-act).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (>= cid end)
      acc
    (let* ((del?  (= (cl-deli cid solver) 1))
           (orig? (< cid nc))
           (lbd   (cl-lbdi cid solver))
           (locked? (clause-locked-p cid solver)))
      (if (or del? orig? locked? (<= lbd *lbd-keep*))
          (collect-deletable (1+ cid) end nc acc solver)
        (collect-deletable (1+ cid) end nc
                           (cons (cons cid (cons lbd (- (cl-acti cid solver)))) acc)
                           solver)))))

(defun score< (a b)
  ;; Compare two (cid . (lbd . neg-act)) entries.
  (declare (xargs :mode :program))
  (let* ((la (cadr a)) (lb (cadr b))
         (aa (cddr a)) (ab (cddr b)))
    (or (< la lb)
        (and (= la lb) (< aa ab)))))

(defun insert-by-score (x sorted)
  (declare (xargs :mode :program))
  (if (endp sorted)
      (list x)
    (if (score< x (car sorted))
        (cons x sorted)
      (cons (car sorted) (insert-by-score x (cdr sorted))))))

(defun sort-by-score (alist)
  ;; Sort by (lbd, neg-act) ascending = worst clauses first.
  ;; Using a simple insertion sort (good enough for moderate lists).
  (declare (xargs :mode :program))
  (if (endp alist)
      nil
    (insert-by-score (car alist) (sort-by-score (cdr alist)))))

(defun mark-deleted (candidates target solver)
  ;; Mark the first 'target' candidates as deleted.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (or (endp candidates) (<= target 0))
      solver
    (let* ((cid (caar candidates))
           (solver   (update-cl-deli cid 1 solver))
           (solver   (update-nlrn (max 0 (1- (nlrn solver))) solver)))
      (mark-deleted (cdr candidates) (1- target) solver))))

(defun maybe-delete-clauses (solver)
  ;; Delete approximately half of low-quality learned clauses if threshold exceeded.
  (declare (xargs :stobjs (solver) :mode :program))
  (if (< (nlrn solver) (del-lim solver))
      solver
    (let* ((nc-orig    (nc solver))
           (candidates (collect-deletable nc-orig (ndb solver) nc-orig nil solver))
           (sorted     (sort-by-score candidates))
           (target     (floor (length sorted) 2))
           (solver          (mark-deleted sorted target solver))
           ;; Double deletion threshold
           (solver          (update-del-lim (* 2 (del-lim solver)) solver)))
      solver)))

;;;; ============================================================
;;;; 16.  Main CDCL Loop
;;;; ============================================================

; Result codes:
;   :sat   - formula is satisfiable (full assignment on trail)
;   :unsat - formula is unsatisfiable

(defun cdcl-inner (solver)
  ;; Inner loop: BCP + conflict analysis until no conflict.
  ;; Returns (mv :continue/:unsat solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (mv-let (conflict solver)
    (propagate solver)
    (if (= conflict -1)
        ;; No conflict: BCP quiescent
        (mv :continue solver)
      ;; Conflict found
      (if (= (dlev solver) 0)
          ;; Conflict at root level -> UNSAT
          (mv :unsat solver)
        ;; Analyze conflict
        (mv-let (learned bt-lev lbd solver)
          (analyze conflict solver)
          ;; Clear seen bits for all learned literals
          (let* ((solver (clear-seen-for-lits learned solver)))
            ;; Update EMA
            (let* ((solver (update-ema lbd solver)))
              ;; Backtrack to asserting level
              (let* ((solver (backtrack bt-lev solver)))
                ;; Add learned clause
                (mv-let (cid solver)
                  (add-learned-clause learned lbd solver)
                  ;; Bump learned clause activity
                  (let* ((solver (bump-clause-act cid solver))
                         ;; Bump VMTF for all variables in learned clause
                         (solver (vmtf-bump-list learned solver))
                         ;; Enqueue asserting literal (learned[0])
                         (solver (enqueue (car learned) cid solver))
                         ;; Restart check
                         (solver (if (restart-p solver) (do-restart solver) solver))
                         ;; Clause deletion check
                         (solver (maybe-delete-clauses solver)))
                    ;; Continue inner loop
                    (cdcl-inner solver)))))))))))

(defun cdcl-outer (solver)
  ;; Outer loop: make decisions, run inner loop.
  ;; Returns (mv :sat/:unsat solver).
  (declare (xargs :stobjs (solver) :mode :program))
  (mv-let (dec-res solver)
    (decide solver)
    (if (eq dec-res :sat)
        (mv :sat solver)   ; all variables assigned, no conflict
      ;; Decision made; run BCP + conflict resolution
      (mv-let (inner-res solver)
        (cdcl-inner solver)
        (if (eq inner-res :unsat)
            (mv :unsat solver)
          (cdcl-outer solver))))))

(defun cdcl-solve (n clauses solver)
  ;; Top-level solver entry point.
  ;; n       = number of variables (positive integer)
  ;; clauses = list of lists of literals (pos-lit or neg-lit)
  ;; Returns (mv result solver) where result is :sat, :unsat.
  (declare (xargs :stobjs (solver) :mode :program))
  (mv-let (init-res solver)
    (init-solver n clauses solver)
    (if (eq init-res :unsat)
        (mv :unsat solver)
      ;; Root-level BCP (unit propagation of root-level facts)
      (mv-let (conflict solver)
        (propagate solver)
        (if (not (= conflict -1))
            (mv :unsat solver)
          (cdcl-outer solver))))))

;;;; ============================================================
;;;; 17.  Model Extraction
;;;; ============================================================

(defun extract-model (v n solver acc)
  ;; Collect the satisfying assignment as an alist ((var . bool) ...).
  (declare (xargs :stobjs (solver) :mode :program))
  (if (> v n)
      acc
    (let* ((av (asgni v solver))
           (entry (cons v (= av 1))))
      (extract-model (1+ v) n solver (cons entry acc)))))

(defun get-model (solver)
  ;; Return the satisfying assignment as an alist (1-indexed variables).
  (declare (xargs :stobjs (solver) :mode :program))
  (extract-model 1 (nv solver) solver nil))
