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
;   Scalar  foo  -> (foo s),          (update-foo v s)
;   Array   bar  -> (bari i s),       (update-bari i v s),
;                   (bar-length s),   (resize-bar n s)

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
  (cl-act    :type (array single-float    (0))     :resizable t :initially 0.0)
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
  ;; phase[v]: 0 = save negative, 1 = save positive
  (phase     :type (array bit             (0))     :resizable t :initially 0)

  ;; ---- EMA restarts (Glucose-style) -----------------------
  (ema-f     :type single-float :initially 0.0)   ; fast EMA of LBD
  (ema-s     :type single-float :initially 0.0)   ; slow EMA of LBD
  (csr       :type (unsigned-byte 30) :initially 0) ; conflicts since restart

  ;; ---- Clause deletion ------------------------------------
  (del-lim   :type (unsigned-byte 30) :initially 1000) ; trigger threshold
  (nlrn      :type (unsigned-byte 30) :initially 0)    ; number of learned clauses
  (act-inc   :type single-float :initially 1.0)         ; activity bump amount

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

(defun lit-val (l s)
  ;; Return 1 if l is TRUE, -1 if FALSE, 0 if unassigned.
  (declare (xargs :stobjs s :mode :program))
  (let* ((v   (lit-var l))
         (av  (asgni v s)))
    (if (= (lit-sign l) 0) av (- av))))

(defun lit-true-p (l s)
  (declare (xargs :stobjs s :mode :program))
  (= (lit-val l s) 1))

(defun lit-false-p (l s)
  (declare (xargs :stobjs s :mode :program))
  (= (lit-val l s) -1))

(defun lit-undef-p (l s)
  (declare (xargs :stobjs s :mode :program))
  (= (lit-val l s) 0))

;;;; ============================================================
;;;; 3.  Clause Literal Access / Swap Helpers
;;;; ============================================================

(defun cl-lit (cid k s)
  ;; Return the k-th literal of clause cid.
  (declare (xargs :stobjs s :mode :program))
  (ldatai (+ (cl-starti cid s) k) s))

(defun set-cl-lit (cid k val s)
  ;; Set the k-th literal of clause cid to val.
  (declare (xargs :stobjs s :mode :program))
  (update-ldatai (+ (cl-starti cid s) k) val s))

(defun swap-cl-lits (cid i j s)
  ;; Swap literals at positions i and j within clause cid.
  (declare (xargs :stobjs s :mode :program))
  (let* ((li (cl-lit cid i s))
         (lj (cl-lit cid j s))
         (s  (set-cl-lit cid i lj s))
         (s  (set-cl-lit cid j li s)))
    s))

;;;; ============================================================
;;;; 4.  Array Initialization Helpers
;;;; ============================================================

(defun clear-asgn (v n s)
  ;; Set asgn[v..n] := 0.
  (declare (xargs :stobjs s :mode :program))
  (if (> v n)
      s
    (clear-asgn (1+ v) n (update-asgni v 0 s))))

(defun clear-arsn (v n s)
  ;; Set arsn[v..n] := -2.
  (declare (xargs :stobjs s :mode :program))
  (if (> v n)
      s
    (clear-arsn (1+ v) n (update-arsni v -2 s))))

(defun clear-watch (l len s)
  ;; Set watch[l..len-1] := nil.
  (declare (xargs :stobjs s :mode :program))
  (if (>= l len)
      s
    (clear-watch (1+ l) len (update-watchi l nil s))))

(defun clear-seen (v n s)
  ;; Set seen[v..n] := 0.
  (declare (xargs :stobjs s :mode :program))
  (if (> v n)
      s
    (clear-seen (1+ v) n (update-seeni v 0 s))))

;;;; ============================================================
;;;; 5.  VMTF Operations
;;;; ============================================================

; The VMTF list is doubly-linked.  0 is the null/end sentinel.
; vmtf-hd = highest-priority variable (or 0 if empty).
; vmtf-nxt[v] = next variable (lower priority), 0 if v is the tail.
; vmtf-prv[v] = previous variable (higher priority), 0 if v is the head.

(defun vmtf-link-init (v n s)
  ;; Build initial chain: 1 <-> 2 <-> ... <-> n  (head=1, tail=n)
  (declare (xargs :stobjs s :mode :program))
  (if (> v n)
      s
    (let* ((prv  (if (= v 1) 0 (1- v)))
           (nxt  (if (= v n) 0 (1+ v)))
           (s    (update-vmtf-nxti v nxt s))
           (s    (update-vmtf-prvi v prv s))
           (s    (update-vmtf-stmpi v 0 s)))
      (vmtf-link-init (1+ v) n s))))

(defun vmtf-detach (v s)
  ;; Remove variable v from its current position in the list.
  (declare (xargs :stobjs s :mode :program))
  (let* ((prv (vmtf-prvi v s))
         (nxt (vmtf-nxti v s))
         (s   (if (> prv 0)
                  (update-vmtf-nxti prv nxt s)
                s))
         (s   (if (> nxt 0)
                  (update-vmtf-prvi nxt prv s)
                s))
         (s   (if (= (vmtf-hd s) v)
                  (update-vmtf-hd nxt s)
                s)))
    s))

(defun vmtf-push-front (v s)
  ;; Insert v at the head of the VMTF list (highest priority).
  (declare (xargs :stobjs s :mode :program))
  (let* ((old-hd (vmtf-hd s))
         (s      (update-vmtf-nxti v old-hd s))
         (s      (update-vmtf-prvi v 0 s))
         (s      (if (> old-hd 0)
                     (update-vmtf-prvi old-hd v s)
                   s))
         (s      (update-vmtf-hd v s))
         ;; Update stamp
         (tick   (1+ (vmtf-clk s)))
         (s      (update-vmtf-clk tick s))
         (s      (update-vmtf-stmpi v tick s)))
    s))

(defun vmtf-move-to-front (v s)
  ;; Move variable v to the front of the VMTF list.
  (declare (xargs :stobjs s :mode :program))
  (if (= v (vmtf-hd s))
      s  ; already at front
    (let* ((s (vmtf-detach v s))
           (s (vmtf-push-front v s)))
      s)))

(defun vmtf-bump-list (lits s)
  ;; Move all variables in the literal list 'lits' to the front.
  ;; Called after conflict analysis with the learned clause literals.
  (declare (xargs :stobjs s :mode :program))
  (if (endp lits)
      s
    (vmtf-bump-list (cdr lits) (vmtf-move-to-front (lit-var (car lits)) s))))

(defun vmtf-next-unassigned (v s)
  ;; Walk VMTF list from v; return first unassigned variable, or 0.
  (declare (xargs :stobjs s :mode :program))
  (cond
    ((= v 0) 0)
    ((= (asgni v s) 0) v)          ; unassigned
    (t (vmtf-next-unassigned (vmtf-nxti v s) s))))

;;;; ============================================================
;;;; 6.  Trail and Assignment (enqueue)
;;;; ============================================================

(defun enqueue (lit reason s)
  ;; Assign literal 'lit' with given reason (clause-id or -1 for decision).
  ;; Does NOT check for prior assignment — caller must ensure lit is unassigned.
  (declare (xargs :stobjs s :mode :program))
  (let* ((v   (lit-var lit))
         (val (if (= (lit-sign lit) 0) 1 -1))
         (s   (update-asgni  v val s))
         (s   (update-alevi  v (dlev s) s))
         (s   (update-arsni  v reason s))
         (te  (trail-sz s))
         (s   (update-traili te lit s))
         (s   (update-trail-sz (1+ te) s)))
    s))

;;;; ============================================================
;;;; 7.  Watch List Helpers
;;;; ============================================================

(defun push-watch (lit cid blocker s)
  ;; Add a watch entry for 'lit': when lit becomes FALSE, check clause cid.
  (declare (xargs :stobjs s :mode :program))
  (update-watchi lit (cons (cons cid blocker) (watchi lit s)) s))

(defun install-watches (cid s)
  ;; Install 2WL for clause cid (must have length >= 2).
  ;; Watches: watch[lits[0]] and watch[lits[1]].
  (declare (xargs :stobjs s :mode :program))
  (let* ((l0 (cl-lit cid 0 s))
         (l1 (cl-lit cid 1 s))
         (s  (push-watch l0 cid l1 s))
         (s  (push-watch l1 cid l0 s)))
    s))

;;;; ============================================================
;;;; 8.  Solver Initialization
;;;; ============================================================

(defun count-lits (clauses acc)
  ;; Total number of literals across all clauses.
  (declare (xargs :mode :program))
  (if (endp clauses)
      acc
    (count-lits (cdr clauses) (+ acc (length (car clauses))))))

(defun add-clause-lits (lits-list base-idx cid s)
  ;; Write literals from lits-list into ldata starting at base-idx.
  ;; Returns (mv unsat s) where unsat=t if lits-list is empty (empty clause).
  (declare (xargs :stobjs s :mode :program))
  (if (endp lits-list)
      (mv nil s)
    (let* ((s (update-ldatai base-idx (car lits-list) s)))
      (add-clause-lits (cdr lits-list) (1+ base-idx) cid s))))

(defun load-clause (lits-list cid s)
  ;; Add clause with given literals to the database at position cid.
  ;; Returns (mv result s) where result is :unsat, :unit-enqueued, or :ok.
  (declare (xargs :stobjs s :mode :program))
  (let* ((len (length lits-list)))
    (cond
      ;; Empty clause -> immediate UNSAT
      ((= len 0)
       (mv :unsat s))
      ;; Unit clause at root level: enqueue directly
      ((= len 1)
       (let* ((l   (car lits-list))
              (top (ltop s))
              (s   (update-cl-starti cid top s))
              (s   (update-cl-leni   cid 1   s))
              (s   (update-cl-lbdi   cid 1   s))
              (s   (update-cl-acti   cid 0.0 s))
              (s   (update-cl-deli   cid 0   s))
              (s   (update-ldatai top l s))
              (s   (update-ltop (1+ top) s))
              (s   (update-ndb (1+ (ndb s)) s)))
         (if (lit-false-p l s)
             (mv :unsat s)
           (if (lit-undef-p l s)
               (mv :unit-enqueued (enqueue l -1 s))
             (mv :ok s)))))
      ;; General clause (length >= 2)
      (t
       (let* ((top (ltop s))
              (s   (update-cl-starti cid top s))
              (s   (update-cl-leni   cid len s))
              (s   (update-cl-lbdi   cid 0   s))
              (s   (update-cl-acti   cid 0.0 s))
              (s   (update-cl-deli   cid 0   s)))
         (mv-let (ignore s)
           (add-clause-lits lits-list top cid s)
           (declare (ignore ignore))
           (let* ((s (update-ltop (+ top len) s))
                  (s (update-ndb (1+ (ndb s)) s))
                  (s (install-watches cid s)))
             (mv :ok s))))))))

(defun load-clauses (clauses cid s)
  ;; Load list of clauses (each a list of literals) into the solver.
  ;; Returns (mv :unsat-or-ok s).
  (declare (xargs :stobjs s :mode :program))
  (if (endp clauses)
      (mv :ok s)
    (mv-let (res s)
      (load-clause (car clauses) cid s)
      (if (eq res :unsat)
          (mv :unsat s)
        (load-clauses (cdr clauses) (1+ cid) s)))))

(defun init-solver (n clauses s)
  ;; n       = number of variables
  ;; clauses = list of lists of (unsigned-byte 30) literals
  ;; Returns (mv :sat/:unsat/:ok s)
  ;;   :ok means initialized, ready to run CDCL
  (declare (xargs :stobjs s :mode :program))
  (let* ((nc-orig  (length clauses))
         (nl-total (count-lits clauses 0))
         ;; Reserve extra space for learned clauses
         (db-cap   (+ nc-orig 200000))
         (ld-cap   (+ nl-total 2000000))
         (var-cap  (+ n 1))
         (lit-cap  (* 2 (+ n 1)))

         ;; Set problem size
         (s (update-nv n s))
         (s (update-nc nc-orig s))

         ;; Resize clause database arrays
         (s (resize-ldata    ld-cap  s))
         (s (resize-cl-start db-cap  s))
         (s (resize-cl-len   db-cap  s))
         (s (resize-cl-lbd   db-cap  s))
         (s (resize-cl-act   db-cap  s))
         (s (resize-cl-del   db-cap  s))
         (s (update-ndb 0 s))
         (s (update-ltop 0 s))

         ;; Resize and clear variable arrays
         (s (resize-asgn var-cap s))
         (s (resize-alev var-cap s))
         (s (resize-arsn var-cap s))
         (s (clear-asgn 1 n s))
         (s (clear-arsn 1 n s))

         ;; Resize and clear trail
         (s (resize-trail (1+ n) s))
         (s (update-trail-sz 0 s))
         (s (resize-tlim (1+ n) s))
         (s (update-tlim-sz 0 s))
         (s (update-prop-q 0 s))
         (s (update-dlev 0 s))

         ;; Resize and clear watch lists
         (s (resize-watch lit-cap s))
         (s (clear-watch 0 lit-cap s))

         ;; Resize and init VMTF
         (s (resize-vmtf-nxt  var-cap s))
         (s (resize-vmtf-prv  var-cap s))
         (s (resize-vmtf-stmp var-cap s))
         (s (update-vmtf-hd 1 s))
         (s (update-vmtf-clk 0 s))
         (s (vmtf-link-init 1 n s))

         ;; Resize phase and seen
         (s (resize-phase var-cap s))
         (s (resize-seen  var-cap s))
         (s (clear-seen   1 n s))

         ;; Reset EMA and deletion state
         (s (update-ema-f 0.0 s))
         (s (update-ema-s 0.0 s))
         (s (update-csr 0 s))
         (s (update-del-lim (+ nc-orig 1000) s))
         (s (update-nlrn 0 s))
         (s (update-act-inc 1.0 s)))

    ;; Load all clauses
    (load-clauses clauses 0 s)))

;;;; ============================================================
;;;; 9.  Unit Propagation (BCP with 2WL)
;;;; ============================================================

; Returns (mv conflict-cid s) where conflict-cid = -1 means no conflict.

(defun find-new-watcher (cid start len s)
  ;; Search clause cid's literals from position 'start' for a non-false one.
  ;; Returns index (>= 0) or -1.
  (declare (xargs :stobjs s :mode :program))
  (if (>= start len)
      -1
    (if (not (lit-false-p (cl-lit cid start s) s))
        start
      (find-new-watcher cid (1+ start) len s))))

(defun process-watch-list (ws fp kept conflict s)
  ;; Process the watch list 'ws' for false literal fp.
  ;; fp  = the literal that just became FALSE (it was being watched by each clause in ws).
  ;; kept = accumulator (in reverse order) of watch entries to keep in watch[fp].
  ;; conflict = -1 or the conflicting clause id (stops propagation, drains rest).
  ;; Returns (mv kept conflict s).
  (declare (xargs :stobjs s :mode :program))
  (if (atom ws)
      (mv kept conflict s)
    (let* ((w    (car ws))
           (rest (cdr ws))
           (cid  (car w))
           (blkr (cdr w)))
      (cond
        ;; Deleted clause: discard entry silently
        ((= (cl-deli cid s) 1)
         (process-watch-list rest fp kept conflict s))

        ;; Already have a conflict: just drain remaining watches unchanged
        ((not (= conflict -1))
         (mv (revappend rest (cons w kept)) conflict s))

        ;; Fast path: blocker literal is TRUE -> clause satisfied
        ((lit-true-p blkr s)
         (process-watch-list rest fp (cons w kept) conflict s))

        ;; Need to examine the clause
        (t
         (let* ((len (cl-leni cid s)))
           ;; Ensure ldata[cl-start[cid] + 1] = fp  (make fp the second watcher)
           ;; so that ldata[cl-start[cid] + 0] is the "other" watcher.
           (when (= (cl-lit cid 0 s) fp)
             ;; swap positions 0 and 1
             ;; Note: this mutates ldata in the stobj; fine in program mode.
             (let ((tmp (cl-lit cid 0 s)))
               (declare (ignore tmp)))
             ; We must do this imperatively via set-cl-lit:
             (let* ((l0 (cl-lit cid 0 s))
                    (l1 (cl-lit cid 1 s))
                    (s  (set-cl-lit cid 0 l1 s))
                    (s  (set-cl-lit cid 1 l0 s)))
               (declare (ignore s)))
             ; The above doesn't thread s properly; use a helper:
             nil)
           (let* ((s    (if (= (cl-lit cid 0 s) fp)
                            (swap-cl-lits cid 0 1 s)
                          s))
                  (other (cl-lit cid 0 s)))  ; the non-fp watcher
             (cond
               ;; Other watcher is TRUE: clause satisfied
               ((lit-true-p other s)
                (process-watch-list rest fp
                                    (cons (cons cid other) kept)
                                    conflict s))
               ;; Search positions 2..len-1 for a non-false literal
               (t
                (let* ((k (find-new-watcher cid 2 len s)))
                  (if (>= k 0)
                      ;; Found: move ldata[cl-start+k] to position 1 (new watcher)
                      (let* ((new-w (cl-lit cid k s))
                             (s     (swap-cl-lits cid 1 k s))
                             ;; new watcher = new-w (now at position 1)
                             ;; Add watch entry: when new-w becomes false, check cid
                             (s     (push-watch new-w cid other s)))
                        ;; Do NOT keep entry in watch[fp] (moved to watch[new-w])
                        (process-watch-list rest fp kept conflict s))
                    ;; No new watcher: clause is unit or conflicting
                    (let* ((kept2 (cons w kept)))
                      (if (lit-undef-p other s)
                          ;; Unit: propagate 'other'
                          (let* ((s (enqueue other cid s)))
                            (process-watch-list rest fp kept2 -1 s))
                        ;; Conflict: 'other' is also false
                        (mv (revappend rest kept2) cid s)))))))))))))

(defun propagate-step (s)
  ;; Process one literal from the BCP queue.
  ;; Returns (mv conflict-cid s).  conflict-cid = -1 means no conflict yet.
  (declare (xargs :stobjs s :mode :program))
  (let* ((q    (traili (prop-q s) s))   ; dequeue literal q (TRUE)
         (s    (update-prop-q (1+ (prop-q s)) s))
         (fp   (nlit q))               ; fp = neg(q) = literal that just became FALSE
         (old  (watchi fp s))
         (s    (update-watchi fp nil s)))  ; temporarily clear; rebuild below
    (mv-let (new-kept conflict s)
      (process-watch-list old fp nil -1 s)
      ;; Prepend rebuilt list (reversed) to whatever was added during processing
      ;; (handles the edge case where new-w = neg(fp) = q was added to watch[fp])
      (let* ((s (update-watchi fp (revappend new-kept (watchi fp s)) s)))
        (mv conflict s)))))

(defun propagate (s)
  ;; Run BCP until fixpoint or conflict.
  ;; Returns (mv conflict-cid s).  conflict-cid = -1 means no conflict.
  (declare (xargs :stobjs s :mode :program))
  (if (= (prop-q s) (trail-sz s))
      (mv -1 s)  ; queue empty, no conflict
    (mv-let (conflict s)
      (propagate-step s)
      (if (not (= conflict -1))
          (mv conflict s)
        (propagate s)))))

;;;; ============================================================
;;;; 10.  Conflict Analysis  (1-UIP)
;;;; ============================================================

; Returns (mv learned-lits bt-level lbd s)
;   learned-lits: list of literals; [0] = asserting literal
;   bt-level    : backtrack level
;   lbd         : Literal Block Distance of learned clause

(defun process-reason-lits (lits k len cur-lev counter learned s)
  ;; Iterate over literals of a clause (lits = list), mark seen, collect non-current-level.
  ;; Returns (mv counter learned s).
  (declare (xargs :stobjs s :mode :program))
  (if (>= k len)
      (mv counter learned s)
    (let* ((l (car lits))
           (v (lit-var l))
           (lv (alevi v s)))
      (if (= (seeni v s) 1)
          ;; Already seen
          (process-reason-lits (cdr lits) (1+ k) len cur-lev counter learned s)
        (let* ((s (update-seeni v 1 s)))
          (if (= lv cur-lev)
              ;; At current level: increment counter (will be resolved)
              (process-reason-lits (cdr lits) (1+ k) len cur-lev (1+ counter) learned s)
            ;; Below current level: add neg(l) to learned clause
            (if (> lv 0)
                (process-reason-lits (cdr lits) (1+ k) len cur-lev counter
                                     (cons (nlit l) learned) s)
              ;; Level 0: skip (already unit-propagated permanently)
              (process-reason-lits (cdr lits) (1+ k) len cur-lev counter learned s))))))))

(defun clause-lits-as-list (cid s)
  ;; Return literals of clause cid as a list (for passing to process-reason-lits).
  (declare (xargs :stobjs s :mode :program))
  (let ((len (cl-leni cid s))
        (st  (cl-starti cid s)))
    (let loop ((k 0) (acc nil))
      (declare (xargs :mode :program))
      (if (= k len)
          (nreverse acc)
        (loop (1+ k) (cons (ldatai (+ st k) s) acc))))))

; Because ACL2 doesn't support named let-loops, use a recursive helper:
(defun clause-lits-loop (cid k len st s acc)
  (declare (xargs :stobjs s :mode :program))
  (if (= k len)
      (reverse acc)
    (clause-lits-loop cid (1+ k) len st s
                      (cons (ldatai (+ st k) s) acc))))

(defun clause-lits-as-list (cid s)
  (declare (xargs :stobjs s :mode :program))
  (clause-lits-loop cid 0 (cl-leni cid s) (cl-starti cid s) s nil))

(defun find-uip-step (trail-idx cur-lev counter learned s)
  ;; Walk trail backwards from trail-idx to find the 1-UIP.
  ;; Returns (mv uip-lit learned s).
  (declare (xargs :stobjs s :mode :program))
  (if (< trail-idx 0)
      ;; Should not happen in a correct solver
      (mv 0 learned s)
    (let* ((l (traili trail-idx s))
           (v (lit-var l)))
      (if (= (seeni v s) 0)
          ;; Not seen: skip
          (find-uip-step (1- trail-idx) cur-lev counter learned s)
        ;; Seen: this is a candidate
        (let* ((s (update-seeni v 0 s)))   ; clear seen
          (if (= counter 1)
              ;; counter=1: l is the 1-UIP
              (mv l learned s)
            ;; Resolve: process reason of v
            (let* ((r (arsni v s)))
              (if (= r -1)
                  ;; Decision literal (no reason clause): resolve done
                  (mv l learned s)
                ;; Resolve against reason clause of v
                (let* ((reason-lits (clause-lits-as-list r s)))
                  (mv-let (new-counter new-learned s)
                    (process-reason-lits reason-lits 0 (length reason-lits)
                                         cur-lev (1- counter) learned s)
                    (find-uip-step (1- trail-idx) cur-lev new-counter new-learned s)))))))))))

(defun distinct-levels (lits s acc)
  ;; Count distinct non-zero decision levels in lits.
  ;; acc = list of already-seen levels.
  (declare (xargs :stobjs s :mode :program))
  (if (endp lits)
      (length acc)
    (let* ((lv (alevi (lit-var (car lits)) s)))
      (if (or (= lv 0) (member lv acc))
          (distinct-levels (cdr lits) s acc)
        (distinct-levels (cdr lits) s (cons lv acc))))))

(defun bt-level-of (lits s best-lv best-idx cur-idx)
  ;; Find the literal in lits (skipping index 0 = asserting) with highest level.
  ;; Returns that level (for the second watcher position).
  (declare (xargs :stobjs s :mode :program))
  (if (endp lits)
      (mv best-lv best-idx)
    (let* ((lv (alevi (lit-var (car lits)) s)))
      (if (> lv best-lv)
          (bt-level-of (cdr lits) s lv cur-idx (1+ cur-idx))
        (bt-level-of (cdr lits) s best-lv best-idx (1+ cur-idx))))))

(defun list-swap (lst i j)
  ;; Swap elements at positions i and j in list lst (0-indexed).
  (declare (xargs :mode :program))
  (let* ((a   (nth i lst))
         (b   (nth j lst))
         (lst (update-nth i b lst))
         (lst (update-nth j a lst)))
    lst))

(defun analyze (conflict-cid s)
  ;; Analyze conflict at clause conflict-cid.
  ;; Returns (mv learned-lits bt-level lbd s).
  (declare (xargs :stobjs s :mode :program))
  (let* ((cur-lev (dlev s))
         ;; Seed: process conflict clause literals
         (conf-lits (clause-lits-as-list conflict-cid s)))
    (mv-let (counter learned s)
      (process-reason-lits conf-lits 0 (length conf-lits) cur-lev 0 nil s)
      ;; Walk trail backwards to find 1-UIP
      (mv-let (uip learned s)
        (find-uip-step (1- (trail-sz s)) cur-lev counter learned s)
        ;; Build learned clause: asserting literal is neg(uip), rest is learned
        (let* ((asserting  (nlit uip))
               (all-lits   (cons asserting learned))
               ;; Compute backtrack level = max level in all-lits[1..]
               ;; and reorder so that literal at bt-level is at position 1
               (lbd        (distinct-levels all-lits s nil)))
          (if (endp learned)
              ;; Unit learned clause (empty implication graph)
              (mv all-lits 0 lbd s)
            (mv-let (bt-lv bt-idx)
              (bt-level-of learned s 0 0 1)  ; search learned (indices 1..)
              ;; Swap the bt-level literal to position 1 in all-lits
              (let* ((all-lits (list-swap all-lits 1 (1+ bt-idx))))  ; +1 because all-lits has asserting at 0
                (mv all-lits bt-lv lbd s)))))))))

(defun clear-seen-for-lits (lits s)
  ;; Clear seen[v] for each variable in lits.
  (declare (xargs :stobjs s :mode :program))
  (if (endp lits)
      s
    (clear-seen-for-lits (cdr lits)
                         (update-seeni (lit-var (car lits)) 0 s))))

;;;; ============================================================
;;;; 11.  Backtracking  (with Phase Saving)
;;;; ============================================================

(defun unassign-trail-from (idx target-sz s)
  ;; Undo trail assignments from position trail-sz-1 down to target-sz.
  ;; Also saves phase and clears assignment arrays.
  (declare (xargs :stobjs s :mode :program))
  (if (<= idx (1- target-sz))
      s
    (let* ((l  (traili idx s))
           (v  (lit-var l))
           ;; Save phase: positive lit -> phase=1, negative -> phase=0
           (ph (if (= (lit-sign l) 0) 1 0))
           (s  (update-phasei  v ph s))
           ;; Unassign
           (s  (update-asgni   v 0  s))
           (s  (update-arsni   v -2 s))
           ;; Move to front in VMTF (re-prioritize for future decisions)
           (s  (vmtf-move-to-front v s)))
      (unassign-trail-from (1- idx) target-sz s))))

(defun backtrack (target-lev s)
  ;; Undo all assignments above target-lev.
  ;; Backtrack to level target-lev: keep trail[0..tlim[target-lev]-1].
  (declare (xargs :stobjs s :mode :program))
  (let* (;; Target trail size: if target-lev = 0, keep root propagations.
         ;; tlim[d] = trail size at END of level d.
         ;; After push of level d+1 decision, we record tlim[d] = trail-sz.
         ;; Backtracking to level L: new trail-sz = tlim[L].
         ;; If L=0 and tlim-sz=0 (never made decisions), trail-sz stays 0.
         (tgt-ts  (if (and (> target-lev 0) (<= target-lev (tlim-sz s)))
                      (tlimi (1- target-lev) s)  ; tlim is 0-indexed: tlim[d-1] for level d
                    (if (= target-lev 0)
                        (if (> (tlim-sz s) 0)
                            (tlimi 0 s)   ; this is trail size after root level (before level-1 decision)
                          0)
                      0)))
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
         (tgt-ts2 (if (< target-lev (tlim-sz s))
                      (tlimi target-lev s)
                    0))
         (cur-ts  (trail-sz s))
         (s       (unassign-trail-from (1- cur-ts) tgt-ts2 s))
         (s       (update-trail-sz   tgt-ts2 s))
         (s       (update-prop-q     tgt-ts2 s))
         (s       (update-dlev       target-lev s))
         (s       (update-tlim-sz    target-lev s)))
    s))

;;;; ============================================================
;;;; 12.  Adding a Learned Clause
;;;; ============================================================

(defun add-learned-clause (lits-list lbd s)
  ;; lits-list: list of literals.  lits[0]=asserting, lits[1]=bt-level literal.
  ;; Returns (mv cid s).
  (declare (xargs :stobjs s :mode :program))
  (let* ((len  (length lits-list))
         (cid  (ndb s))
         (top  (ltop s))
         ;; Write literals into ldata
         (s    (add-clause-lits-to-db lits-list top s))
         ;; Set clause metadata
         (s    (update-cl-starti cid top s))
         (s    (update-cl-leni   cid len s))
         (s    (update-cl-lbdi   cid lbd s))
         (s    (update-cl-acti   cid (act-inc s) s))
         (s    (update-cl-deli   cid 0 s))
         (s    (update-ltop  (+ top len) s))
         (s    (update-ndb   (1+ cid) s))
         (s    (update-nlrn  (1+ (nlrn s)) s))
         ;; Install watches (lits[0] and lits[1])
         (s    (if (>= len 2)
                   (install-watches cid s)
                 s)))
    (mv cid s)))

(defun add-clause-lits-to-db (lits-list base s)
  ;; Write literals from lits-list starting at ldata[base].
  (declare (xargs :stobjs s :mode :program))
  (if (endp lits-list)
      s
    (add-clause-lits-to-db (cdr lits-list) (1+ base)
                           (update-ldatai base (car lits-list) s))))

;;;; ============================================================
;;;; 13.  Decision
;;;; ============================================================

(defun decide (s)
  ;; Pick next decision literal using VMTF + phase saving.
  ;; Returns (mv :sat s) if all variables assigned, else (mv :continue s).
  (declare (xargs :stobjs s :mode :program))
  (let* ((v (vmtf-next-unassigned (vmtf-hd s) s)))
    (if (= v 0)
        (mv :sat s)   ; all variables assigned
      (let* (;; Phase saving: use saved phase
             (ph  (phasei v s))
             (lit (if (= ph 1) (pos-lit v) (neg-lit v)))
             ;; New decision level
             (lev (1+ (dlev s)))
             ;; Record trail limit for this new level
             (tlsz (tlim-sz s))
             (s   (update-tlimi tlsz (trail-sz s) s))
             (s   (update-tlim-sz (1+ tlsz) s))
             (s   (update-dlev lev s))
             ;; Enqueue decision
             (s   (enqueue lit -1 s)))
        (mv :continue s)))))

;;;; ============================================================
;;;; 14.  EMA-Based Restarts
;;;; ============================================================

(defparameter *ema-fast-alpha* 3.0e-2)   ; fast window ~33 conflicts
(defparameter *ema-slow-alpha* 1.0e-5)   ; slow window ~100k conflicts
(defparameter *restart-margin* 1.25)
(defparameter *restart-min-conflicts* 50)

(defun update-ema (lbd s)
  ;; Update fast and slow EMA with new LBD value.
  (declare (xargs :stobjs s :mode :program))
  (let* ((af  *ema-fast-alpha*)
         (as  *ema-slow-alpha*)
         (f   (+ (* (- 1.0 af) (ema-f s)) (* af (float lbd))))
         (sl  (+ (* (- 1.0 as) (ema-s s)) (* as (float lbd))))
         (s   (update-ema-f f s))
         (s   (update-ema-s sl s))
         (s   (update-csr (1+ (csr s)) s)))
    s))

(defun restart-p (s)
  ;; Return t if a restart should be triggered.
  (declare (xargs :stobjs s :mode :program))
  (and (> (csr s) *restart-min-conflicts*)
       (> (ema-f s) (* *restart-margin* (ema-s s)))))

(defun do-restart (s)
  ;; Execute a restart: backtrack to level 0, reset conflict counter.
  (declare (xargs :stobjs s :mode :program))
  (let* ((s (backtrack 0 s))
         (s (update-csr 0 s)))
    s))

;;;; ============================================================
;;;; 15.  Clause Activity and Deletion
;;;; ============================================================

(defparameter *act-decay* 0.999)
(defparameter *act-rescale* 1.0e-20)
(defparameter *act-max*    1.0e20)
(defparameter *lbd-keep*   2)     ; keep clauses with LBD <= this (glue clauses)

(defun bump-clause-act (cid s)
  ;; Bump activity of clause cid by act-inc.
  (declare (xargs :stobjs s :mode :program))
  (let* ((new-a (+ (cl-acti cid s) (act-inc s)))
         (s     (update-cl-acti cid new-a s)))
    ;; Rescale all activities if overflow
    (if (> new-a *act-max*)
        (rescale-all-acts (nc s) (ndb s) s)
      s)))

(defun rescale-all-acts (cid end s)
  ;; Multiply all clause activities by act-rescale, and scale act-inc.
  (declare (xargs :stobjs s :mode :program))
  (if (>= cid end)
      (update-act-inc (* (act-inc s) *act-rescale*) s)
    (let* ((s (update-cl-acti cid (* (cl-acti cid s) *act-rescale*) s)))
      (rescale-all-acts (1+ cid) end s))))

(defun clause-locked-p (cid s)
  ;; A clause is locked if it is the reason for some currently assigned variable.
  ;; Check: lits[0] is true AND arsn[lit-var(lits[0])] = cid.
  (declare (xargs :stobjs s :mode :program))
  (let* ((l0  (cl-lit cid 0 s))
         (v0  (lit-var l0)))
    (and (lit-true-p l0 s)
         (= (arsni v0 s) cid))))

(defun collect-deletable (cid end nc acc s)
  ;; Collect learned clause ids that are candidates for deletion.
  ;; Returns list of (cid . score) where score = (lbd . neg-act).
  (declare (xargs :stobjs s :mode :program))
  (if (>= cid end)
      acc
    (let* ((del?  (= (cl-deli cid s) 1))
           (orig? (< cid nc))
           (lbd   (cl-lbdi cid s))
           (locked? (clause-locked-p cid s)))
      (if (or del? orig? locked? (<= lbd *lbd-keep*))
          (collect-deletable (1+ cid) end nc acc s)
        (collect-deletable (1+ cid) end nc
                           (cons (cons cid (cons lbd (- (cl-acti cid s)))) acc)
                           s)))))

(defun sort-by-score (alist)
  ;; Sort by (lbd, neg-act) ascending = worst clauses first.
  ;; Using a simple insertion sort (good enough for moderate lists).
  (declare (xargs :mode :program))
  (if (endp alist)
      nil
    (insert-by-score (car alist) (sort-by-score (cdr alist)))))

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

(defun mark-deleted (candidates target s)
  ;; Mark the first 'target' candidates as deleted.
  (declare (xargs :stobjs s :mode :program))
  (if (or (endp candidates) (<= target 0))
      s
    (let* ((cid (caar candidates))
           (s   (update-cl-deli cid 1 s))
           (s   (update-nlrn (max 0 (1- (nlrn s))) s)))
      (mark-deleted (cdr candidates) (1- target) s))))

(defun maybe-delete-clauses (s)
  ;; Delete approximately half of low-quality learned clauses if threshold exceeded.
  (declare (xargs :stobjs s :mode :program))
  (if (< (nlrn s) (del-lim s))
      s
    (let* ((nc-orig    (nc s))
           (candidates (collect-deletable nc-orig (ndb s) nc-orig nil s))
           (sorted     (sort-by-score candidates))
           (target     (floor (length sorted) 2))
           (s          (mark-deleted sorted target s))
           ;; Double deletion threshold
           (s          (update-del-lim (* 2 (del-lim s)) s)))
      s)))

;;;; ============================================================
;;;; 16.  Main CDCL Loop
;;;; ============================================================

; Result codes:
;   :sat   - formula is satisfiable (full assignment on trail)
;   :unsat - formula is unsatisfiable

(defun cdcl-inner (s)
  ;; Inner loop: BCP + conflict analysis until no conflict.
  ;; Returns (mv :continue/:unsat s).
  (declare (xargs :stobjs s :mode :program))
  (mv-let (conflict s)
    (propagate s)
    (if (= conflict -1)
        ;; No conflict: BCP quiescent
        (mv :continue s)
      ;; Conflict found
      (if (= (dlev s) 0)
          ;; Conflict at root level -> UNSAT
          (mv :unsat s)
        ;; Analyze conflict
        (mv-let (learned bt-lev lbd s)
          (analyze conflict s)
          ;; Clear seen bits for all learned literals
          (let* ((s (clear-seen-for-lits learned s)))
            ;; Update EMA
            (let* ((s (update-ema lbd s)))
              ;; Backtrack to asserting level
              (let* ((s (backtrack bt-lev s)))
                ;; Add learned clause
                (mv-let (cid s)
                  (add-learned-clause learned lbd s)
                  ;; Bump learned clause activity
                  (let* ((s (bump-clause-act cid s))
                         ;; Bump VMTF for all variables in learned clause
                         (s (vmtf-bump-list learned s))
                         ;; Enqueue asserting literal (learned[0])
                         (s (enqueue (car learned) cid s))
                         ;; Restart check
                         (s (if (restart-p s) (do-restart s) s))
                         ;; Clause deletion check
                         (s (maybe-delete-clauses s)))
                    ;; Continue inner loop
                    (cdcl-inner s)))))))))))

(defun cdcl-outer (s)
  ;; Outer loop: make decisions, run inner loop.
  ;; Returns (mv :sat/:unsat s).
  (declare (xargs :stobjs s :mode :program))
  (mv-let (dec-res s)
    (decide s)
    (if (eq dec-res :sat)
        (mv :sat s)   ; all variables assigned, no conflict
      ;; Decision made; run BCP + conflict resolution
      (mv-let (inner-res s)
        (cdcl-inner s)
        (if (eq inner-res :unsat)
            (mv :unsat s)
          (cdcl-outer s))))))

(defun cdcl-solve (n clauses s)
  ;; Top-level solver entry point.
  ;; n       = number of variables (positive integer)
  ;; clauses = list of lists of literals (pos-lit or neg-lit)
  ;; Returns (mv result s) where result is :sat, :unsat.
  (declare (xargs :stobjs s :mode :program))
  (mv-let (init-res s)
    (init-solver n clauses s)
    (if (eq init-res :unsat)
        (mv :unsat s)
      ;; Root-level BCP (unit propagation of root-level facts)
      (mv-let (conflict s)
        (propagate s)
        (if (not (= conflict -1))
            (mv :unsat s)
          (cdcl-outer s))))))

;;;; ============================================================
;;;; 17.  Model Extraction
;;;; ============================================================

(defun extract-model (v n s acc)
  ;; Collect the satisfying assignment as an alist ((var . bool) ...).
  (declare (xargs :stobjs s :mode :program))
  (if (> v n)
      acc
    (let* ((av (asgni v s))
           (entry (cons v (= av 1))))
      (extract-model (1+ v) n s (cons entry acc)))))

(defun get-model (s)
  ;; Return the satisfying assignment as an alist (1-indexed variables).
  (declare (xargs :stobjs s :mode :program))
  (extract-model 1 (nv s) s nil))
