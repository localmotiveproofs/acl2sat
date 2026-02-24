; dimacs.lisp  —  DIMACS CNF parser and file-level solver interface
;
; DIMACS CNF format:
;   c comment lines (ignored)
;   p cnf <num-vars> <num-clauses>
;   <lit1> <lit2> ... 0    (one clause per line, terminated by 0)
;   Positive integer i  -> positive literal of variable i
;   Negative integer -i -> negative literal of variable i
;
; We convert DIMACS integer literals to our encoding:
;   dimacs  i (> 0) -> pos-lit(i)  = 2*i
;   dimacs -i (< 0) -> neg-lit(i)  = 2*i + 1

(in-package "ACL2")

;;;; ============================================================
;;;; 1.  Integer  <->  Literal conversion
;;;; ============================================================

(defun dimacs->lit (i)
  ;; Convert a DIMACS integer literal (nonzero) to our internal encoding.
  (declare (xargs :mode :program))
  (if (> i 0)
      (* 2 i)           ; pos-lit(i)
    (+ (* 2 (- i)) 1))) ; neg-lit(-i)

(defun lit->dimacs (l)
  ;; Convert internal literal back to DIMACS signed integer.
  (declare (xargs :mode :program))
  (let ((v (ash l -1)))
    (if (= (logand l 1) 0) v (- v))))

;;;; ============================================================
;;;; 2.  String tokenizer
;;;; ============================================================

(defun skip-to-newline (chars)
  ;; Skip characters until (and including) the next newline.
  (declare (xargs :mode :program))
  (cond
    ((endp chars) nil)
    ((eql (car chars) #\Newline) (cdr chars))
    (t (skip-to-newline (cdr chars)))))

(defun skip-whitespace (chars)
  ;; Skip whitespace characters (space, tab, newline, CR).
  (declare (xargs :mode :program))
  (cond
    ((endp chars) nil)
    ((member (car chars) '(#\Space #\Tab #\Newline #\Return))
     (skip-whitespace (cdr chars)))
    (t chars)))

(defun read-token (chars acc)
  ;; Read a maximal non-whitespace sequence.
  ;; Returns (mv token rest-chars).
  (declare (xargs :mode :program))
  (cond
    ((endp chars) (mv (coerce (reverse acc) 'string) nil))
    ((member (car chars) '(#\Space #\Tab #\Newline #\Return))
     (mv (coerce (reverse acc) 'string) chars))
    (t (read-token (cdr chars) (cons (car chars) acc)))))

(defun parse-int-string (str)
  ;; Parse a decimal integer string (possibly with leading '-').
  ;; Returns the integer, or nil on failure.
  (declare (xargs :mode :program))
  (let* ((chars (coerce str 'list)))
    (if (endp chars)
        nil
      (if (eql (car chars) #\-)
          (let ((n (parse-nat-string (coerce (cdr chars) 'string))))
            (if n (- n) nil))
        (parse-nat-string str)))))

(defun parse-nat-chars (chars acc)
  (declare (xargs :mode :program))
  (cond
    ((endp chars) acc)
    ((and (char>= (car chars) #\0) (char<= (car chars) #\9))
     (parse-nat-chars (cdr chars)
                      (+ (* acc 10)
                         (- (char-code (car chars)) (char-code #\0)))))
    (t nil)))

(defun parse-nat-string (str)
  (declare (xargs :mode :program))
  (let ((chars (coerce str 'list)))
    (if (endp chars)
        nil
      (parse-nat-chars chars 0))))

;;;; ============================================================
;;;; 3.  DIMACS token-stream parser
;;;; ============================================================

(defun parse-clause-tokens (chars cur-clause acc-clauses)
  ;; Parse integer tokens until end of input or 'p'/'c' header.
  ;; Integers != 0 are accumulated into cur-clause.
  ;; 0 terminates a clause.
  ;; Returns (mv num-vars num-clauses clause-list rest-chars).
  ;; This version is called AFTER the header is parsed.
  (declare (xargs :mode :program))
  (let* ((chars (skip-whitespace chars)))
    (if (endp chars)
        (mv (reverse acc-clauses))
      (if (eql (car chars) #\c)
          ;; Comment line: skip
          (parse-clause-tokens (skip-to-newline chars) cur-clause acc-clauses)
        (mv-let (tok rest)
          (read-token chars nil)
          (let ((n (parse-int-string tok)))
            (cond
              ((null n)
               ;; Non-integer token: skip
               (parse-clause-tokens rest cur-clause acc-clauses))
              ((= n 0)
               ;; End of clause
               (parse-clause-tokens rest nil
                                    (cons (reverse cur-clause) acc-clauses)))
              (t
               ;; Literal: convert and add to current clause
               (parse-clause-tokens rest
                                    (cons (dimacs->lit n) cur-clause)
                                    acc-clauses)))))))))

(defun parse-header (chars)
  ;; Scan for the 'p cnf N M' line and return (mv N M rest-chars).
  ;; Skip comment lines.
  (declare (xargs :mode :program))
  (let* ((chars (skip-whitespace chars)))
    (cond
      ((endp chars) (mv 0 0 nil))
      ((eql (car chars) #\c)
       ;; Comment: skip entire line
       (parse-header (skip-to-newline chars)))
      ((eql (car chars) #\p)
       ;; Problem line: "p cnf N M"
       ;; Skip 'p'
       (let* ((chars (cdr chars))
              (chars (skip-whitespace chars)))
         ;; Skip 'cnf'
         (mv-let (tok1 chars)
           (read-token chars nil)
           (declare (ignore tok1))
           (let* ((chars (skip-whitespace chars)))
             ;; Read N
             (mv-let (tok-n chars)
               (read-token chars nil)
               (let* ((chars (skip-whitespace chars)))
                 ;; Read M
                 (mv-let (tok-m chars)
                   (read-token chars nil)
                   (let ((nv (parse-nat-string tok-n))
                         (nc (parse-nat-string tok-m)))
                     (mv (or nv 0) (or nc 0) chars)))))))))
      (t
       ;; Unexpected: skip this character
       (parse-header (cdr chars))))))

(defun parse-dimacs-string (str)
  ;; Parse a complete DIMACS CNF string.
  ;; Returns (mv num-vars clauses) where clauses is a list of literal lists.
  (declare (xargs :mode :program))
  (let* ((chars (coerce str 'list)))
    (mv-let (nv _nc rest)
      (parse-header chars)
      (declare (ignore _nc))
      (let* ((clauses (parse-clause-tokens rest nil nil)))
        (mv nv clauses)))))

;;;; ============================================================
;;;; 4.  File I/O
;;;; ============================================================

(defun read-file-chars (filename state)
  ;; Read the entire file as a string, then convert to chars.
  ;; Returns (mv chars state).
  (declare (xargs :mode :program :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :character state)
    (if (null channel)
        (mv nil state)
      (mv-let (contents state)
        (read-file-into-string2 filename 0 nil state)
        (let* ((state (close-input-channel channel state)))
          (mv contents state))))))

(defun read-dimacs-file (filename state)
  ;; Read and parse a DIMACS CNF file.
  ;; Returns (mv num-vars clauses state).
  (declare (xargs :mode :program :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :character state)
    (if (null channel)
        (progn$
          (cw "Error: could not open file ~s0~%" filename)
          (mv 0 nil state))
      (mv-let (str state)
        (read-file-into-string2 filename 0 nil state)
        (let* ((state (close-input-channel channel state)))
          (if (null str)
              (mv 0 nil state)
            (mv-let (nv clauses)
              (parse-dimacs-string str)
              (mv nv clauses state))))))))

;;;; ============================================================
;;;; 5.  Result printing
;;;; ============================================================

(defun print-model-alist (model)
  ;; Print the model (alist of (var . bool)) in DIMACS format.
  (declare (xargs :mode :program))
  (if (endp model)
      (cw "~%")
    (let* ((entry (car model))
           (var   (car entry))
           (pos   (cdr entry)))
      (cw "~s0~s1 " (if pos "" "-") var)
      (print-model-alist (cdr model)))))

(defun print-result (result solver)
  (declare (xargs :stobjs solver :mode :program))
  (cond
    ((eq result :sat)
     (cw "s SATISFIABLE~%v ")
     (print-model-alist (get-model solver))
     (cw "0~%"))
    ((eq result :unsat)
     (cw "s UNSATISFIABLE~%"))
    (t
     (cw "s UNKNOWN~%"))))

;;;; ============================================================
;;;; 6.  Top-level: solve a DIMACS file
;;;; ============================================================

(defun solve-dimacs (filename state solver)
  ;; Read a DIMACS file, solve it, print result.
  ;; Returns (mv result state solver).
  (declare (xargs :mode :program :stobjs (state solver)))
  (mv-let (nv clauses state)
    (read-dimacs-file filename state)
    (if (and (= nv 0) (null clauses))
        (mv :error state solver)
      (mv-let (result solver)
        (cdcl-solve nv clauses solver)
        (let* ((dummy (print-result result solver)))
          (declare (ignore dummy))
          (mv result state solver))))))
