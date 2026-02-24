(in-package "ACL2")

;; Unit test helpers
(defun run-solver (n clauses)
  ;; Helper to invoke cdcl-solve on a clause list and return the result code.
  (declare (xargs :mode :program))
  (with-local-stobj solver
    (mv-let (result solver)
      (cdcl-solve n clauses solver)
      (declare (ignore solver))
      result)))

(defun test-lit-roundtrip-pos ()
  (declare (xargs :mode :program))
  (let* ((literal (dimacs->lit 3)))
    (= (lit->dimacs literal) 3)))

(defun test-lit-roundtrip-neg ()
  (declare (xargs :mode :program))
  (let* ((literal (dimacs->lit -7)))
    (= (lit->dimacs literal) -7)))

(defun test-parse-int-basics ()
  (declare (xargs :mode :program))
  (and (= (parse-int-string "0") 0)
       (= (parse-int-string "37") 37)
       (= (parse-int-string "-12") -12)
       (null (parse-int-string ""))))

(defun test-solver-trivial-sat ()
  (declare (xargs :mode :program))
  (let* ((clauses (list (list (pos-lit 1)))))
    (equal (run-solver 1 clauses) :sat)))

(defun test-solver-trivial-unsat ()
  (declare (xargs :mode :program))
  (let* ((clauses (list (list (pos-lit 1))
                        (list (neg-lit 1)))))
    (equal (run-solver 1 clauses) :unsat)))

(defun test-solver-from-dimacs ()
  (declare (xargs :mode :program))
  (mv-let (nv clauses)
    (parse-dimacs-string "p cnf 3 3\n1 2 0\n-1 3 0\n-3 0\n")
    (equal (run-solver nv clauses) :sat)))

(defun report-test (name passed rest)
  (declare (xargs :mode :program))
  (if passed
      (prog2$ (cw "PASS: ~x0~%" name)
              rest)
    (prog2$ (cw "FAIL: ~x0~%" name)
            nil)))

(defun run-all-tests ()
  (declare (xargs :mode :program))
  (report-test 'test-lit-roundtrip-pos (test-lit-roundtrip-pos)
    (report-test 'test-lit-roundtrip-neg (test-lit-roundtrip-neg)
      (report-test 'test-parse-int-basics (test-parse-int-basics)
        (report-test 'test-solver-trivial-sat (test-solver-trivial-sat)
          (report-test 'test-solver-trivial-unsat (test-solver-trivial-unsat)
            (report-test 'test-solver-from-dimacs (test-solver-from-dimacs)
              (prog2$ (cw "All tests passed.~%") t))))))))
