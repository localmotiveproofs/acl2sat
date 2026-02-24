; main.lisp  —  Entry point: load all files and expose top-level interface.
;
; Usage from ACL2:
;   (ld "main.lisp")
;   (solve-dimacs "path/to/problem.cnf" state solver)
;
; Or from the shell (via Makefile):
;   echo '(ld "main.lisp") (solve-dimacs "problem.cnf" state solver) (acl2::quit)' | acl2

(in-package "ACL2")

;; Load solver core then DIMACS utilities
(ld "solver.lisp" :ld-error-action :error)
(ld "dimacs.lisp" :ld-error-action :error)

;; Convenience wrapper for interactive use
(defmacro solve (filename)
  `(mv-let (result state solver)
     (solve-dimacs ,filename state solver)
     (declare (ignore result state solver))
     (value :invisible)))
