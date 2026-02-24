ACL2SAT(7)                                                            ACL2SAT(7)

NAME
    acl2sat - CDCL SAT solver and DIMACS frontend implemented in ACL2

SYNOPSIS
    make test-sat
    make test-unsat
    make bench FILE=path/to/problem.cnf
    make check
    make test
    echo '(ld "main.lisp") (solve-dimacs "foo.cnf" state solver) (acl2::quit)' | acl2

DESCRIPTION
    This repository contains a program-mode CDCL SAT solver written in ACL2 Lisp.
    solver.lisp defines the single-stobj solver, literals, watched-literal
    propagation, conflict analysis, clause learning, restarts, and clause
    deletion.  main.lisp loads the solver and exposes a convenience macro
    (solve <filename>) for use inside the ACL2 REPL.  dimacs.lisp implements the
    DIMACS parser, small string utilities, file I/O, printing DIMACS models, and
    the solve-dimacs entry point.  tests.lisp contains program-mode unit tests
    that exercise literal conversion helpers, integer parsing, and several
    end-to-end SAT/UNSAT runs through cdcl-solve.  There are no verified theorems
    in this project; all functionality is executed in :program mode only.

FILES
    solver.lisp
        defstobj solver with clause database arrays, decision heuristics,
        restarts, and clause garbage collection.  Exported program functions:
        cdcl-solve, get-model, and many internal helpers that operate on the
        solver stobj.

    dimacs.lisp
        Plain string tokenizer, DIMACS integer conversion, DIMACS CNF parser,
        file I/O helpers, and solve-dimacs that runs cdcl-solve then prints the
        DIMACS-format result.

    main.lisp
        Loads solver.lisp and dimacs.lisp, then defines (solve <filename>) as a
        small wrapper for interactive ACL2 sessions.

    tests.lisp
        Program-mode test harness; run via (run-all-tests) or `make test`.  Tests
        call literal conversion helpers, parse small DIMACS snippets, and invoke
        cdcl-solve on tiny SAT/UNSAT problems.

    Makefile
        Shell targets for running tiny SAT/UNSAT examples, benching arbitrary
        DIMACS files, load-checking the ACL2 code, and executing the tests.

COMMANDS
    make test-sat
        Builds sample DIMACS files under tests/ and runs solve-dimacs to show a
        SAT assignment.

    make test-unsat
        Same as above, but for a tiny UNSAT instance reporting only the “s line”.

    make bench FILE=path/to/problem.cnf
        Loads solver.lisp and dimacs.lisp, then solves the specified DIMACS CNF.

    make check
        Loads solver.lisp and dimacs.lisp in ACL2 to confirm they translate; no
        tests are executed.

    make test
        Loads solver.lisp, dimacs.lisp, and tests.lisp, then runs all program-mode
        unit tests.  (Verified to pass before this README was written.)

USAGE
    From an ACL2 shell:
        (ld "main.lisp")
        (solve-dimacs "tests/sat_small.cnf" state solver)

    From the command line:
        echo '(ld "main.lisp") (solve-dimacs "foo.cnf" state solver) (acl2::quit)' | acl2

    The solver exposes cdcl-solve for programmatic use: it takes a variable count
    and list of clauses (each list of encoded literals) and returns :sat or
    :unsat plus the mutated solver stobj.  get-model extracts an alist of Boolean
    assignments when :sat is returned.
