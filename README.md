# ACL2SAT

## OVERVIEW

ACL2SAT is a conflict-driven clause learning (CDCL) SAT solver written entirely
in ACL2 program mode.  The solver operates on a single-threaded object `solver`
that stores all clause, assignment, and heuristic state.  DIMACS parsing plus
file I/O is provided for end-to-end command-line runs, and a small test harness
executes unit and integration checks through program-mode evaluations.

## FILES

### `solver.lisp`

* `defstobj solver` — fields include:
  * Clause arrays `ldata`, `cl-start`, `cl-len`, `cl-lbd`, `cl-act`, `cl-del`,
    as well as counters `ndb` and `ltop`.
  * Assignment/trail structures `asgn`, `alev`, `arsn`, `trail`, `tlim`,
    `prop-q`, `dlev`.
  * Watch arrays `watch` for two-watched-literal propagation.
  * VMTF (Variable-Move-To-Front) linked lists and phase saving vector.
  * Restart/EMA state (`ema-f`, `ema-s`, `csr`) and clause deletion counters
    (`del-lim`, `nlrn`, `act-inc`).
  * Temporary arrays (`seen`) for conflict analysis.
* Literal helpers (`lit-val`, `lit-true-p`, etc.) encode literals as unsigned
  integers (`pos-lit(v)=2v`, `neg-lit(v)=2v+1`).
* Unit propagation:
  * Two-watched-literal scheme with blocking literals (`push-watch`,
    `process-watch-list`, `propagate`).
* Conflict analysis:
  * 1-UIP learning via `process-reason-lits`, `find-uip-step`, `analyze`.
  * Learned clauses are added by `add-learned-clause`, with watchers installed on
    the asserting literal and maximal-level literal.
* Decision heuristic:
  * Variable Move-To-Front ordering (`vmtf-move-to-front`).
  * Phase saving using the `phasebits` array.
* Restarts:
  * Glucose-style dual EMA trigger; tuning constants in the Configuration section.
* Clause deletion:
  * LBD-aware selection and mark-and-skip deletion via `collect-deletable`,
    `sort-by-score`, `mark-deleted`, and `maybe-delete-clauses`.
* Entry points:
  * `cdcl-solve` loads clauses, runs the full CDCL loop, and returns `:sat` or
    `:unsat`.
  * `get-model` converts the solver state to a DIMACS-style assignment alist.

### `dimacs.lisp`

* Implements tokenization (`skip-to-newline`, `read-token`), integer parsing,
  and DIMACS CNF parsing (`parse-dimacs-string`).
* Provides file readers (`read-file-chars`, `read-dimacs-file`), DIMACS literal
  converters, and result printing (`print-model-alist`, `print-result`).
* `solve-dimacs` loads a DIMACS CNF from disk, calls `cdcl-solve`, then emits
  the `s`/`v` lines expected by DIMACS tools.

### `main.lisp`

* Loads `solver.lisp` followed by `dimacs.lisp`.
* Defines `(solve filename)` macro for interactive ACL2 sessions; the macro
  loads a DIMACS file, invokes `solve-dimacs`, and discards the ACL2 return
  values.

### `tests.lisp`

* Program-mode tests that exercise:
  * Literal round-trips through `dimacs->lit`/`lit->dimacs`.
  * Integer parser edge cases.
  * Trivial SAT and UNSAT clause sets via `cdcl-solve`.
  * Parsing and solving a short DIMACS snippet.
* `run-all-tests` prints PASS/FAIL lines; `make test` runs these checks.

### `Makefile`

* `make test-sat`/`make test-unsat` — generate tiny DIMACS instances under
  `tests/` and pass them through `solve-dimacs`.
* `make bench FILE=...` — run the solver on an arbitrary DIMACS file.
* `make check` — ACL2 load of `solver.lisp` and `dimacs.lisp` to ensure they
  translate; no SAT run is performed.
* `make test` — loads solver, DIMACS utilities, and the tests, then runs
  `run-all-tests`.  All tests were verified to pass prior to this README.

## CONFIGURATION CONSTANTS

The solver exposes several `defconst` parameters that control heuristics:

| Constant | Description |
| --- | --- |
| `*ema-fast-alpha* = 3/100` | Fast EMA weighting for Glucose restarts (≈33-conflict window). |
| `*ema-slow-alpha* = 1/100000` | Slow EMA weighting (≈100k-conflict window). |
| `*restart-margin* = 5/4` | Restart trigger when `ema-f > margin * ema-s`. |
| `*restart-min-conflicts* = 50` | Minimum conflicts before a restart is eligible. |
| `*act-decay* = 999/1000` | Clause activity decay applied during rescaling. |
| `*act-rescale* = 10^-20` | Scaling factor when activities overflow. |
| `*act-max* = 10^20` | Upper bound before activity rescaling occurs. |
| `*lbd-keep* = 2` | LBD threshold for protecting a clause from deletion. |

Additional runtime fields act as dynamic knobs:

* `del-lim` (stobj field) — threshold for triggering clause deletion; initialized
  to `nc + 1000` in `init-solver` and doubled after each deletion pass.
* `act-inc` — clause activity increment, rescaled together with clause activity.
* `phasebits` — per-variable saved phase applied at each decision.
* `vmtf` fields — control head/timestamps of the decision ordering.
* `prop-q`, `trail-sz`, and `tlim` — track enqueue positions and decision-level
  boundaries for backtracking.

## HEURISTICS AND IMPLEMENTATION DETAILS

* **Two-Watched Literals (2WL)**: Each clause stores its literals contiguously in
  `ldata`.  Watches are maintained in `watch[lit]` as `(cid . blocker)` pairs.
  `process-watch-list` handles blocker checks, watcher swaps, new watcher search,
  unit propagation, and conflict detection.
* **Conflict Analysis / Learning**: Uses seen bits (`seen` array) to collect
  literals involved in conflicts, computes the 1-UIP, and measures LBD.  Learned
  clauses are stored with asserting literal at index 0, second highest level
  literal at index 1, and watchers installed on both.
* **Decision Heuristic**: Variable Move-To-Front (VMTF) list is updated whenever
  a variable is assigned or appears in a learned clause.  Phase saving picks the
  last successful polarity via `phasebits`.
* **Clause Activity and Deletion**:
  * Clause activity is bumped on each learning event and decays via `*act-decay*`
    when rescaling occurs.
  * Candidate clauses are ranked by `(lbd, -activity)` and roughly half of the
    worst candidates are marked deleted when `nlrn >= del-lim`.
* **Restarts**: Fast (`ema-f`) and slow (`ema-s`) EMA of LBD are updated per
  conflict.  A restart occurs when minimum conflict count is reached and
  `ema-f > *restart-margin* * ema-s`.
* **Initialization**: `init-solver` sizes arrays to `nc + 200000` clauses and
  `nv + 1` variables, clears assignments, and installs watchers for all clauses.
  Unit clauses are enqueued immediately; empty clauses terminate with `:unsat`.

## USAGE

### Command Line

```sh
make test-sat
make test-unsat
make bench FILE=path/to/problem.cnf
make check
make test
echo '(ld "main.lisp") (solve-dimacs "foo.cnf" state solver) (acl2::quit)' | acl2
```

### ACL2 Session

```lisp
(ld "main.lisp")
(solve-dimacs "tests/sat_small.cnf" state solver)
(ld "tests.lisp")
(run-all-tests)
```

### Programmatic Access

```lisp
(with-local-stobj solver
  (mv-let (res solver)
    (cdcl-solve 3 '((2 4) (3 5 6) ...) solver)
    (if (eq res :sat)
        (get-model solver)
      res)))
```

`cdcl-solve` expects literals in the internal encoding (`pos-lit`, `neg-lit`).
`solve-dimacs` handles the DIMACS conversion and supports end-to-end runs from
files. All functions are defined in :program mode; there are no guard-verification
proofs or ACL2 theorems in this repository. All current tests (`make test`) pass.*** End Patch
