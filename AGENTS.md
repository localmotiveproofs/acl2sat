# Repository Guidelines

## Project Structure & Module Organization
`solver.lisp` hosts the CDCL core (stobj layout, watched-literal queues, heuristics). `dimacs.lisp` covers DIMACS parsing plus file I/O helpers, while `main.lisp` loads both modules and exposes the `solve` macro for interactive runs. `Makefile` is the canonical entry point and seeds sample DIMACS cases under `tests/`. Keep any generated CNF fixtures in `tests/` and name them descriptively (for example, `tests/industrial_10k.cnf`).

## Build, Test, and Development Commands
- `make check` — load every source file in ACL2 to confirm it typechecks; run this before pushing.
- `make test-sat` / `make test-unsat` — generate tiny DIMACS files and solve them for SAT/UNSAT smoke coverage, printing the `s`/`v` lines.
- `make bench FILE=path/to/file.cnf` — execute the solver against an arbitrary DIMACS input for regressions or profiling.
- ACL2 shell run: `echo '(ld "main.lisp") (solve-dimacs "tests/foo.cnf" state solver) (acl2::quit)' | acl2`.

## Coding Style & Naming Conventions
Follow ACL2 conventions already present in `solver.lisp`: two-space indentation inside forms, line up keyword/value pairs, and group related definitions with banner comments. Pure functions should use `defun`, utilities that expand inline use `defmacro`. Stobj fields and helpers follow the `foo`/`fooi`/`update-fooi` pattern; keep new names consistent (e.g., `cl-` prefix for clause helpers, `lit-` for literal utilities). Favor descriptive lowercase names with hyphens, and document non-obvious heuristics using leading semicolon blocks.

## Testing Guidelines
Run the smoke targets (`make test-sat`, `make test-unsat`) before every commit to ensure solver sanity. When adding DIMACS fixtures, store them under `tests/` and add a short comment header describing the property being exercised. Benchmarks that surface bugs should become reproducible tests via a new `make` rule or by documenting the exact `make bench` invocation in your PR.

## Commit & Pull Request Guidelines
Commits follow the existing history: a short, imperative subject (≤72 chars, e.g., `Improve conflict analysis logging`) with optional wrapped body text for rationale and tests. Each PR should include a brief problem statement, summary of solver or parser changes, how to reproduce/verify (`make check`, `make test-*`, `make bench FILE=...`), and any performance or resource notes. Attach solver output snippets when demonstrating SAT/UNSAT fixes, and link related issues or DIMACS benchmarks for traceability.

## Security & Configuration Tips
Store only plaintext DIMACS benchmarks—never proprietary data. Generated artifacts (`*.fasl`, `*.cert`, `tests/*.cnf`) should be cleaned with `make clean`. ACL2 invocations rely on the `ACL2` binary in `$PATH`; keep the major version consistent when comparing solver behavior.
