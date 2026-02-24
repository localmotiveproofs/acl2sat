# Makefile for acl2sat CDCL SAT solver
#
# Targets:
#   make test-sat       — run a small satisfiable instance
#   make test-unsat     — run a small unsatisfiable instance
#   make bench FILE=x   — solve an arbitrary DIMACS file
#   make check          — load and typecheck all source files in ACL2

ACL2 ?= acl2

# The ACL2 invocation that loads solver + DIMACS support
LOAD_CMD = (ld \"solver.lisp\" :ld-error-action :error) \
           (ld \"dimacs.lisp\" :ld-error-action :error)

.PHONY: test-sat test-unsat bench check clean

## Smoke tests —————————————————————————————————————————————————

test-sat: tests/sat_small.cnf
	@echo "=== SAT instance ==="
	@echo '$(LOAD_CMD) (solve-dimacs "tests/sat_small.cnf" state solver) (acl2::quit)' \
	  | $(ACL2) 2>&1 | grep -E '^s |^v '

test-unsat: tests/unsat_small.cnf
	@echo "=== UNSAT instance ==="
	@echo '$(LOAD_CMD) (solve-dimacs "tests/unsat_small.cnf" state solver) (acl2::quit)' \
	  | $(ACL2) 2>&1 | grep -E '^s '

## General benchmark ————————————————————————————————————————————

bench:
ifndef FILE
	$(error Usage: make bench FILE=path/to/problem.cnf)
endif
	@echo '$(LOAD_CMD) (solve-dimacs "$(FILE)" state solver) (acl2::quit)' \
	  | $(ACL2) 2>&1 | grep -E '^s |^v '

## Load-check (no solving) ————————————————————————————————————

check:
	@echo '$(LOAD_CMD) (acl2::quit)' | $(ACL2) 2>&1 | tail -5

## Generate tiny test instances ——————————————————————————————

tests/sat_small.cnf:
	@mkdir -p tests
	@printf 'c Simple satisfiable instance: x1 OR x2, NOT x1 OR x2\n' > $@
	@printf 'p cnf 3 4\n'  >> $@
	@printf '1 2 0\n'       >> $@
	@printf '-1 2 0\n'      >> $@
	@printf '1 -2 3 0\n'    >> $@
	@printf '-3 0\n'        >> $@

tests/unsat_small.cnf:
	@mkdir -p tests
	@printf 'c Minimal UNSAT: p AND NOT p\n' > $@
	@printf 'p cnf 1 2\n' >> $@
	@printf '1 0\n'        >> $@
	@printf '-1 0\n'       >> $@

clean:
	rm -rf tests/*.cnf *.fasl *.cert
