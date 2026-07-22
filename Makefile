.PHONY: bootstrap build test python-test certificates lint check static-check docs clean

bootstrap:
	./scripts/bootstrap.sh

build:
	lake build

test:
	lake env lean GSHTest/Smoke.lean

python-test:
	python3 -m unittest -v tests.test_regex_cert

certificates:
	@for f in data/certificates/*.json; do python3 scripts/check_certificate.py "$$f"; done

lint:
	python3 scripts/lint_claims.py
	python3 scripts/check_proof_holes.py

check: build test python-test certificates lint

static-check: python-test certificates lint

docs:
	./scripts/build_docs.sh

clean:
	lake clean || true
	cd docs && latexmk -C blueprint.tex textbook_number_theorists.tex textbook_formal_language_theorists.tex textbook_lean_experts.tex || true
