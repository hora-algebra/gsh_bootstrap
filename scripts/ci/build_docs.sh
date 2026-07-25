#!/usr/bin/env bash
# Rebuild the tracked PDFs in `docs/pdf/` from their sources in `docs/`.
#
# Two bugs fixed 2026-07-25. The `..` was one level short after this script
# moved into `scripts/ci/`, so `ROOT` was the `scripts` directory and the `cd`
# hit a `scripts/docs` that does not exist -- the script could not have run
# since the move. And latexmk wrote next to the source, so nothing regenerated
# `docs/pdf/`, whose four tracked PDFs were free to drift from the `.tex` they
# claim to render. They are moved into place here so the tracked artifact has a
# producer.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT/docs"
mkdir -p pdf
for source in \
  blueprint.tex \
  textbook_number_theorists.tex \
  textbook_formal_language_theorists.tex \
  textbook_lean_experts.tex
do
  latexmk -pdf -interaction=nonstopmode -halt-on-error "$source"
  mv -f "${source%.tex}.pdf" pdf/
done
