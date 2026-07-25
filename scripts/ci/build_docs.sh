#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT/docs"
for source in \
  blueprint.tex \
  textbook_number_theorists.tex \
  textbook_formal_language_theorists.tex \
  textbook_lean_experts.tex
do
  latexmk -pdf -interaction=nonstopmode -halt-on-error "$source"
done
