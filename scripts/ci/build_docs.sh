#!/usr/bin/env bash
# Rebuild the tracked PDFs in `docs/pdf/` from their sources in `docs/`.
#
# Three bugs fixed. The `..` was one level short after this script moved into
# `scripts/ci/`, so `ROOT` was the `scripts` directory and the `cd` hit a
# `scripts/docs` that does not exist -- the script could not have run since the
# move (2026-07-25). And latexmk wrote next to the source, so nothing
# regenerated `docs/pdf/`, whose four tracked PDFs were free to drift from the
# `.tex` they claim to render.
#
# The third came from an adversarial review of that repair (2026-07-26). Moving
# each PDF as soon as latexmk exited 0 trusted the exit code for a fact it does
# not report. With a stale `docs/blueprint.pdf` left over from the old
# next-to-the-source behaviour, a latexmk that exits 0 without producing
# anything -- a wrapper, a cache hit misconfigured, a `latexmk` shadowed on
# PATH -- overwrote four good tracked PDFs with four old ones and reported
# success. It was also non-transactional: a failure on the second document left
# the first already replaced, so the tracked set was a mixture of two builds.
#
# So: build into a fresh staging directory that starts empty, require each
# output to exist there and be non-empty, and publish only after every document
# has compiled. A stale file next to the source can no longer be mistaken for
# today's output, because the output is never read from there.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
cd "$ROOT/docs"

SOURCES=(
  blueprint.tex
  textbook_number_theorists.tex
  textbook_formal_language_theorists.tex
  textbook_lean_experts.tex
)

stage="$(mktemp -d)"
trap 'rm -rf "$stage"' EXIT

for source in "${SOURCES[@]}"; do
  latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$stage" "$source"
  produced="$stage/$(basename "${source%.tex}").pdf"
  if [[ ! -s "$produced" ]]; then
    echo "latexmk exited 0 but produced no $produced; refusing to publish" >&2
    exit 1
  fi
done

mkdir -p pdf
for source in "${SOURCES[@]}"; do
  mv -f "$stage/$(basename "${source%.tex}").pdf" pdf/
done
echo "rebuilt ${#SOURCES[@]} PDF(s) in docs/pdf/"
