#!/usr/bin/env bash
# Rebuild the tracked PDFs in `docs/pdf/` from their sources in `docs/`.
#
# Four bugs fixed, each found after the previous fix looked finished.
#
# 1. The `..` was one level short after this script moved into `scripts/ci/`, so
#    `ROOT` was the `scripts` directory and the `cd` hit a `scripts/docs` that
#    does not exist. The script could not have run since the move.
# 2. latexmk wrote next to the source, so nothing regenerated `docs/pdf/`, whose
#    four tracked PDFs were free to drift from the `.tex` they claim to render.
# 3. Publishing each PDF as soon as latexmk exited 0 trusted the exit code for a
#    fact it does not report: with a stale PDF left beside a source, a latexmk
#    that exits 0 without producing anything replaced four good tracked PDFs
#    with four old ones and reported success. Fixed by building into a fresh
#    staging directory and requiring each output to exist there and be non-empty.
# 4. The publish loop was still not transactional. An adversarial review injected
#    a failure into the second `mv` and got one document from the new build and
#    three from the old one, with no indication which was which. A half-published
#    set is worse than either whole one, because the four documents cross-cite.
#    So the previously published files are copied aside first and restored if any
#    part of the publish fails.
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
backup="$stage/previously-published"
publishing=0

cleanup() {
  local rc=$?
  if (( rc != 0 && publishing == 1 )); then
    # Put back exactly what was there before the publish began. Restoring is
    # best effort by necessity -- if this fails too, say so loudly rather than
    # leaving a silent mixture.
    for previous in "$backup"/*.pdf; do
      [[ -e "$previous" ]] || continue
      mv -f "$previous" "pdf/$(basename "$previous")" \
        || echo "RESTORE FAILED for $(basename "$previous"); docs/pdf/ is now a mixture" >&2
    done
    echo "publish failed; docs/pdf/ rolled back to the previous build" >&2
  fi
  rm -rf "$stage"
  exit "$rc"
}
trap cleanup EXIT

for source in "${SOURCES[@]}"; do
  latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir="$stage" "$source"
  produced="$stage/$(basename "${source%.tex}").pdf"
  if [[ ! -s "$produced" ]]; then
    echo "latexmk exited 0 but produced no $produced; refusing to publish" >&2
    exit 1
  fi
done

mkdir -p pdf "$backup"
for source in "${SOURCES[@]}"; do
  name="$(basename "${source%.tex}").pdf"
  [[ -e "pdf/$name" ]] && cp -p "pdf/$name" "$backup/$name"
done

publishing=1
for source in "${SOURCES[@]}"; do
  name="$(basename "${source%.tex}").pdf"
  mv -f "$stage/$name" "pdf/$name"
done
publishing=0

echo "rebuilt ${#SOURCES[@]} PDF(s) in docs/pdf/"
