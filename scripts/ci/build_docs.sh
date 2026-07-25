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
absent=()

cleanup() {
  local rc=$?
  if (( rc != 0 && publishing == 1 )); then
    # Put back exactly what was there before the publish began.
    #
    # A stop-time review caught the first version of this reporting success it
    # had not achieved: when a restoring `mv` failed -- a read-only mount, a
    # full disk, a permission change mid-run -- the handler still printed
    # "rolled back" and then deleted the staging directory, taking the only
    # remaining copy of the previous build with it. A rollback that can destroy
    # what it is rolling back to is worse than no rollback, because the operator
    # is told the opposite of what happened. So: if any restore fails, keep the
    # backup where it is, name it, and exit with a status of its own.
    local failed=0
    # `cp`, not `mv`: restoring by moving emptied the backup as it went, so a
    # restore that failed halfway left the message below ("preserved,
    # undeleted") true of only the files it had not reached yet. Copying keeps
    # the previous build complete whatever happens.
    for previous in "$backup"/*.pdf; do
      [[ -e "$previous" ]] || continue
      cp -p "$previous" "pdf/$(basename "$previous")" || failed=1
    done
    # Restoring the backups is not enough on its own. A document that had no
    # published PDF before this run has nothing to restore, so round three of
    # the review published one, failed the next `mv`, and left the new file
    # behind: `docs/pdf/` came out of the "rollback" holding a file that was
    # never there. Anything with no previous version is removed instead.
    for name in ${absent[@]+"${absent[@]}"}; do
      [[ -e "pdf/$name" ]] || continue
      rm -f "pdf/$name" || failed=1
    done
    if (( failed )); then
      echo "ROLLBACK FAILED: docs/pdf/ is a mixture of two builds." >&2
      echo "The previous build is preserved, undeleted, in $backup" >&2
      exit 75
    fi
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
absent=()
for source in "${SOURCES[@]}"; do
  name="$(basename "${source%.tex}").pdf"
  if [[ -e "pdf/$name" ]]; then
    cp -p "pdf/$name" "$backup/$name"
  else
    absent+=("$name")
  fi
done

publishing=1
for source in "${SOURCES[@]}"; do
  name="$(basename "${source%.tex}").pdf"
  mv -f "$stage/$name" "pdf/$name"
done
publishing=0

echo "rebuilt ${#SOURCES[@]} PDF(s) in docs/pdf/"
