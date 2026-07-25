#!/usr/bin/env bash
# Rebuild the tracked PDFs in `docs/pdf/` from their sources in `docs/`.
#
# Five rounds of adversarial review have gone through this script, and every
# repair until the fifth shared one mistake: it trusted an exit code for a fact
# the exit code does not report. The fifth round injected an `mv` that deleted
# its destination and exited 0; the script lost all four tracked PDFs and
# printed "rebuilt 4 PDF(s)". An `mv` that did nothing at all and exited 0 got
# the previous build reported as the new one. A backup `cp` that silently did
# nothing got "rolled back to the previous build" printed over a directory
# holding a mixture.
#
# So nothing here believes a command. Every step states a postcondition and
# checks it with `cmp`, a different binary from the ones whose work it checks:
#
#   * each document compiles, and the staged output exists and is non-empty;
#   * each previously published PDF is copied aside and the copy verified equal
#     to the original before anything is overwritten;
#   * publication copies rather than moves, so the staged build survives it, and
#     each published file is verified equal to what was staged;
#   * any failure -- including a command that "succeeded" without doing its job
#     -- restores from the verified backups, removes documents that had no
#     previous version, and verifies the restoration too.
#
# The earlier bugs are kept in the history: `ROOT` was one directory short after
# this script moved into `scripts/ci/` and it could not run at all; latexmk wrote
# beside the source so `docs/pdf/` had no producer; publishing per document left
# a mixture of two builds when one failed; restoring by `mv` emptied the backup
# it then reported as preserved.
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

fail() {
  echo "build_docs: $1" >&2
  exit "${2:-1}"
}

cleanup() {
  local rc=$?
  if (( rc != 0 && publishing == 1 )); then
    local broken=0 previous name
    for previous in "$backup"/*.pdf; do
      [[ -e "$previous" ]] || continue
      name="$(basename "$previous")"
      cp -p "$previous" "pdf/$name" || broken=1
      cmp -s "$previous" "pdf/$name" || broken=1
    done
    # A document with no previous version has nothing to restore; leaving the
    # one just published would make the "rollback" invent a file.
    for name in ${absent[@]+"${absent[@]}"}; do
      [[ -e "pdf/$name" ]] || continue
      rm -f "pdf/$name" || broken=1
    done
    if (( broken )); then
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
  [[ -s "$produced" ]] \
    || fail "latexmk exited 0 but produced no $produced; refusing to publish"
done

mkdir -p pdf "$backup"
for source in "${SOURCES[@]}"; do
  name="$(basename "${source%.tex}").pdf"
  if [[ -e "pdf/$name" ]]; then
    cp -p "pdf/$name" "$backup/$name"
    cmp -s "pdf/$name" "$backup/$name" \
      || fail "could not back up docs/pdf/$name; refusing to publish over it"
  else
    absent+=("$name")
  fi
done

publishing=1
for source in "${SOURCES[@]}"; do
  name="$(basename "${source%.tex}").pdf"
  # `cp`, not `mv`: the staged build has to survive publication so the result
  # can be compared against it.
  cp "$stage/$name" "pdf/$name"
done
for source in "${SOURCES[@]}"; do
  name="$(basename "${source%.tex}").pdf"
  cmp -s "$stage/$name" "pdf/$name" \
    || fail "docs/pdf/$name is not what was built; rolling back" 76
done
publishing=0

echo "rebuilt ${#SOURCES[@]} PDF(s) in docs/pdf/"
