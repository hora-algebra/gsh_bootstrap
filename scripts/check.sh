#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

STATIC_ONLY=0
if [[ "${1:-}" == "--static" ]]; then
  STATIC_ONLY=1
elif [[ $# -gt 0 ]]; then
  echo "usage: $0 [--static]" >&2
  exit 2
fi

python3 -m unittest discover -s tests -v
for certificate in data/certificates/*.json; do
  python3 scripts/ci/check_certificate.py "$certificate"
done
python3 scripts/ci/verify_small_group_witnesses.py
python3 scripts/ci/completeness_upgrade.py
python3 scripts/ci/f20_alph7_obstruction.py
# The verdicts are committed so they can be reviewed, and regenerated here so
# they cannot be edited. A difference means either the code changed without the
# verdict being refreshed, or the verdict was written by hand.
if ! git diff --quiet -- data/verdicts/ 2>/dev/null; then
  echo "data/verdicts/ changed when regenerated; commit the new verdicts" >&2
  git --no-pager diff --stat -- data/verdicts/ >&2
  exit 4
fi
python3 scripts/ci/lint_claims.py
python3 scripts/ci/check_proof_holes.py
# Re-run the fast research scripts. Catches a script that crashes, stops
# importing, or hangs -- not a changed verdict, which is what the migration
# tracked in data/verdicts/PENDING.md is for.
python3 scripts/ci/run_research.py --tier fast

if [[ "$STATIC_ONLY" -eq 0 ]]; then
  if ! command -v lake >/dev/null 2>&1; then
    echo "lake is not installed; use --static only for repository-generation checks" >&2
    exit 3
  fi
  lake build
  lake env lean GSHTest/Smoke.lean
  # Machine-checked axiom audit: fails if any ladder theorem acquires `sorryAx`,
  # `Lean.ofReduceBool` (`native_decide`), or any other axiom.
  lake env lean GSHTest/Axioms.lean
fi

echo "All requested checks passed."
