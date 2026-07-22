#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

INSTALL_ELAN=0
OFFLINE=0
for arg in "$@"; do
  case "$arg" in
    --install-elan) INSTALL_ELAN=1 ;;
    --offline) OFFLINE=1 ;;
    *) echo "unknown argument: $arg" >&2; exit 2 ;;
  esac
done

python3 -m unittest -v tests.test_regex_cert
python3 scripts/check_certificate.py data/certificates/height0_ends_a.json
python3 scripts/check_certificate.py data/certificates/height1_even_a.json

if ! command -v lake >/dev/null 2>&1; then
  if [[ "$INSTALL_ELAN" -eq 0 ]]; then
    cat >&2 <<'MSG'
Lean/Lake is not installed. Python checks passed.
Install elan from the official Lean repository, then rerun this script, or run:
  ./scripts/bootstrap.sh --install-elan
MSG
    exit 3
  fi
  if ! command -v curl >/dev/null 2>&1; then
    echo "curl is required for --install-elan" >&2
    exit 3
  fi
  curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
  # shellcheck disable=SC1090
  source "$HOME/.elan/env"
fi

if [[ "$OFFLINE" -eq 0 ]]; then
  lake update
  lake exe cache get
fi
lake build
lake env lean GSHTest/Smoke.lean
python3 scripts/lint_claims.py
python3 scripts/check_proof_holes.py

echo "Bootstrap complete."
