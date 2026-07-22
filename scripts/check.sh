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

python3 -m unittest -v tests.test_regex_cert
for certificate in data/certificates/*.json; do
  python3 scripts/check_certificate.py "$certificate"
done
python3 scripts/lint_claims.py
python3 scripts/check_proof_holes.py

if [[ "$STATIC_ONLY" -eq 0 ]]; then
  if ! command -v lake >/dev/null 2>&1; then
    echo "lake is not installed; use --static only for repository-generation checks" >&2
    exit 3
  fi
  lake build
  lake env lean GSHTest/Smoke.lean
fi

echo "All requested checks passed."
