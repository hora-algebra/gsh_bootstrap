#!/usr/bin/env python3
"""Command-line entry point for the generalized-regex certificate checker."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.regex_cert import CertificateError, load_and_check  # noqa: E402


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    parser.add_argument("--json", action="store_true", dest="as_json")
    args = parser.parse_args()
    try:
        report = load_and_check(args.certificate)
    except CertificateError as error:
        if args.as_json:
            print(json.dumps({"ok": False, "error": str(error)}, ensure_ascii=False))
        else:
            print(f"ERROR: {error}", file=sys.stderr)
        return 2
    if args.as_json:
        print(json.dumps(report.to_json(), ensure_ascii=False, sort_keys=True))
    elif report.ok:
        print(
            "PASS: equivalent; "
            f"height={report.actual_height} <= {report.claimed_height}; "
            f"minimal states expression={report.expression_states}, target={report.target_states}"
        )
    else:
        print(
            "FAIL: languages differ; shortest witness="
            + repr(list(report.witness or ())),
            file=sys.stderr,
        )
    return 0 if report.ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
