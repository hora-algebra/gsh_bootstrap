#!/usr/bin/env python3
"""Reject axioms/admit and require every Lean `sorry` to be registered."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
OBLIGATIONS = (ROOT / "PROOF_OBLIGATIONS.md").read_text(encoding="utf-8")
ID_RE = re.compile(r"(?:L|M|N)-[A-Z0-9]+(?:-[A-Z0-9]+)*-\d{3}")


def main() -> int:
    errors: list[str] = []
    registered = set(ID_RE.findall(OBLIGATIONS))
    sorry_count = 0
    for path in sorted(ROOT.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        lines = path.read_text(encoding="utf-8").splitlines()
        for number, line in enumerate(lines, start=1):
            code = line.split("--", 1)[0]
            if re.search(r"\baxiom\b", code):
                errors.append(f"{path.relative_to(ROOT)}:{number}: axiom is forbidden")
            if re.search(r"\badmit\b", code):
                errors.append(f"{path.relative_to(ROOT)}:{number}: admit is forbidden")
            if re.search(r"\bsorry\b", code):
                sorry_count += 1
                nearby = " ".join(lines[max(0, number - 7): min(len(lines), number + 1)])
                match = ID_RE.search(nearby)
                if not match:
                    errors.append(
                        f"{path.relative_to(ROOT)}:{number}: sorry lacks a nearby BLUEPRINT obligation id"
                    )
                elif match.group(0) not in registered:
                    errors.append(
                        f"{path.relative_to(ROOT)}:{number}: unknown obligation {match.group(0)}"
                    )
    if errors:
        print("Proof-hole check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"Proof-hole check passed: {sorry_count} registered Lean placeholders")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
