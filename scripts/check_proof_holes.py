#!/usr/bin/env python3
"""Reject axioms/admit and require every Lean `sorry` to be registered.

Comments are not code: `sorry`/`axiom`/`admit` inside `--` line comments or
(nested) `/- ... -/` block comments — including docstrings — are ignored when
scanning for holes.  The BLUEPRINT-id proximity search still reads the raw
lines, because the ids themselves live in `-- BLUEPRINT:` comments.
"""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
OBLIGATIONS = (ROOT / "PROOF_OBLIGATIONS.md").read_text(encoding="utf-8")
ID_RE = re.compile(r"(?:L|M|N)-[A-Z0-9]+(?:-[A-Z0-9]+)*-\d{3}")


def strip_comments(text: str) -> str:
    """Blank out `--` line comments and nested `/- ... -/` block comments,
    preserving newlines so line numbers stay aligned."""
    out: list[str] = []
    i, n = 0, len(text)
    depth = 0
    while i < n:
        if depth == 0:
            if text.startswith("--", i):
                j = text.find("\n", i)
                if j == -1:
                    j = n
                out.append(" " * (j - i))
                i = j
            elif text.startswith("/-", i):
                depth = 1
                out.append("  ")
                i += 2
            else:
                out.append(text[i])
                i += 1
        else:
            if text.startswith("/-", i):
                depth += 1
                out.append("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append(text[i] if text[i] == "\n" else " ")
                i += 1
    return "".join(out)


def main() -> int:
    errors: list[str] = []
    registered = set(ID_RE.findall(OBLIGATIONS))
    sorry_count = 0
    for path in sorted(ROOT.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        text = path.read_text(encoding="utf-8")
        raw_lines = text.splitlines()
        code_lines = strip_comments(text).splitlines()
        for number, code in enumerate(code_lines, start=1):
            if re.search(r"\baxiom\b", code):
                errors.append(f"{path.relative_to(ROOT)}:{number}: axiom is forbidden")
            if re.search(r"\badmit\b", code):
                errors.append(f"{path.relative_to(ROOT)}:{number}: admit is forbidden")
            if re.search(r"\bsorry\b", code):
                sorry_count += 1
                nearby = " ".join(raw_lines[max(0, number - 7): min(len(raw_lines), number + 1)])
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
