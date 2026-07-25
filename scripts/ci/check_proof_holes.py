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

ROOT = Path(__file__).resolve().parents[2]
OBLIGATIONS = (ROOT / "PROOF_OBLIGATIONS.md").read_text(encoding="utf-8")
ID_RE = re.compile(r"(?:L|M|N)-[A-Z0-9]+(?:-[A-Z0-9]+)*-\d{3}")

# Being registered in PROOF_OBLIGATIONS.md is no longer enough to justify a
# `sorry`.  Only the open problem itself may be one, so that a placeholder can
# never be added to a working file and then legitimised by adding a row.
# Widening this set is a deliberate policy change, not a repair.
ALLOWED_SORRY_IDS = {"L-GSH-CHALLENGE-001"}


def strip_comments(text: str) -> str:
    """Blank out comments and string literals, keeping line numbers aligned.

    String literals matter: `GSHTest/Axioms.lean` is an audit *about* axioms, so
    its error messages contain the word, and a checker that reads a diagnostic
    as a declaration cannot be used in the one file whose job is to enforce the
    rule. Blanking `"..."` costs nothing — no Lean declaration hides inside a
    string — and it removes a whole class of false positive.
    """
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
            elif text[i] == '"':
                j = i + 1
                while j < n and text[j] != '"':
                    j += 2 if text[j] == "\\" else 1
                j = min(j + 1, n)
                out.append("".join(c if c == "\n" else " " for c in text[i:j]))
                i = j
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
            # Not anchored to the start of the line: `set_option foo in axiom
            # hidden : False` is valid Lean and slipped past a declaration-position
            # regex (2026-07-25 adversarial review). String literals are blanked
            # above, which is what made the anchor look necessary in the first place.
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
                elif match.group(0) not in ALLOWED_SORRY_IDS:
                    errors.append(
                        f"{path.relative_to(ROOT)}:{number}: sorry for {match.group(0)} is not "
                        f"permitted; only {sorted(ALLOWED_SORRY_IDS)} may be left unproved"
                    )
    if errors:
        print("Proof-hole check failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(
        f"Proof-hole check passed: {sorry_count} Lean placeholder(s), "
        f"all in {sorted(ALLOWED_SORRY_IDS)}"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
