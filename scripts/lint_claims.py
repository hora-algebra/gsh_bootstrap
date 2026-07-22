#!/usr/bin/env python3
"""Lightweight structural lint for the claims ledger and research prose."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
LEDGER = ROOT / "CLAIMS_LEDGER.md"
VALID = {
    "PROVED",
    "CITED",
    "COMPUTED",
    "CONJECTURAL",
    "SPECULATIVE",
    "REFUTED",
    "UNREVIEWED",
}


def parse_rows(text: str) -> list[list[str]]:
    rows: list[list[str]] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line.startswith("|") or line.startswith("|---"):
            continue
        cells = [cell.strip() for cell in line.strip("|").split("|")]
        if cells and cells[0] == "ID":
            continue
        if len(cells) == 6:
            rows.append(cells)
    return rows


def main() -> int:
    errors: list[str] = []
    text = LEDGER.read_text(encoding="utf-8")
    rows = parse_rows(text)
    seen: set[str] = set()
    if not rows:
        errors.append("CLAIMS_LEDGER.md contains no parseable claim rows")
    for cells in rows:
        claim_id, claim, status, evidence, owner, review = cells
        if claim_id in seen:
            errors.append(f"duplicate claim id: {claim_id}")
        seen.add(claim_id)
        if not re.fullmatch(r"[A-Z0-9][A-Z0-9-]*", claim_id):
            errors.append(f"invalid claim id: {claim_id}")
        if status not in VALID:
            errors.append(f"{claim_id}: invalid status {status!r}")
        if len(claim) < 12:
            errors.append(f"{claim_id}: claim is too short to be auditable")
        if status in {"CITED", "PROVED", "COMPUTED", "REFUTED"} and len(evidence) < 8:
            errors.append(f"{claim_id}: {status} row lacks evidence")
        if status == "CITED" and not re.search(r"\d{4}|§|Theorem|theorem|module", evidence):
            errors.append(f"{claim_id}: cited evidence should identify a date/section/theorem/module")
        if owner in {"", "TBD", "?"}:
            errors.append(f"{claim_id}: missing owner")
        if review and not re.fullmatch(r"\d{4}-\d{2}-\d{2}|pending first CI", review):
            errors.append(f"{claim_id}: malformed review date {review!r}")

    prose_files = [
        ROOT / "README.md",
        ROOT / "SURVEY.md",
        ROOT / "SCENARIOS.md",
        ROOT / "SUGGESTIONS.md",
        ROOT / "ROADMAP.md",
    ]
    forbidden = {
        "A5 is the first unresolved": "A_5 is not the first unresolved group-order case",
        "A_5 is the first unresolved": "A_5 is not the first unresolved group-order case",
        "search proves": "bounded search is not a mathematical lower bound",
        "obviously height": "language height requires minimization over expressions",
    }
    for path in prose_files:
        body = path.read_text(encoding="utf-8")
        for phrase, explanation in forbidden.items():
            if phrase.lower() in body.lower():
                errors.append(f"{path.name}: forbidden phrase {phrase!r}: {explanation}")

    if errors:
        print("Claims lint failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"Claims lint passed: {len(rows)} ledger rows checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
