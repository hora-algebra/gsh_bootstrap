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
    "EMPIRICAL",
    "CONJECTURAL",
    "SPECULATIVE",
    "REFUTED",
    "UNREVIEWED",
}

# `COMPUTED` means the claim was reduced to a finite object and that object was
# traversed exhaustively. Bounded-length agreement and random words are
# `EMPIRICAL`: they can refute but never establish. The two were conflated until
# the 2026-07-25 audit, so the split is enforced here rather than by convention.
#
# Note what is deliberately NOT accepted as an attestation: the bare word
# "exhaustive". The row that motivated this gate said "reconstruction checks
# exhaustive to bounded length", which is a sample wearing the word. Only the
# phrases below, which name an actual decision procedure, count.
SAMPLING_MARKER = re.compile(
    r"\brandom\b|\bsampl\w*|\bspot[- ]check|bounded[- ]exhaustive"
    r"|exhaustive to bounded|bounded length|\blength\s*(?:<=|≤|&le;)?\s*\d+",
    re.IGNORECASE,
)
# Deliberately narrow. "exact product-automaton search" is NOT here: in
# `A4-STD-01` that phrase described a sub-step (the atoms) while the end-to-end
# claim rested on length-16 agreement, so accepting it would let a row pass on
# the strength of a component it does not depend on. An attestation must name a
# procedure that decides *the row's own claim*.
COMPLETENESS_ATTESTATION = re.compile(
    r"product reachability|complete enumeration|no sampling"
    r"|full transition[- ]monoid|complete finite proof|exhaustive traversal"
    r"|exact DFA equivalence",
    re.IGNORECASE,
)
CLAIM_ID = re.compile(r"\b[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+\b")


# A cell boundary is a pipe that is not escaped as `\|`. Markdown tables carry
# literal pipes (e.g. `\|w\|_a`) only in escaped form, so splitting on a bare
# "|" silently shreds those rows into the wrong number of cells.
UNESCAPED_PIPE = re.compile(r"(?<!\\)\|")


def split_cells(line: str) -> list[str]:
    parts = UNESCAPED_PIPE.split(line)
    # A table row opens and closes with an unescaped pipe, producing empty
    # leading/trailing fragments that are not cells.
    if parts and not parts[0].strip():
        parts = parts[1:]
    if parts and not parts[-1].strip():
        parts = parts[:-1]
    return [part.strip().replace("\\|", "|") for part in parts]


def parse_rows(text: str) -> list[list[str]]:
    rows: list[list[str]] = []
    for raw in text.splitlines():
        line = raw.strip()
        if not line.startswith("|") or line.startswith("|---"):
            continue
        cells = split_cells(line)
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
        if status in {"CITED", "PROVED", "COMPUTED", "EMPIRICAL", "REFUTED"} and len(evidence) < 8:
            errors.append(f"{claim_id}: {status} row lacks evidence")
        if status == "COMPUTED" and SAMPLING_MARKER.search(evidence):
            if not COMPLETENESS_ATTESTATION.search(evidence):
                errors.append(
                    f"{claim_id}: COMPUTED row cites sampling "
                    f"({SAMPLING_MARKER.search(evidence).group(0)!r}) with no completeness "
                    "attestation. Either name the exhaustive decision procedure "
                    "(product reachability / complete enumeration / full transition-monoid "
                    "search / exact DFA equivalence) or set the status to EMPIRICAL."
                )
        if status == "EMPIRICAL" and not SAMPLING_MARKER.search(evidence):
            errors.append(
                f"{claim_id}: EMPIRICAL row must state what the sample was "
                "(bounded length, random words, spot checks) so the gap is auditable"
            )
        if status == "CITED" and not re.search(r"\d{4}|§|Theorem|theorem|module", evidence):
            errors.append(f"{claim_id}: cited evidence should identify a date/section/theorem/module")
        if owner in {"", "TBD", "?"}:
            errors.append(f"{claim_id}: missing owner")
        if review and not re.fullmatch(r"\d{4}-\d{2}-\d{2}|pending first CI", review):
            errors.append(f"{claim_id}: malformed review date {review!r}")

    # Status is the ceiling and it propagates: a row may not be stronger than the
    # rows it consumes. Citing an EMPIRICAL row is allowed only when the citing
    # row says so, which keeps the caveat travelling with the claim instead of
    # evaporating one hop at a time (the 2026-07-22 → 07-25 A_4 failure).
    empirical = {cells[0] for cells in rows if cells[2] == "EMPIRICAL"}
    for cells in rows:
        claim_id, claim, status, evidence, _owner, _review = cells
        if status == "EMPIRICAL" or not empirical:
            continue
        text = f"{claim} {evidence}"
        cited = {token for token in CLAIM_ID.findall(text) if token in empirical} - {claim_id}
        if cited and "EMPIRICAL" not in text:
            errors.append(
                f"{claim_id}: status {status} but it cites the EMPIRICAL row(s) "
                f"{', '.join(sorted(cited))} without saying so. Either mark the "
                "dependency EMPIRICAL in this row's text, or lower this row's status."
            )

    prose_files = [
        ROOT / "README.md",
        ROOT / "docs" / "SURVEY.md",
        ROOT / "docs" / "SCENARIOS.md",
        ROOT / "docs" / "SUGGESTIONS.md",
        ROOT / "docs" / "ROADMAP.md",
        ROOT / "RESULTS.md",
    ]
    _A4 = (
        "the A_4 full-alphabet result is EMPIRICAL (A4-FULL-01): its reconstruction step "
        "is checked only to length 4 plus random words"
    )
    forbidden = {
        "A5 is the first unresolved": "A_5 is not the first unresolved group-order case",
        "A_5 is the first unresolved": "A_5 is not the first unresolved group-order case",
        "search proves": "bounded search is not a mathematical lower bound",
        "obviously height": "language height requires minimization over expressions",
        # Vocabulary bound to status (2026-07-25 audit). The verb must not
        # outrun the label; these five sentences all did.
        "order ≤ 12 is settled": _A4,
        "barrier moved from order 12 to order 20": _A4,
        "位数 ≤ 12 の全群が決着": _A4,
        "障壁が位数 12 から位数 20 に移動": _A4,
        "A4 は反例候補から完全に外れた": _A4,
    }
    # Checked per line, so that a line which *withdraws* a claim may quote it.
    # Without this exemption the retraction is unwritable, and an unwritable
    # retraction is how a wrong claim survives.
    withdrawal = re.compile(r"withdraw|retract|撤回|降格|previously (read|claimed)", re.IGNORECASE)
    for path in prose_files:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if withdrawal.search(line):
                continue
            for phrase, explanation in forbidden.items():
                if phrase.lower() in line.lower():
                    errors.append(
                        f"{path.name}:{number}: forbidden phrase {phrase!r}: {explanation}"
                    )

    if errors:
        print("Claims lint failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"Claims lint passed: {len(rows)} ledger rows checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
