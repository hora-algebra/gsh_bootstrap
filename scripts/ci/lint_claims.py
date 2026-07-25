#!/usr/bin/env python3
"""Lightweight structural lint for the claims ledger and research prose."""

from __future__ import annotations

from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.verdict import ORDER, ceilings  # noqa: E402

LEDGER = ROOT / "CLAIMS_LEDGER.md"
#: `COMPUTED` rows that predate `tools/verdict.py` and are still backed only by
#: prose. The list may shrink and never grow: a row added or promoted from here
#: on has to be backed by a verdict file, while the rows already here are worked
#: through in the order the audit ranked them. Migrating one means deleting its
#: line, which is a diff a reviewer can see.
PENDING = ROOT / "data" / "verdicts" / "PENDING.md"
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
# ...and an attestation that scopes itself away is not an attestation. `no
# sampling in the exhaustive parts` is a tautology, and it is how `C7C3-FULL-01`
# passed while its reconstruction step rested on words of length <= 4. This is
# the same shape as the `A4-STD-01` sub-step loophole: a true statement about a
# component, standing in for the claim. Matched attestations are discarded when
# immediately qualified.
SCOPED_AWAY = re.compile(
    r"(?:no sampling|exact)\s+(?:in|where|for|on)\b",
    re.IGNORECASE,
)


def attests_completeness(evidence: str) -> bool:
    """True when the evidence names a procedure that decides the row's own claim."""
    return bool(COMPLETENESS_ATTESTATION.search(SCOPED_AWAY.sub("", evidence)))


# A third case the two-way gate got wrong: a row whose claim rests on proofs and
# citations, which also *mentions* a bounded run as a sanity check on some
# construction. Demoting it would misdescribe it, and inventing an attestation
# would be a lie, so the only remaining move was to delete the honest mention of
# the run — the gate would have been training authors to say less. The escape is
# deliberately a fixed phrase and not a keyword: it makes the author assert, in
# writing and on a specific row, something a reviewer can go and falsify.
NOT_LOAD_BEARING = "sanity check only, not load-bearing"
CLAIM_ID = re.compile(r"\b[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+\b")
# Labels that outrank EMPIRICAL. Used by the prose propagation gate below.
STRONGER = re.compile(r"\bPROVED\b|\bCOMPUTED\b|\bCITED\b")


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


def stale_labels(text: str, empirical: set[str]) -> set[str]:
    """Ids of EMPIRICAL rows that this passage labels more strongly.

    Applied per paragraph, not per line. The first version checked lines, and a
    `RESULTS.md` paragraph that said "status は `A4-ALLLANG-01` を継いで / `COMPUTED`"
    walked straight through it: the id and the label had a newline between them.
    Prose wraps wherever it wants, so the unit of meaning is the paragraph.

    Kept as a function rather than inlined so the tests exercise the gate
    itself; a mirrored copy in the test file would be free to drift from it.
    """
    if "EMPIRICAL" in text:
        return set()
    cited = {token for token in CLAIM_ID.findall(text) if token in empirical}
    return cited if STRONGER.search(text) else set()


def paragraphs(text: str) -> list[tuple[int, str]]:
    """Blank-line separated blocks, each with the line number it starts on."""
    blocks: list[tuple[int, str]] = []
    current: list[str] = []
    start = 1
    for number, line in enumerate(text.splitlines(), start=1):
        if line.strip():
            if not current:
                start = number
            current.append(line)
        elif current:
            blocks.append((start, "\n".join(current)))
            current = []
    if current:
        blocks.append((start, "\n".join(current)))
    return blocks


def pending_rows() -> set[str]:
    """Claim ids grandfathered out of the verdict requirement, from `PENDING.md`."""
    if not PENDING.is_file():
        return set()
    # A bullet may open with several ids when one finding covers them all, so
    # take every backticked id up to the first em dash, which is where the entry
    # stops naming rows and starts describing the gap.
    found: set[str] = set()
    for line in PENDING.read_text(encoding="utf-8").splitlines():
        if not line.startswith("- `"):
            continue
        found.update(re.findall(r"`([A-Z0-9][A-Z0-9-]*)`", line.split(" — ")[0]))
    return found


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
            if not attests_completeness(evidence) and NOT_LOAD_BEARING not in evidence:
                errors.append(
                    f"{claim_id}: COMPUTED row cites sampling "
                    f"({SAMPLING_MARKER.search(evidence).group(0)!r}) with no completeness "
                    "attestation. Name the exhaustive decision procedure "
                    "(product reachability / complete enumeration / full transition-monoid "
                    f"search / exact DFA equivalence); or write {NOT_LOAD_BEARING!r} and say "
                    "what does carry the claim; or set the status to EMPIRICAL."
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

    # The same propagation rule, applied to prose. The ledger gate above stops a
    # demotion from evaporating inside CLAIMS_LEDGER.md, but the 2026-07-25 audit
    # demoted `A4-ALLLANG-01` and left `RESULTS.md` calling it COMPUTED in four
    # other places — a forbidden-phrase list cannot catch that, because the
    # offending sentences share no phrase. What they do share is structure: an
    # EMPIRICAL row's id sitting on the same line as a stronger label.
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
        text = path.read_text(encoding="utf-8")
        for number, line in enumerate(text.splitlines(), start=1):
            if withdrawal.search(line):
                continue
            for phrase, explanation in forbidden.items():
                if phrase.lower() in line.lower():
                    errors.append(
                        f"{path.name}:{number}: forbidden phrase {phrase!r}: {explanation}"
                    )
        for number, block in paragraphs(text):
            if withdrawal.search(block):
                continue
            stale = stale_labels(block, empirical)
            if stale:
                errors.append(
                    f"{path.name}:{number}: {', '.join(sorted(stale))} is EMPIRICAL but this "
                    f"paragraph labels it {STRONGER.search(block).group(0)}. Say EMPIRICAL here, "
                    "or stop attaching a status to it."
                )

    # The gate the prose checks above could not be. Everything before this point
    # reads what an author wrote about a computation; this reads what the
    # computation reported. `tools/verdict.py` explains why the distinction had
    # to become structural — the short version is `THOMAS-D2-02`, whose evidence
    # cell was true in every sentence and whose certifying program traversed a
    # finite object that had nothing to do with the claim.
    earned = ceilings()
    pending = pending_rows()
    unbacked: list[str] = []
    for cells in rows:
        claim_id, _claim, status, _evidence, _owner, _review = cells
        if status != "COMPUTED":
            continue
        ceiling = earned.get(claim_id)
        if ceiling is None:
            unbacked.append(claim_id)
            if claim_id not in pending:
                errors.append(
                    f"{claim_id}: COMPUTED with no verdict. Have the backing script "
                    "report through `tools.verdict` and name this row in a check that "
                    f"covers the whole claim, or add the row to {PENDING.name} with the "
                    "step that is still only described rather than decided."
                )
        elif ORDER.index(ceiling) < ORDER.index("COMPUTED"):
            errors.append(
                f"{claim_id}: COMPUTED, but the verdict files support only {ceiling}. "
                "Either the check that covers the whole claim is missing, a step is "
                "sampled, or no negative control fired."
            )
    stale_pending = sorted(pending - set(unbacked))
    if stale_pending:
        errors.append(
            f"{PENDING.name} lists {', '.join(stale_pending)}, which no longer needs "
            "grandfathering. Delete those lines: the list may shrink, never grow."
        )

    # Every path the registers cite must exist. Nothing checked this before, and
    # the 2026-07-25 restructure moved 59 files and rewrote 278 citations — a
    # silent typo in any one of them turns a piece of evidence into a dead end
    # that still reads like provenance.
    cited_path = re.compile(r"`((?:[\w.-]+/)+[\w.-]+\.\w+)`")
    known_absent = {
        # Deliberately outside the repository, and said so where each is cited.
        "hora-priority-papers/sources/",
        "hora-algebra/",
        "exploring-math/",
        "generalized-star-height/",
        # Withdrawn from version control by SLIDE-WITHDRAW-01.
        "site/index.html",
    }
    # A path that a sentence describes as *gone* is not a broken link, it is a
    # record. Forcing those lines to be deleted would trade a true historical
    # statement for a green check, which is the trade the previous gates kept
    # accidentally offering; the exemption is narrow and names the verbs.
    historical = re.compile(
        r"\bmoved\b|\bformerly\b|\brenamed\b|\bsuperseded\b|\bexternal\b|\bdeleted\b",
        re.IGNORECASE,
    )
    for path in [LEDGER, ROOT / "PROOF_OBLIGATIONS.md", ROOT / "RESULTS.md"]:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            if historical.search(line):
                continue
            for cited in cited_path.findall(line):
                if any(cited.startswith(prefix) for prefix in known_absent):
                    continue
                if "." in cited.split("/", 1)[0]:
                    continue  # a hostname, not a repository path
                if not (ROOT / cited).exists():
                    errors.append(f"{path.name}:{number}: cited path does not exist: {cited}")

    # The status vocabulary is defined in one place and paraphrased in several.
    # On 2026-07-25 `README.md` listed seven labels and omitted `EMPIRICAL` — the
    # one the incident had just created — so the document that a reader meets
    # first had no word for the distinction the whole repository turns on.
    for path in [ROOT / "README.md", ROOT / "AGENTS.md"]:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            named = {label for label in VALID if label in line}
            if len(named) >= 3 and "EMPIRICAL" not in named:
                errors.append(
                    f"{path.name}:{number}: this line enumerates status labels "
                    f"({', '.join(sorted(named))}) but omits EMPIRICAL, which is the "
                    "one that distinguishes a decided claim from a sampled one."
                )

    # Section numbers must be unique. Two branches merged on 2026-07-25 each added
    # a "5.14" and a "5.15" to RESULTS.md; git merged both cleanly because they
    # touched different regions, and the document then had two of each — with the
    # cross-references from the ledger pointing at whichever one the reader found
    # first. Concurrent section-numbering collisions are the normal failure mode
    # here, so they get a check rather than a convention.
    heading = re.compile(r"^#{2,4}\s+(\d+(?:\.\d+)*)\s")
    for path in (ROOT / "RESULTS.md",):
        numbers: dict[str, int] = {}
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            match = heading.match(line)
            if not match:
                continue
            section = match.group(1)
            if section in numbers:
                errors.append(
                    f"{path.name}:{number}: section {section} is already used at "
                    f"line {numbers[section]}. Renumber one of them, and repoint the "
                    "§-references that meant it."
                )
            numbers[section] = number

    if errors:
        print("Claims lint failed:", file=sys.stderr)
        for error in errors:
            print(f"- {error}", file=sys.stderr)
        return 1
    print(f"Claims lint passed: {len(rows)} ledger rows checked")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
