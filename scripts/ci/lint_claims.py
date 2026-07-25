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
#: prose. Migrating one means deleting its line, which is a diff a reviewer can
#: see.
PENDING = ROOT / "data" / "verdicts" / "PENDING.md"
#: The baseline, frozen on 2026-07-25. `PENDING.md` may only ever be a subset of
#: this. An adversarial review pointed out that the first version checked only
#: for *stale* entries, so adding a new unbacked `COMPUTED` row and a matching
#: `PENDING.md` line in the same commit passed --- "may shrink and never grow"
#: was a request to the reviewer, not a constraint on the program. Freezing the
#: set here is what makes it a ratchet: a new id cannot be grandfathered at all,
#: with or without a reason, because the reason would have to be added to this
#: line and that is a diff nobody can write by accident.
GRANDFATHERED = frozenset({
    "A4-STD-01", "A4-STD-02", "F20-BASECODE-01", "F20-COH-SEP-01",
    "F20-FULL-OBS-01", "F20-MONO-FRONT-01", "F20-STD-01", "FRONTIER-ORD20-01",
    "LAAB-04-01", "SEARCH-CAL-01", "SEARCH-CAL-02", "SFA-L2-MEASURE-01",
    "SMALL-NONAB-31-01", "THOMAS-D2-02", "TRANSD-LADDER-01", "WEIS-L2-GSH-01",
    "WEIS-L2-M2-01", "WEIS-L2-M3-01", "WEIS-L2-NOTFN-01", "WEIS-L2-RSH-01",
})
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
# 2026-07-26, from an adversarial review: matching only the upper-case labels let
# `A4-FULL-01 has been proved for every word.` through. Retraction 1 was not a
# wrong label, it was a right label with a verb that outran it, so the verbs are
# checked too. `CITED` stays case-sensitive: lower-case "cited" is ordinary prose
# in this repository ("the cited path"), while "proved" about an EMPIRICAL row is
# not ordinary anything.
STRONGER_VERB = re.compile(
    r"\bproved\b|\bproven\b|\bestablishe[sd]\b|\bsettle[sd]\b|\bresolved\b"
    r"|\bcomputed\b|\bdecided\b|\bclosed\b"
    r"|決着|解決済|解決した|確定した|確定済|落ちた",
    re.IGNORECASE,
)
#: A verb inside a negation is the opposite claim, and flagging it would train
#: authors to describe an EMPIRICAL row less precisely than they can. Round two
#: of the adversarial review flagged `A4-FULL-01 has not been proved.` and
#: `A4-FULL-01 remains open and is not resolved.` as false positives of the
#: widened verb list; both are exactly what an author *should* write.
NEGATION = re.compile(
    r"\bnot\b|\bnever\b|\bcannot\b|\bfails? to\b|\bno\b|\bwithout\b"
    r"|ていない|でない|されない|未|ではない",
    re.IGNORECASE,
)


def outranking_label(unit: str) -> str | None:
    """The label or verb in `unit` that claims more than EMPIRICAL, if any.

    Returns the matched text so the diagnostic can quote it. Round two of the
    adversarial review found the caller doing `STRONGER.search(unit).group(0)`
    unconditionally, which raised `AttributeError` whenever only a verb matched:
    the gate refused the passage by crashing rather than by reporting, so the
    author saw a traceback instead of the sentence to fix.
    """
    label = STRONGER.search(unit)
    if label:
        return label.group(0)
    verb = STRONGER_VERB.search(unit)
    if verb and not NEGATION.search(unit[max(0, verb.start() - 40):verb.start()]):
        return verb.group(0)
    return None


WITHDRAWAL = re.compile(r"withdraw|retract|撤回|降格|previously (read|claimed)", re.IGNORECASE)
#: A retraction *quotes* the wording it withdraws. 2026-07-26, from an
#: adversarial review: the verb alone used to be enough, so
#: `We retract the caveat: order ≤ 12 is settled.` asserted the false claim in
#: the author's own voice and the word "retract" waved it through. Every real
#: retraction in this repository -- `RETRACTIONS.md`, every corrected note --
#: already quotes, so requiring it costs nothing and closes the hole.
QUOTED_SPAN = re.compile(
    r"\"[^\"\n]*\"|“[^”\n]*”|「[^」\n]*」|『[^』\n]*』|~~[^~\n]*~~"
)
#: Clause boundaries for the cited-path check. Deliberately not a bare "." --
#: that is inside every filename the check is meant to protect.
CLAUSE_SPLIT = re.compile(r"(?:;|；|。|—|–|--|\n|\.(?=\s))\s*")
#: A path a clause describes as *gone* is a record, not a broken link.
#: What makes a citation a record rather than a broken link. Bare "moved" and
#: bare "renamed" are deliberately NOT here. Round two of the adversarial review
#: walked a dead path through on `The evidence moved to
#: \`notes/does_not_exist.md\`.`, where the verb is about the path but names it
#: as the *destination* -- which is the one case where the path must exist. Every
#: marker below says the path is gone, not merely that something happened to it.
HISTORICAL = re.compile(
    r"\bfrom\b|\bformer(?:ly)?\b|\bdeleted\b|\bremoved\b|\bwithdrawn\b"
    r"|\bsuperseded\b|\bexternal\b|\bout of\b|\brenamed away\b"
    r"|no longer exists?|\bused to (?:be|live|sit)\b",
    re.IGNORECASE,
)


def historically_absent(clause: str) -> bool:
    """True when this clause says the paths in it are gone.

    Clause-scoped rather than line-scoped (2026-07-25): one unrelated verb used
    to exempt every path on the line. Within the clause the marker may sit on
    either side of the path, because English puts it on either side -- "moved
    from `X`" and "the former locations `X`, `Y` were deleted" are the same
    record. What carries the weight is the marker set, not the position.
    """
    return HISTORICAL.search(clause) is not None


def withdrawal_exempt(line: str, phrase: str = "") -> bool:
    """True when this line withdraws `phrase` rather than asserting it.

    Round two of the adversarial review: requiring *a* quotation mark somewhere
    on the line was not enough, because the quotation did not have to be around
    anything in particular. `We retract 「typographical note」: order ≤ 12 is
    settled.` satisfied it while asserting the false claim in the clear. The
    quoted span must now actually contain the phrase being withdrawn.
    """
    if not WITHDRAWAL.search(line):
        return False
    if not phrase:
        return bool(QUOTED_SPAN.search(line))
    lowered = line.lower()
    target = phrase.lower()
    return any(
        target in lowered[span.start():span.end()]
        for span in QUOTED_SPAN.finditer(line)
    )


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
    stale: set[str] = set()
    for unit in label_units(text):
        if "EMPIRICAL" in unit:
            continue
        cited = {token for token in CLAIM_ID.findall(unit) if token in empirical}
        if cited and outranking_label(unit):
            stale |= cited
    return stale


def outranking_unit_label(text: str) -> str:
    """The first outranking label or verb in any unit of `text`, for the message."""
    for unit in label_units(text):
        if "EMPIRICAL" in unit:
            continue
        found = outranking_label(unit)
        if found:
            return found
    return "a stronger label"


def label_units(text: str) -> list[str]:
    """The units a single label claim can span.

    2026-07-26, from an adversarial review. The paragraph was the wrong unit for
    a markdown table: the whole table is one block, so a correct `EMPIRICAL` in
    any row exempted a false `COMPUTED` in every other row -- and `PROGRESS.md`,
    the document that made this check matter, is mostly tables. A table row is
    therefore its own unit. Contiguous non-table lines stay joined, because that
    is the case the paragraph rule was introduced for: prose wraps wherever it
    wants and the id and its label routinely land on different lines.
    """
    units: list[str] = []
    prose: list[str] = []
    for line in text.splitlines():
        if line.lstrip().startswith("|") and UNESCAPED_PIPE.search(line):
            if prose:
                units.append("\n".join(prose))
                prose = []
            units.append(line)
        else:
            prose.append(line)
    if prose:
        units.append("\n".join(prose))
    return units


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


#: A repository path cited in backticks, e.g. `notes/weis_2011_primary_audit.md`.
CITED_PATH = re.compile(r"`((?:[\w.-]+/)+[\w.-]+\.\w+)`")


def dead_paths(line: str, cited_path, known_absent) -> list[str]:
    """Repository paths this line cites that do not exist and are not recorded as gone.

    Extracted 2026-07-26 for the same reason as `prose_errors`: the tests were
    asserting on the clause splitter rather than on the check built out of it,
    so a change that kept the splitter correct and the check wrong would have
    stayed green.
    """
    missing: list[str] = []
    for clause in CLAUSE_SPLIT.split(line):
        if historically_absent(clause):
            continue
        for cited in cited_path.findall(clause):
            if any(cited.startswith(prefix) for prefix in known_absent):
                continue
            if "." in cited.split("/", 1)[0]:
                continue  # a hostname, not a repository path
            if not (ROOT / cited).exists():
                missing.append(cited)
    return missing


_A4 = (
    "the A_4 full-alphabet result is EMPIRICAL (A4-FULL-01): its reconstruction step "
    "is checked only to length 4 plus random words"
)
FORBIDDEN = {
    "A5 is the first unresolved": "A_5 is not the first unresolved group-order case",
    "A_5 is the first unresolved": "A_5 is not the first unresolved group-order case",
    "search proves": "bounded search is not a mathematical lower bound",
    "obviously height": "language height requires minimization over expressions",
    # Vocabulary bound to status (2026-07-25 audit). The verb must not outrun the
    # label; these five sentences all did.
    "order ≤ 12 is settled": _A4,
    "barrier moved from order 12 to order 20": _A4,
    "位数 ≤ 12 の全群が決着": _A4,
    "障壁が位数 12 から位数 20 に移動": _A4,
    "A4 は反例候補から完全に外れた": _A4,
}


def prose_errors(paths, empirical: set[str]) -> list[str]:
    """Every prose complaint about `paths`, in the order a reader meets them.

    Extracted from `main()` on 2026-07-26 so the regression tests can drive the
    gate itself on their own fixtures. Round two of the adversarial review found
    the previous tests asserting on predicates while the gate around them
    crashed, and one asserting on the *source text* of this module rather than
    on its behaviour. A test that cannot run the gate cannot tell you the gate
    works.
    """
    errors: list[str] = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        for number, line in enumerate(text.splitlines(), start=1):
            for phrase, explanation in FORBIDDEN.items():
                if phrase.lower() in line.lower() and not withdrawal_exempt(line, phrase):
                    errors.append(
                        f"{path.name}:{number}: forbidden phrase {phrase!r}: {explanation}"
                    )
        # No withdrawal exemption on the stale check, deliberately: a passage
        # that withdraws a stronger label has to name the label that replaced it,
        # and naming `EMPIRICAL` is already the way out.
        for number, block in paragraphs(text):
            stale = stale_labels(block, empirical)
            if stale:
                errors.append(
                    f"{path.name}:{number}: {', '.join(sorted(stale))} is EMPIRICAL but this "
                    f"paragraph labels it {outranking_unit_label(block)}. Say EMPIRICAL here, "
                    "or stop attaching a status to it."
                )
    return errors


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
        ROOT / "PROGRESS.md",
        ROOT / "README.md",
        ROOT / "docs" / "SURVEY.md",
        ROOT / "docs" / "SCENARIOS.md",
        ROOT / "docs" / "SUGGESTIONS.md",
        ROOT / "docs" / "ROADMAP.md",
        ROOT / "RESULTS.md",
        # Added 2026-07-25. `notes/` holds the derivations every COMPUTED row
        # points at, and it was outside this check entirely: the Conway note
        # still called `A4-FULL-01` COMPUTED in two places, three days after the
        # completeness audit demoted it. The gate that exists to stop exactly
        # that was not looking at the directory where the mathematics is
        # written. Globbed rather than listed so a new note is covered on
        # arrival instead of when someone remembers to add it.
        # rglob, not glob (2026-07-26): a non-recursive pattern meant a false
        # claim parked in `notes/archive/` was simply outside the gate.
        *sorted((ROOT / "notes").rglob("*.md")),
    ]
    errors.extend(prose_errors(prose_files, empirical))

    # The gate the prose checks above could not be. Everything before this point
    # reads what an author wrote about a computation; this reads what the
    # computation reported. `tools/verdict.py` explains why the distinction had
    # to become structural — the short version is `THOMAS-D2-02`, whose evidence
    # cell was true in every sentence and whose certifying program traversed a
    # finite object that had nothing to do with the claim.
    # A verdict file that no script in this repository writes is not evidence.
    # `ceilings()` now recomputes rather than trusting the recorded block, so a
    # forged file cannot claim a ceiling it did not earn -- but an *orphan* file
    # could still carry real-looking checks that nothing regenerates, which is
    # the same rot the research scripts had before CI re-ran them.
    producers = {"completeness_upgrade"}
    for path in sorted((ROOT / "data" / "verdicts").glob("*.json")):
        if path.stem not in producers:
            errors.append(
                f"data/verdicts/{path.name}: no script in scripts/ci/ produces this "
                "verdict, so nothing regenerates or refutes it. Add the producer to "
                "`producers` in this file and to scripts/check.sh, or delete the file."
            )

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
    added = sorted(pending - GRANDFATHERED)
    if added:
        errors.append(
            f"{PENDING.name} lists {', '.join(added)}, which is not in the frozen "
            "2026-07-25 baseline. A row cannot be grandfathered after the fact: back "
            "it with a verdict, or give it a status the evidence supports."
        )

    # Every path the registers cite must exist. Nothing checked this before, and
    # the 2026-07-25 restructure moved 59 files and rewrote 278 citations — a
    # silent typo in any one of them turns a piece of evidence into a dead end
    # that still reads like provenance.
    cited_path = CITED_PATH
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
    historical = HISTORICAL
    # 2026-07-26, from an adversarial review: applied to the whole line, one
    # unrelated "moved" exempted every path on it, so
    # `This result moved the frontier; its evidence is notes/does_not_exist.md.`
    # hid a dead citation behind a verb about something else. The exemption is
    # now per clause. The split deliberately does not break on a bare "." --
    # that is inside every filename it is meant to protect.
    for path in [LEDGER, ROOT / "PROOF_OBLIGATIONS.md", ROOT / "RESULTS.md"]:
        for number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), start=1):
            for cited in dead_paths(line, cited_path, known_absent):
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
