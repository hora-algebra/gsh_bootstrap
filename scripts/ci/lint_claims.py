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
    r"\bnot\b|n't\b|\bnever\b|\bcannot\b|\bfail(?:s|ed)? to\b|\bno\b|\bwithout\b"
    r"|ていない|でない|されない|未|ではない|わけではない|とは限らない",
    re.IGNORECASE,
)
#: Japanese puts its negation after the verb, so a rule that only looks
#: backwards reads 「解決したわけではない」 as the claim it denies.
TRAILING_NEGATION = re.compile(
    r"\A[^。；;]{0,24}?(?:わけではない|ではない|ていない|とは限らない|ない)",
)
#: What may stand between a negation and the verb it denies: auxiliaries, the
#: copula, punctuation. Anything else is another predicate, and a negation about
#: another predicate is not about this verb.
#:
#: Japanese single-character particles are deliberately absent. Allowing them let
#: `ものの` through as も + の + の, three permitted tokens in a row -- and
#: Japanese puts its negation after the verb anyway, where `TRAILING_NEGATION`
#: reads it.
#: Auxiliaries and degree words -- what an English negation puts between itself
#: and its verb. Articles and `it` are deliberately absent: they begin a
#: complement or a new clause, which is how `is not likely *it has been*
#: proved` and `is not *an* anomaly` bridged a negation about something else to
#: the verb.
_AUX = (
    r"\b(?:been|be|being|to|yet|is|was|were|are|am|have|has|had|so|far"
    r"|either|any|ever|once)\b"
)
#: An adverb, minus the conjunctive ones (they join clauses) and
#: `only|merely|simply` (they make the negation correlative).
_ADVERB = (
    r"(?!(?:nevertheless|however|still|nonetheless|therefore|thus|hence"
    r"|moreover|instead|regardless|only|merely|simply)\b)\w+ly\b"
)


#: **The residue, measured rather than assumed (2026-07-26).** A stop-time review
#: said free ordering lets a negation about another clause bridge to the verb.
#: Everything probed that passes is either a legitimate negation -- `has not
#: ever so far been proved`, `is not to be so far proved`, `has not been, so
#: far, actually proved` -- or ungrammatical: `was not ever so, was proved`,
#: `has not any so far been proved`. A finite verb in the permitted set can in
#: principle start a second clause, and in practice doing so takes a sentence
#: nobody writes.
#:
#: The probes are in `test_the_probes_behind_the_documented_residue`, which
#: asserts the two halves that can be asserted: the grammatical negations keep
#: passing, and the constructions that should be caught keep being caught. The
#: ungrammatical ones are listed there and deliberately not asserted. An earlier
#: version of this comment said "fifteen constructions"; the sweep ran in three
#: batches and the count did not survive being checked, so it is gone rather
#: than corrected -- what matters is which sentences, and they are in the test.
#:
#: Not fixed, and not called fixed. This rule has been corrected four times
#: tonight and every correction rejected prose an honest author writes; a fifth
#: aimed at inputs that are not sentences is a bad trade. The thirty-three-case
#: matrix in `AdversarialBypassTests` is the specification, and it is what to
#: re-run before changing any of this.
NEGATION_GAP = re.compile(
    # Auxiliaries and adverbs, in any order: "has not *been formally* proved"
    # and "has not *formally been* proved" are the same sentence, and requiring
    # auxiliaries first rejected the second. What keeps a complement out is the
    # word list, not the order -- articles and `it` are not on it.
    r"[\s,、`*_]*(?:(?:" + _AUX + r"|" + _ADVERB + r")[\s,、`*_]*)*",
    re.IGNORECASE,
)


def negated(unit: str, verb_start: int) -> bool:
    """True when a negation governs the verb at `verb_start`.

    Scoped to the clause the verb is in, so that a negation about something else
    cannot license an overstatement about this row.
    """
    before = unit[:verb_start]
    for hit in NEGATION.finditer(before):
        # Adjacency, not proximity: between a negation and the verb it denies
        # there is nothing but auxiliaries. Round nine walked eight adversative
        # forms past a conjunction list -- にもかかわらず, とはいえ, 一方で,
        # nevertheless, however -- and extending the list is the treadmill every
        # reopened rule in this file has been. What survives instead is the
        # relation: `A4-FULL-01 has not been proved` has only "been" in the gap,
        # `not trivial nevertheless it has been proved` has a predicate in it.
        if NEGATION_GAP.fullmatch(before[hit.end():]):
            return True
    return TRAILING_NEGATION.search(unit[verb_start:]) is not None


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
    for verb in STRONGER_VERB.finditer(unit):
        if not negated(unit, verb.start()):
            return verb.group(0)
    return None


#: Strong only. `previously read` used to count, which let a paragraph opening
#: "Previously read the appendix." license a live overstatement after it. A
#: retraction says it is retracting.
WITHDRAWAL = re.compile(r"withdraw|retract|撤回|降格", re.IGNORECASE)
#: A retraction *quotes* the wording it withdraws. 2026-07-26, from an
#: adversarial review: the verb alone used to be enough, so
#: `We retract the caveat: order ≤ 12 is settled.` asserted the false claim in
#: the author's own voice and the word "retract" waved it through. Every real
#: retraction in this repository -- `RETRACTIONS.md`, every corrected note --
#: already quotes, so requiring it costs nothing and closes the hole.
QUOTED_SPAN = re.compile(
    r"\"[^\"\n]*\"|'[^'\n]*'|‘[^’\n]*’|“[^”\n]*”|「[^」\n]*」|『[^』\n]*』"
)
#: `~~strike~~` is deliberately not a quotation: round four asserted a live claim
#: as `~~order ≤ 12 is settled~~ is in fact true.`
INLINE_CODE = re.compile(r"`[^`\n]*`")
#: Quoting a claim is mentioning it. Saying the quotation is correct is asserting
#: it, and round four did exactly that inside a nested quotation.
AFFIRMING = re.compile(
    r"\bis (?:true|correct|right|accurate|still (?:true|correct))\b|\bin fact\b"
    r"|\bremains? the (?:result|conclusion|case)\b|\bstill stands\b"
    r"|は正しい|実際に(?:は)?正しい|は真である",
    re.IGNORECASE,
)


def masked_for_quoting(line: str) -> str:
    """`line` with inline-code spans blanked, so their quote characters cannot pair.

    Round four hid a live claim between two backticked quote marks:
    ``We retract a typo. `"` order ≤ 12 is settled `"` is true.``
    """
    return INLINE_CODE.sub(lambda m: " " * (m.end() - m.start()), line)
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


#: How far from a path a marker may sit and still be about that path. Round
#: three walked two clause-wide exemptions through: `Evidence from the
#: experiment is recorded at \`notes/does_not_exist.md\`.`, where an unrelated
#: "from" covered the path, and `The former path \`X\` was deleted and its
#: replacement is \`Y\`.`, where a marker that correctly described `X` also
#: covered `Y` -- the one path in the sentence that must exist. Adjacency is
#: what distinguishes "this path is gone" from "a path is mentioned near a word".
#: Between a gone marker and the path it excuses, only these may stand. A fixed
#: character window was wrong in both directions: round four exempted a live
#: path with `A former result says \`X\` remains current.` (the marker modifies
#: "result", not the path) while rejecting records whose marker sat one clause
#: away. Adjacency is grammatical, not metric -- nothing but punctuation and
#: auxiliaries may come between.
MARKER_GAP = re.compile(
    r"\A[\s,:;`()\-–—]*"
    # ...plus the nouns a marker naturally modifies: "the former *locations*
    # `X`, `Y` were deleted" is the record, not a way around it. "A former
    # *result* says `X` remains current" is not on this list, and is caught.
    r"(?:(?:was|were|is|are|has|have|had|been|it|that|which|now|since|and|from|into"
    r"|locations?|paths?|files?|modules?|declarations?"
    r"|lived?|lives|sat|sits|located|found|kept|held|at|in|under)"
    r"[\s,:;`()\-–—]*)*\Z",
    re.IGNORECASE,
)


#: A clause that says the path is still in use is not a record of its absence,
#: whatever marker it also carries. The noun list in `MARKER_GAP` let
#: `The former files \`X\` is current.` and `The former modules \`X\` remains in
#: use.` be excused by a word about the files, while the sentence said the
#: opposite of gone.
LIVE_CLAIM = re.compile(
    r"\bis current\b|\bremains?\b|\bstill\b|\bin use\b|\bcurrently\b"
    r"|\bthe current\b|\bis available\b|\bprovides?\b|\bcontains?\b"
    r"|\bis here\b|現行|使われている|参照せよ",
    re.IGNORECASE,
)


def historically_absent(clause: str, start: int, end: int) -> bool:
    """True when a gone marker is grammatically attached to this path."""
    if LIVE_CLAIM.search(clause):
        return False
    for marker in HISTORICAL.finditer(clause):
        if marker.end() <= start and MARKER_GAP.fullmatch(clause[marker.end():start]):
            return True
        if marker.start() >= end and MARKER_GAP.fullmatch(clause[end:marker.start()]):
            return True
    return False


#: A passage that reports what was once asserted, rather than asserting it. The
#: stale-label check has no general withdrawal escape -- `A4-FULL-01 is PROVED;
#: its earlier caveat was withdrawn.` must not pass -- but `RETRACTIONS.md`
#: needs to be able to say what the withdrawn claim *was*, verb and all, or the
#: retraction cannot be written down. These markers are about past text
#: specifically, which "was withdrawn" is not.
REPORTED = re.compile(
    r"what was asserted|previously (?:read|claimed|said)"
    # 「…と書いていた」 with or without a following particle, and however long
    # the quotation between 以前 and it runs. The first version required 「が」
    # and a quotation under thirty characters, so two genuine retraction records
    # -- one in `RESULTS.md`, one in a note -- were rejected for quoting the
    # wording they withdraw at its actual length.
    r"|と書いてい(?:た|ました)|と述べていた|以前[^\n]{0,120}?書いて|かつて[^\n]{0,120}?書いて",
    re.IGNORECASE,
)


#: Markdown allows at most three leading spaces before a fence; four makes it an
#: indented code block, and treating it as a fence let round five disable the
#: gate for the prose between two indented backtick lines. The kind and length
#: are captured because a fence closes only with the same character, at least as
#: long -- `\`\`\`` then `~~~`, or ```` then ``` , used to count as closed.
FENCE = re.compile(r"^(?: {0,3})(?P<kind>`{3,}|~{3,})\s*(?P<info>.*)$")


def unclosed_fence(text: str) -> bool:
    """True when a code fence is opened and never closed.

    Fencing the prose checks made an unclosed fence a silent exemption for
    everything after it -- the loudest possible way to disable a gate, written
    as three backticks. It is an error now rather than a quiet pass.
    """
    opener: str | None = None
    for line in text.splitlines():
        match = FENCE.match(BLOCKQUOTE.sub("", line))
        if not match:
            continue
        kind = match.group("kind")
        if opener is None:
            opener = kind
        elif kind[0] == opener[0] and len(kind) >= len(opener) and not match.group("info"):
            opener = None
    return opener is not None


def without_fences(text: str) -> str:
    """`text` with fenced-code lines blanked, keeping the line numbering.

    Everything inside a fence is an example. Reading its `#` lines as headings
    split a retraction away from its own record, and reading its prose as prose
    would flag sentences nobody asserted.
    """
    kept: list[str] = []
    opener: str | None = None
    for line in text.splitlines():
        # A blockquoted example is still an example.
        match = FENCE.match(BLOCKQUOTE.sub("", line))
        if match:
            kind = match.group("kind")
            if opener is None:
                opener = kind
                kept.append("")
                continue
            # A closing fence carries no info string and must match the opener's
            # character and be at least as long.
            if kind[0] == opener[0] and len(kind) >= len(opener) and not match.group("info"):
                opener = None
                kept.append("")
                continue
        kept.append("" if opener is not None else line)
    return "\n".join(kept)


def sections(text: str) -> dict[int, str]:
    """Line number -> its markdown section.

    Used only to ask whether a `REPORTED` paragraph sits inside a retraction
    record. A retraction is a section -- heading, "**Withdrawn.**", then the
    paragraphs that say what was asserted -- so the marker legitimately lives in
    a different paragraph from the report. The forbidden-phrase exemption uses
    the much tighter `withdrawal_context` instead, because it licenses one
    specific sentence rather than classifying a record.
    """
    lines = text.splitlines()
    bounds = [0] + [i for i, line in enumerate(lines) if line.startswith("#")] + [len(lines)]
    owner: dict[int, str] = {}
    for start, stop in zip(bounds, bounds[1:]):
        body = "\n".join(lines[start:stop])
        for number in range(start + 1, stop + 1):
            owner[number] = body
    return owner


def withdrawal_context(text: str) -> dict[int, str]:
    """Line number -> the text allowed to establish that this line withdraws.

    The paragraph the line is in, plus -- when that paragraph is a heading --
    the paragraph after it, because a retraction's heading quotes the withdrawn
    wording while the verb "Withdrawn" opens the body below. `RETRACTIONS.md`
    §19 is exactly that shape.

    Scoped to the paragraph rather than the section (round four): one "Withdrawn
    elsewhere." anywhere in a long section used to license the forbidden phrases
    in all of it, and a file with no headings was one section from top to
    bottom.
    """
    blocks = paragraphs(text)
    following = {
        start: blocks[index + 1][1] if index + 1 < len(blocks) else ""
        for index, (start, _) in enumerate(blocks)
    }
    owner: dict[int, str] = {}
    for start, block in blocks:
        body = block
        if block.lstrip().startswith("#"):
            body = block + "\n" + following[start]
        for offset in range(len(block.splitlines())):
            owner[start + offset] = body
    return owner


def withdrawal_exempt(line: str, phrase: str = "", context: str = "") -> bool:
    """True when every occurrence of `phrase` on this line is being withdrawn.

    Two rounds of adversarial review narrowed this. Requiring *a* quotation mark
    somewhere on the line let `We retract 「typographical note」: order ≤ 12 is
    settled.` through, so the quoted span had to contain the phrase. Requiring
    *a* quoted occurrence then let

        We retract "order ≤ 12 is settled"; order ≤ 12 is settled.

    through, because quoting the phrase once licensed asserting it again beside
    the quotation -- in prose, or in the next cell of the same table row. Every
    occurrence has to be inside a quotation now. One left in the clear is an
    assertion, whatever the rest of the line says about it.
    """
    masked = masked_for_quoting(line)
    if AFFIRMING.search(masked):
        return False
    if not WITHDRAWAL.search(context or line):
        return False
    if not phrase:
        return bool(QUOTED_SPAN.search(masked))
    quoted = [(span.start(), span.end()) for span in QUOTED_SPAN.finditer(masked)]
    lowered, target = line.lower(), phrase.lower()
    start = lowered.find(target)
    seen = False
    while start != -1:
        seen = True
        end = start + len(target)
        if not any(qs <= start and end <= qe for qs, qe in quoted):
            return False
        start = lowered.find(target, end)
    return seen


# A cell boundary is a pipe that is not escaped as `\|`. Markdown tables carry
# literal pipes (e.g. `\|w\|_a`) only in escaped form, so splitting on a bare
# "|" silently shreds those rows into the wrong number of cells.
UNESCAPED_PIPE = re.compile(r"(?<!\\)\|")
#: Markdown quoting a table still shows a table.
BLOCKQUOTE = re.compile(r"^\s*(?:>\s*)+")
#: An HTML table is a table too; each `<tr>` opens a row.
HTML_ROW_OPEN = re.compile(r"<tr\b[^>]*>", re.IGNORECASE)
#: How far a row may run before it stops being a row. A wrapped cell needs
#: several lines -- round five split an id from its verb by wrapping over five
#: -- while an unclosed row that keeps collecting swallows the document. The
#: bound is generous now because the collection also stops at a blank line and
#: at the start of another row, and because a false label no longer needs to
#: share a unit with its id to be caught: `attached` relates them.
ROW_LOOKAHEAD = 12


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
        for mention in CLAIM_ID.finditer(unit):
            if mention.group(0) not in empirical:
                continue
            if attached(unit, mention, EMPIRICAL_LABEL):
                continue
            if attached_label(unit, mention):
                stale.add(mention.group(0))
    return stale


EMPIRICAL_LABEL = re.compile(r"\bEMPIRICAL\b")


def attached(unit: str, mention: "re.Match[str]", pattern: "re.Pattern[str]") -> bool:
    """True when `pattern` matches somewhere with no other claim id in between.

    Both the accusation and the excuse have to belong to the id they are about.
    Neither a unit-wise nor a cell-wise rule does that. Unit-wise let round five
    put `| A4-FULL-01 | COMPUTED | compare: C7C3-FULL-01 is EMPIRICAL |`
    through, and pin a `COMPUTED` about one row onto a bare mention of another
    eight lines down. Cell-wise stops seeing `| A4-FULL-01 | EMPIRICAL |`, where
    the id and its status are in different cells by construction. "Nothing else
    claims it" is the relation both need.
    """
    for found in pattern.finditer(unit):
        if found.start() >= mention.end():
            between = unit[mention.end():found.start()]
        elif found.end() <= mention.start():
            between = unit[found.end():mention.start()]
        else:
            continue
        if not CLAIM_ID.search(between):
            return True
    return False


def attached_label(unit: str, mention: "re.Match[str]") -> bool:
    """True when a label or verb outranking EMPIRICAL belongs to this id."""
    if attached(unit, mention, STRONGER):
        return True
    for verb in STRONGER_VERB.finditer(unit):
        if negated(unit, verb.start()):
            continue
        if attached(unit, mention, re.compile(re.escape(verb.group(0)))):
            return True
    return False


#: Where one label claim stops and the next begins, inside a unit. Deliberately
#: NOT a newline: the paragraph rule exists because prose wraps between an id
#: and its label. Round five put a true `EMPIRICAL` about one row in the same
#: unit as a false `COMPUTED` about another -- `A4-FULL-01 has been proved.
#: Separately, C7C3-FULL-01 is EMPIRICAL.` -- and the second excused the first.
LABEL_CLAUSE = re.compile(r"[;；。]|\.(?=\s)|(?<!\\)\|")


def outranking_unit_label(text: str) -> str:
    """The first outranking label or verb in any clause of `text`, for the message."""
    for unit in label_units(text):
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
    lines = text.splitlines()
    units: list[str] = []
    prose: list[str] = []

    def flush() -> None:
        if prose:
            units.append("\n".join(prose))
            prose.clear()

    def bare(index: int) -> str:
        return BLOCKQUOTE.sub("", lines[index]).strip()

    index = 0
    while index < len(lines):
        here = bare(index)
        if here.startswith("|") and UNESCAPED_PIPE.search(here):
            flush()
            # A cell may wrap onto the next line, and then the id and its verb
            # are in one row but on two lines. Exactly one line of lookahead:
            # round four fed an unclosed row followed by ordinary prose and had
            # the rest of the document absorbed into the row, where a later
            # unrelated EMPIRICAL excused the false label above it.
            if not here.endswith("|") or here == "|":
                closing = None
                for ahead in range(index + 1, min(index + 1 + ROW_LOOKAHEAD, len(lines))):
                    nxt = bare(ahead)
                    if not nxt or nxt.startswith("|"):
                        break
                    if nxt.endswith("|"):
                        closing = ahead
                        break
                if closing is not None:
                    units.append("\n".join(lines[index:closing + 1]))
                    index = closing + 1
                    continue
            units.append(lines[index])
            index += 1
            continue
        if HTML_ROW_OPEN.search(here):
            flush()
            # Collect to `</tr>`; splitting at every `<tr>` put an id and its
            # label in different units whenever the row spanned lines.
            closing = None
            for ahead in range(index, min(index + 1 + ROW_LOOKAHEAD, len(lines))):
                if "</tr>" in bare(ahead).lower():
                    closing = ahead
                    break
            stop = closing if closing is not None else index
            units.append("\n".join(lines[index:stop + 1]))
            index = stop + 1
            continue
        prose.append(lines[index])
        index += 1
    flush()
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
CITED_PATH = re.compile(r"`((?:[\w.-]+/)+[\w.-]+\.\w+)(?:#[\w.-]+)?`")


def dead_paths(line: str, cited_path, known_absent) -> list[str]:
    """Repository paths this line cites that do not exist and are not recorded as gone.

    Extracted 2026-07-26 for the same reason as `prose_errors`: the tests were
    asserting on the clause splitter rather than on the check built out of it,
    so a change that kept the splitter correct and the check wrong would have
    stayed green.
    """
    missing: list[str] = []
    for clause in CLAUSE_SPLIT.split(line):
        for match in cited_path.finditer(clause):
            cited = match.group(1)
            if "." in cited.split("/", 1)[0]:
                continue  # a hostname, not a repository path
            if (ROOT / cited).exists():
                continue
            # `known_absent` records paths this repository removed on purpose.
            # It used to skip everything, including the check that the sentence
            # is not calling the path current: round five got
            # `the current deck is \`site/index.html\`.` past it.
            # A prefix match is not a path match: round seven excused
            # `site/index.html.bak` because it starts with a name on the list.
            if any(cited == prefix or cited.startswith(prefix.rstrip("/") + "/")
                   for prefix in known_absent):
                if not LIVE_CLAIM.search(clause):
                    continue
            elif historically_absent(clause, match.start(), match.end()):
                continue
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


#: `A4-FULL-01 (`COMPUTED`)` -- an id and a status in parentheses, nothing
#: between them. Deliberately one fixed notation rather than "a status word near
#: an id": the first version of this check matched the latter and reported
#: `this row must never be upgraded to `PROVED` without upgrading A4-FULL-01`,
#: which is a hypothetical about a different row. Guessing what a sentence means
#: is what the rest of this file has to do; here both sides are ledger fields,
#: so the check can be a comparison instead, and it is worth restricting the
#: notation to keep it one.
ATTRIBUTED_STATUS = re.compile(
    r"`?(?P<id>[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)+)`?\s*\(\s*`?(?P<status>[A-Z]+)`?\s*\)"
)


#: A row talking about its own status. `A4-ALLLANG-01` said "the ceiling stays
#: `COMPUTED`" in the cell whose status column reads `EMPIRICAL`.
#:
#: Two stop-time reviews narrowed this. Reading the verb -- "stays", "is",
#: "remains" -- to decide whether a sentence was about the present made it a
#: tense-guesser, wrong on "the ceiling was `COMPUTED` before the audit" and on
#: "would be `PROVED` if the sample were replaced". Keying it on the word
#: "ceiling" then made it evadable by writing "upper bound" instead.
#:
#: Asking merely that the row's status appear *somewhere* in the cell was the
#: version after that, and a stop-time review walked through it: in "the ceiling
#: stays `COMPUTED`; `Y-TWO` is `EMPIRICAL`" the required word is present, as a
#: remark about a different row.
#:
#: So the cell has to carry one fixed sentence. Set membership cannot say whose
#: status a word is; a sentence with the row's own status in it can only be
#: written on purpose, and is what a reader looks for.
#:
#: **What this still does not catch, stated so nobody over-trusts it.** A cell
#: may carry the sentence and go on to contradict it -- "This row is
#: `EMPIRICAL`. The ceiling stays `COMPUTED`." passes. Deciding that the second
#: sentence is about *this* row needs the thing every reopened rule in this file
#: has tried and failed to do: infer from a word what a sentence means.
#:
#: The version that would close it is mechanical and known: require every status
#: word in an evidence cell to sit inside one of the two fixed notations -- this
#: sentence, or `ID (STATUS)` -- and reject any that does not. Measured on
#: 2026-07-26 that is 57 mentions across 26 of the 86 rows, all of them
#: informative prose today ("downgraded to `EMPIRICAL` by the audit"). Rewriting
#: the normative ledger's prose into a notation is the redesign the seventh
#: adversarial round prescribed for this whole file, and it is a change to make
#: deliberately, not as the fifth narrowing of one check in one night.
OWN_STATUS = "This row is `{status}`."


def evidence_disagreements(rows: list[list[str]]) -> list[str]:
    """Statuses attributed in evidence cells that the ledger contradicts.

    Round seven found `A4-ALLLANG-01` describing its own input as
    `A4-FULL-01 (COMPUTED)` in the same row whose status column reads
    `EMPIRICAL`, and `ORD12-ALL-01` calling the `A_4` base case `COMPUTED`. Both
    survived every prose check, because a ledger cell is not prose the prose
    checks read.
    """
    status = {cells[0]: cells[2] for cells in rows}
    complaints: list[str] = []
    for cells in rows:
        claim_id, evidence = cells[0], cells[3]
        for attribution in ATTRIBUTED_STATUS.finditer(evidence):
            named = attribution.group("id")
            claimed = attribution.group("status")
            recorded = status.get(named)
            if recorded is None or claimed not in VALID or claimed == recorded:
                continue
            complaints.append(
                f"{claim_id}: evidence calls {named} {claimed}, but the ledger "
                f"records it as {recorded}"
            )
        named = {word for word in re.findall(r"[A-Z]{4,}", evidence) if word in VALID}
        if named and OWN_STATUS.format(status=cells[2]) not in evidence:
            complaints.append(
                f"{claim_id}: evidence names {', '.join(sorted(named))}; it must "
                f'also say "{OWN_STATUS.format(status=cells[2])}"'
            )
    return complaints


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
        raw = path.read_text(encoding="utf-8")
        if unclosed_fence(raw):
            errors.append(
                f"{path.name}: unclosed code fence; everything after it would be "
                "exempt from these checks. Close the fence."
            )
        text = without_fences(raw)
        owner = withdrawal_context(text)
        section = sections(text)
        for number, line in enumerate(text.splitlines(), start=1):
            for phrase, explanation in FORBIDDEN.items():
                if phrase.lower() in line.lower() and not withdrawal_exempt(
                    line, phrase, owner.get(number, "")
                ):
                    errors.append(
                        f"{path.name}:{number}: forbidden phrase {phrase!r}: {explanation}"
                    )
        # No withdrawal exemption on the stale check, deliberately: a passage
        # that withdraws a stronger label has to name the label that replaced it,
        # and naming `EMPIRICAL` is already the way out.
        for number, block in paragraphs(text):
            # Reporting a withdrawn assertion is only reporting inside a
            # retraction. Round four laundered a live claim with a bare
            # "Previously read ..." / 「以前は…と書いていた」 opener.
            if REPORTED.search(block) and WITHDRAWAL.search(section.get(number, "")):
                continue
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
        # The retraction file itself, added 2026-07-26. It was outside the gate
        # that its own first entry created, which is the joke this repository
        # keeps failing to stop telling.
        ROOT / "RETRACTIONS.md",
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
    errors.extend(evidence_disagreements(rows))
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
        # Fenced, like the prose checks. A path inside an example is not a
        # citation; flagging it made the gate reject a document for showing what
        # a citation looks like. The prose side was fenced and this side was not,
        # which is the same asymmetry that let the first-build log's paths hide
        # in headings.
        raw = path.read_text(encoding="utf-8")
        if unclosed_fence(raw):
            errors.append(
                f"{path.name}: unclosed code fence; the cited paths after it "
                "would not be checked. Close the fence."
            )
        fenced = without_fences(raw)
        for number, line in enumerate(fenced.splitlines(), start=1):
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
