from __future__ import annotations

import importlib.util
import os
import subprocess
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

_spec = importlib.util.spec_from_file_location(
    "lint_claims", ROOT / "scripts" / "ci" / "lint_claims.py"
)
lint_claims = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(lint_claims)


ROW = (
    "| ESC-01 | Words satisfying \\|w\\|_a ≡ \\|w\\|_b mod 2 form a group language. "
    "| COMPUTED | `legacy/scripts/search.py` step [1] | hora-algebra | 2026-07-25 |"
)


class SplitCellsTests(unittest.TestCase):
    def test_escaped_pipes_stay_inside_their_cell(self) -> None:
        cells = lint_claims.split_cells(ROW)
        self.assertEqual(len(cells), 6)
        self.assertEqual(cells[0], "ESC-01")
        self.assertIn("|w|_a", cells[1])
        self.assertEqual(cells[2], "COMPUTED")
        self.assertEqual(cells[5], "2026-07-25")

    def test_plain_row_is_unchanged(self) -> None:
        cells = lint_claims.split_cells("| A-01 | claim | PROVED | evidence | owner | 2026-07-25 |")
        self.assertEqual(cells, ["A-01", "claim", "PROVED", "evidence", "owner", "2026-07-25"])

    def test_empty_cells_are_preserved(self) -> None:
        cells = lint_claims.split_cells("| A-01 | claim | PROVED | evidence | owner |  |")
        self.assertEqual(len(cells), 6)
        self.assertEqual(cells[5], "")


class ParseRowsTests(unittest.TestCase):
    def test_row_with_escaped_pipes_is_not_skipped(self) -> None:
        text = "| ID | Claim | Status | Evidence | Owner | Review |\n|---|---|---|---|---|---|\n" + ROW
        rows = lint_claims.parse_rows(text)
        self.assertEqual([row[0] for row in rows], ["ESC-01"])

    def test_every_ledger_row_is_parsed(self) -> None:
        """No CLAIMS_LEDGER.md row may be silently dropped by the parser."""
        text = (ROOT / "CLAIMS_LEDGER.md").read_text(encoding="utf-8")
        candidates = [
            line.strip()
            for line in text.splitlines()
            if line.strip().startswith("|") and not line.strip().startswith("|---")
        ]
        # `| ID | ... |` header lines are deliberately skipped; everything else
        # is a claim row and must survive parsing.
        expected = sum(1 for line in candidates if not line.startswith("| ID |"))
        self.assertEqual(len(lint_claims.parse_rows(text)), expected)


class CompletenessGateTests(unittest.TestCase):
    """The 2026-07-25 audit gate, with negative controls.

    A gate that cannot fail is worth nothing — that is precisely the defect
    this gate exists to catch — so each case below asserts a *verdict*, not
    merely that the regexes run.
    """

    SAMPLING = [
        "checked on all words of length <= 16 plus 30,000 random words",
        "exhaustive to bounded length plus random sampling",
        "agreement on all words of length ≤ 12",
        "verified by spot-check on the small cases",
        "bounded-exhaustive-plus-random reconstruction check",
    ]
    COMPLETE = [
        "proved language-equal by complete product reachability (no sampling)",
        "complete enumeration of 593,575 distinct languages",
        "full transition-monoid enumeration, 291 patterns",
        "exact DFA equivalence against the 20-state target",
    ]

    def test_sampling_language_is_detected(self) -> None:
        for text in self.SAMPLING:
            with self.subTest(text=text):
                self.assertIsNotNone(lint_claims.SAMPLING_MARKER.search(text))

    def test_completeness_attestations_are_recognised(self) -> None:
        for text in self.COMPLETE:
            with self.subTest(text=text):
                self.assertIsNotNone(lint_claims.COMPLETENESS_ATTESTATION.search(text))

    def test_bare_exhaustive_is_not_an_attestation(self) -> None:
        """`exhaustive to bounded length` is a sample wearing the word."""
        text = "reconstruction checks exhaustive to bounded length plus random sampling"
        self.assertIsNone(lint_claims.COMPLETENESS_ATTESTATION.search(text))
        self.assertIsNotNone(lint_claims.SAMPLING_MARKER.search(text))

    def test_substep_attestation_does_not_clear_the_row(self) -> None:
        """The `A4-STD-01` shape: an exact sub-step, a sampled conclusion.

        "product-automaton" is deliberately absent from the attestation set, so
        a row cannot pass on the strength of a component its claim does not
        rest on.
        """
        text = ("atoms proved by exhaustive product-automaton search, "
                "end-to-end agreement on all words of length ≤ 16 plus 30k random words")
        self.assertIsNotNone(lint_claims.SAMPLING_MARKER.search(text))
        self.assertIsNone(lint_claims.COMPLETENESS_ATTESTATION.search(text))

    def test_no_sampling_is_not_read_as_sampling(self) -> None:
        """A row that says "no sampling" must not be flagged by its own denial."""
        text = "exact, no sampling, ~3 s"
        self.assertTrue(lint_claims.attests_completeness(text))

    def test_an_attestation_that_scopes_itself_away_does_not_count(self) -> None:
        """The `C7C3-FULL-01` shape: "no sampling in the exhaustive parts".

        A tautology — the exhaustive parts never sample — and it let a row whose
        reconstruction stopped at length 4 sit at COMPUTED. Same family as the
        `A4-STD-01` sub-step loophole: a true statement about a component,
        standing in for the claim.
        """
        for text in (
            "exact where finite, 53 s, no sampling in the exhaustive parts",
            "no sampling for the atoms; end-to-end agreement to length 16",
        ):
            with self.subTest(text=text):
                self.assertFalse(lint_claims.attests_completeness(text))

    def test_the_escape_hatch_is_a_fixed_phrase(self) -> None:
        """`TRANSD-LADDER-01`: proofs carry the row, a bounded run is decoration.

        The gate must not force such a row to choose between a false demotion
        and an invented attestation — but the way out has to be a deliberate
        sentence, not a keyword anyone might type in passing.
        """
        self.assertIn("not load-bearing", lint_claims.NOT_LOAD_BEARING)
        self.assertFalse(lint_claims.attests_completeness(lint_claims.NOT_LOAD_BEARING))


class SectionNumberTests(unittest.TestCase):
    def test_results_section_numbers_are_unique(self) -> None:
        """Two branches each added a 5.14 and a 5.15 on 2026-07-25 and git took both."""
        seen: dict[str, int] = {}
        pattern = __import__("re").compile(r"^#{2,4}\s+(\d+(?:\.\d+)*)\s")
        text = (ROOT / "RESULTS.md").read_text(encoding="utf-8")
        duplicates = []
        for number, line in enumerate(text.splitlines(), start=1):
            match = pattern.match(line)
            if not match:
                continue
            if match.group(1) in seen:
                duplicates.append(f"{match.group(1)} at {seen[match.group(1)]} and {number}")
            seen[match.group(1)] = number
        self.assertEqual(duplicates, [])
        self.assertGreater(len(seen), 10, "no headings matched: the check would be vacuous")

    def test_claim_id_pattern_matches_ledger_ids(self) -> None:
        found = set(lint_claims.CLAIM_ID.findall("depends on A4-FULL-01 and WEIS-L2-M2-01, not on PROVED"))
        self.assertIn("A4-FULL-01", found)
        self.assertIn("WEIS-L2-M2-01", found)

    def test_live_ledger_has_no_computed_row_resting_on_a_sample(self) -> None:
        """The gate's verdict on the real ledger, not on fixtures."""
        text = (ROOT / "CLAIMS_LEDGER.md").read_text(encoding="utf-8")
        offenders = [
            cells[0]
            for cells in lint_claims.parse_rows(text)
            if cells[2] == "COMPUTED"
            and lint_claims.SAMPLING_MARKER.search(cells[3])
            and not lint_claims.COMPLETENESS_ATTESTATION.search(cells[3])
        ]
        self.assertEqual(offenders, [])

    def test_live_ledger_empirical_rows_state_their_sample(self) -> None:
        text = (ROOT / "CLAIMS_LEDGER.md").read_text(encoding="utf-8")
        silent = [
            cells[0]
            for cells in lint_claims.parse_rows(text)
            if cells[2] == "EMPIRICAL" and not lint_claims.SAMPLING_MARKER.search(cells[3])
        ]
        self.assertEqual(silent, [])


class ProsePropagationTests(unittest.TestCase):
    """A demotion must reach the prose, not just the ledger row.

    The forbidden-phrase list cannot do this job: the four surviving
    `RESULTS.md` sentences that still called `A4-ALLLANG-01` COMPUTED after the
    2026-07-25 demotion shared no phrase with each other. What they shared was
    structure, which is what this gate matches.
    """

    flag = staticmethod(lint_claims.stale_labels)

    # Fixed, so these cases test the predicate rather than today's ledger.
    # `FRONTIER-ORD20-01` is deliberately absent: it is COMPUTED — its group
    # theory is exact and the 07-25 correction only re-read this ledger's own
    # statuses — so a passage naming it alongside COMPUTED is correct, and the
    # split-across-lines case below relies on that to isolate `A4-ALLLANG-01`.
    EMPIRICAL = {"A4-FULL-01", "A4-ALLLANG-01", "ORD12-ALL-01", "C7C3-FULL-01"}

    def test_stale_label_on_a_demoted_row_is_caught(self) -> None:
        line = "| 12 | A4 | 本リポジトリで解決済み（`A4-ALLLANG-01`, `COMPUTED`） |"
        self.assertEqual(self.flag(line, self.EMPIRICAL), {"A4-ALLLANG-01"})

    def test_restating_the_demotion_is_allowed(self) -> None:
        line = "`A4-ALLLANG-01` は `EMPIRICAL`（2026-07-25 の完全性監査による降格）"
        self.assertEqual(self.flag(line, self.EMPIRICAL), set())

    def test_a_strong_label_on_an_undemoted_row_is_untouched(self) -> None:
        """`A4-STD-01` really is COMPUTED; the gate must not fire on it."""
        line = "候補 2（A4 word problem）: 反例ではない（`A4-STD-01`、`COMPUTED`）。"
        self.assertEqual(self.flag(line, self.EMPIRICAL), set())

    def test_a_label_split_across_lines_is_still_caught(self) -> None:
        """The miss that forced paragraph granularity.

        This passage sat in `RESULTS.md` §5.17 with the id on one line and the
        label on the next, and the line-based gate returned nothing for all
        three lines.
        """
        passage = (
            "したがって **`C_2×A_4` は `FRONTIER-ORD20-01` の未解決リストから外れ**、残るのは\n"
            "`F_20`, `C_7⋊C_3`, `SL(2,3)`, `S_4` の4群になる（status は `A4-ALLLANG-01` を継いで\n"
            "`COMPUTED`）。"
        )
        self.assertEqual(self.flag(passage, self.EMPIRICAL), {"A4-ALLLANG-01"})
        for line in passage.split("\n"):
            self.assertEqual(self.flag(line, self.EMPIRICAL), set(), "line alone must not suffice")

    def test_paragraphs_split_on_blank_lines_and_report_their_start(self) -> None:
        blocks = lint_claims.paragraphs("a\nb\n\n\nc\n")
        self.assertEqual(blocks, [(1, "a\nb"), (5, "c")])

    def test_mentioning_a_demoted_row_without_a_label_is_untouched(self) -> None:
        line = "`A4-FULL-01`（§5.5）に対応する別の（より難しい）問題である。"
        self.assertEqual(self.flag(line, self.EMPIRICAL), set())

    def test_live_prose_carries_no_stale_label(self) -> None:
        """The gate's verdict on the real files."""
        ledger = (ROOT / "CLAIMS_LEDGER.md").read_text(encoding="utf-8")
        empirical = {c[0] for c in lint_claims.parse_rows(ledger) if c[2] == "EMPIRICAL"}
        self.assertTrue(empirical, "no EMPIRICAL rows: the gate would be vacuous")
        withdrawal = __import__("re").compile(r"withdraw|retract|撤回|降格", __import__("re").I)
        offenders = []
        for name in ("README.md", "RESULTS.md"):
            text = (ROOT / name).read_text(encoding="utf-8")
            for number, block in lint_claims.paragraphs(text):
                if not withdrawal.search(block) and self.flag(block, empirical):
                    offenders.append(f"{name}:{number}")
        self.assertEqual(offenders, [])



class AdversarialBypassTests(unittest.TestCase):
    """Every way past this gate that two rounds of adversarial review executed.

    The commits that built this gate were written and verified by the same
    author, which is the structure `RETRACTIONS.md` entry 4 records failing
    before: the gate inherits the blind spot of the process it constrains. Two
    independent rounds walked through it, the second one straight through the
    first one's repairs.

    These drive `prose_errors` and `dead_paths` -- the functions `main()` calls
    -- on fixtures. Round two found the earlier version of this class asserting
    on predicates while the gate around them crashed, and one test asserting on
    the *source text* of the module rather than on its behaviour. A test that
    cannot run the gate cannot tell you the gate works.
    """

    #: Read from the ledger rather than typed here, so a row demoted later is
    #: covered by these tests on the day it is demoted. Round four pointed out
    #: that a hard-coded set silently stops testing whatever is added next.
    EMPIRICAL = {
        row[0] for row in lint_claims.parse_rows(
            (ROOT / "CLAIMS_LEDGER.md").read_text(encoding="utf-8")
        ) if row[2] == "EMPIRICAL"
    }
    KNOWN_ABSENT = frozenset({"site/index.html"})

    def complain(self, body: str) -> list[str]:
        """Run the prose gate over `body` as if it were a tracked document."""
        with tempfile.TemporaryDirectory() as tmp:
            page = Path(tmp) / "FIXTURE.md"
            page.write_text(body, encoding="utf-8")
            return lint_claims.prose_errors([page], self.EMPIRICAL)

    # --- round one ---

    def test_one_table_row_cannot_launder_another(self) -> None:
        """The whole table was one paragraph, so any EMPIRICAL cell exempted every row."""
        complaints = self.complain(
            "| claim | status |\n"
            "|---|---|\n"
            "| `A4-FULL-01` | COMPUTED |\n"
            "| `C7C3-FULL-01` | EMPIRICAL |\n"
        )
        self.assertTrue(any("A4-FULL-01" in c for c in complaints), complaints)

    def test_a_retraction_verb_alone_does_not_license_the_claim(self) -> None:
        self.assertTrue(self.complain("We retract the caveat: order ≤ 12 is settled."))

    def test_notes_subdirectories_are_inside_the_gate(self) -> None:
        """A false claim parked in `notes/archive/` was simply outside it.

        Driven through the gate on a real nested file rather than by grepping
        this module for the word `rglob`, which is what round two objected to.
        """
        with tempfile.TemporaryDirectory() as tmp:
            nested = Path(tmp) / "notes" / "archive"
            nested.mkdir(parents=True)
            page = nested / "probe.md"
            page.write_text("order ≤ 12 is settled.\n", encoding="utf-8")
            self.assertTrue(lint_claims.prose_errors([page], self.EMPIRICAL))
            self.assertIn(page, sorted((Path(tmp) / "notes").rglob("*.md")))

    # --- round two: the repairs themselves ---

    def test_a_quote_elsewhere_on_the_line_does_not_license_the_phrase(self) -> None:
        """Requiring *a* quotation mark was not requiring one around anything."""
        for line in (
            "We retract 「typographical note」: order ≤ 12 is settled.",
            'order ≤ 12 is settled. retract "x"',
        ):
            with self.subTest(line=line):
                self.assertTrue(self.complain(line), line)

    def test_quoting_the_withdrawn_wording_is_still_writable(self) -> None:
        """An unwritable retraction is how a wrong claim survives."""
        for line in (
            'Withdrawn: "order ≤ 12 is settled" was never established.',
            "この節は以前「位数 ≤ 12 の全群が決着」と書いていたが撤回する。",
        ):
            with self.subTest(line=line):
                self.assertEqual(self.complain(line), [], line)

    def test_lower_case_and_japanese_verbs_are_caught(self) -> None:
        for line in (
            "A4-FULL-01 has been proved for every word.",
            "A4-FULL-01 has been computed.",
            "A4-FULL-01 is decided.",
            "A4-FULL-01 is now closed.",
            "`A4-ALLLANG-01` は確定した。",
            "`ORD12-ALL-01` は落ちた。",
        ):
            with self.subTest(line=line):
                self.assertTrue(self.complain(line), line)

    def test_a_verb_only_passage_is_reported_and_does_not_crash(self) -> None:
        """It refused by raising `AttributeError`, so the author saw a traceback."""
        complaints = self.complain("A4-FULL-01 has been proved for every word.")
        self.assertEqual(len(complaints), 1)
        self.assertIn("proved", complaints[0])

    def test_a_negation_in_another_clause_does_not_license_the_verb(self) -> None:
        """A stop-time review got this past the fixed-width window.

        "not" sits within forty characters of "proved" while negating the
        opposite thing, so scanning a character count rather than a clause read
        the sentence backwards.
        """
        for line in (
            "A4-FULL-01 is not open; it has been proved for every word.",
            "A4-FULL-01, though not trivial, has been proved.",
            "No caveat applies — A4-FULL-01 has been proved.",
        ):
            with self.subTest(line=line):
                self.assertTrue(self.complain(line), line)

    def test_a_negated_verb_is_not_flagged(self) -> None:
        """These are exactly what an author should write about an EMPIRICAL row."""
        for line in (
            "A4-FULL-01 has not been proved.",
            "A4-FULL-01 could not be established.",
            "A4-FULL-01 remains open and is not resolved.",
        ):
            with self.subTest(line=line):
                self.assertEqual(self.complain(line), [], line)

    def test_a_pipe_in_prose_does_not_split_a_wrapped_claim(self) -> None:
        """Any unescaped pipe made its line a unit, cutting the claim from its verb."""
        self.assertTrue(self.complain("A4-FULL-01 | see appendix\nhas been proved for every word."))

    def test_an_undemoted_row_is_left_alone(self) -> None:
        self.assertEqual(self.complain("`A4-STD-01` is proved by product reachability."), [])

    # --- round three: the repairs to the repairs ---

    def test_quoting_a_phrase_does_not_license_restating_it(self) -> None:
        """Quoting it once used to license asserting it beside the quotation."""
        for line in (
            'We retract "order ≤ 12 is settled"; order ≤ 12 is settled.',
            '| We retract "order ≤ 12 is settled" | order ≤ 12 is settled |',
        ):
            with self.subTest(line=line):
                self.assertTrue(self.complain(line), line)

    def test_a_table_is_a_table_however_it_is_dressed(self) -> None:
        """A row laundered a false label when quoted, in HTML, or wrapped."""
        for name, body in (
            ("blockquote", "> | `A4-FULL-01` | COMPUTED |\n> | `C7C3-FULL-01` | EMPIRICAL |"),
            ("html", "<table><tr><td>A4-FULL-01</td><td>COMPUTED</td></tr>\n"
                     "<tr><td>C7C3-FULL-01</td><td>EMPIRICAL</td></tr></table>"),
            ("wrapped cell", "| A4-FULL-01 | has been\nproved for every word. |"),
        ):
            with self.subTest(name=name):
                self.assertTrue(self.complain(body), name)

    def test_a_retraction_can_still_quote_its_heading_and_report_the_claim(self) -> None:
        """`RETRACTIONS.md` must remain writable; it is now inside the gate."""
        self.assertEqual(
            self.complain('## "order ≤ 12 is settled"\n\n**Withdrawn.** The barrier is at order 12.\n'),
            [],
        )
        # Reporting is only reporting inside a retraction, so the fixture
        # carries the section the real file has.
        self.assertEqual(
            self.complain(
                "## The order-12 claim\n\n**Withdrawn.** The barrier is at order 12.\n\n"
                "**What was asserted.** That the result established `A4-FULL-01`.\n"
            ),
            [],
        )

    def test_reporting_outside_a_retraction_does_not_launder_a_claim(self) -> None:
        """Round four opened a paragraph with "Previously read ..." and walked through."""
        for body in (
            "Previously read the appendix. `A4-FULL-01` is PROVED.\n",
            "以前は誤記と書いていた。`A4-FULL-01` has been proved for every word。\n",
        ):
            with self.subTest(body=body):
                self.assertTrue(self.complain(body), body)

    def test_the_live_retraction_file_passes_its_own_gate(self) -> None:
        self.assertEqual(lint_claims.prose_errors([ROOT / "RETRACTIONS.md"], self.EMPIRICAL), [])

    # --- round four: the exemptions were scoped to blocks, not to claims ---

    def test_a_withdrawal_elsewhere_does_not_license_the_phrase(self) -> None:
        """One "Withdrawn." per section used to cover the whole section."""
        for body in (
            '# Results\nWithdrawn elsewhere.\n\n"order ≤ 12 is settled", full stop.\n',
            'Withdrawn elsewhere.\n\n"order ≤ 12 is settled", full stop.\n',
        ):
            with self.subTest(body=body):
                self.assertTrue(self.complain(body), body)

    def test_quote_characters_inside_inline_code_do_not_quote(self) -> None:
        self.assertTrue(self.complain(
            'We retract a typo. `"` order ≤ 12 is settled `"` is true.\n'
        ))

    def test_calling_the_quotation_correct_is_asserting_it(self) -> None:
        for body in (
            'We retract a typo. The statement “「order ≤ 12 is settled」 is correct” is itself true.\n',
            "We retract a typo. ~~order ≤ 12 is settled~~ is in fact true.\n",
        ):
            with self.subTest(body=body):
                self.assertTrue(self.complain(body), body)

    def test_a_coordinator_ends_a_negation(self) -> None:
        """`is not trivial and has been proved` negates the wrong half."""
        self.assertTrue(self.complain("`A4-FULL-01` is not trivial and has been proved.\n"))

    def test_an_html_row_spanning_lines_stays_one_unit(self) -> None:
        self.assertTrue(self.complain(
            "<table><tr><td>A4-FULL-01</td>\n<td>COMPUTED</td></tr>\n"
            "<tr><td>C7C3-FULL-01</td><td>EMPIRICAL</td></tr></table>\n"
        ))

    def test_an_unclosed_row_does_not_swallow_the_document(self) -> None:
        """Everything after it became one unit, and a later EMPIRICAL excused it."""
        self.assertTrue(self.complain(
            "| A4-FULL-01 | COMPUTED\nordinary prose\nC7C3-FULL-01 is EMPIRICAL\n"
        ))

    # --- round two: the cited-path check ---

    def dead(self, line: str) -> list[str]:
        return lint_claims.dead_paths(line, lint_claims.CITED_PATH, self.KNOWN_ABSENT)

    def test_an_em_dash_clause_does_not_exempt_a_dead_path(self) -> None:
        self.assertEqual(
            self.dead("This result moved the frontier — its evidence is `notes/nope.md`."),
            ["notes/nope.md"],
        )

    def test_a_semicolon_clause_does_not_exempt_a_dead_path(self) -> None:
        self.assertEqual(
            self.dead("This result moved the frontier; its evidence is `notes/nope.md`."),
            ["notes/nope.md"],
        )

    def test_naming_a_path_as_a_destination_does_not_exempt_it(self) -> None:
        """"moved to X" says X should exist; it is the one case that must not be waived."""
        self.assertEqual(self.dead("The evidence moved to `notes/nope.md`."), ["notes/nope.md"])

    def test_an_unrelated_from_does_not_exempt_a_dead_path(self) -> None:
        self.assertEqual(
            self.dead("Evidence from the experiment is recorded at `notes/nope.md`."),
            ["notes/nope.md"],
        )

    def test_a_marker_for_one_path_does_not_cover_another(self) -> None:
        """The replacement is the one path in the sentence that must exist."""
        self.assertEqual(
            self.dead("The former path `notes/old_gone.md` was deleted and its "
                      "replacement is `notes/new_gone.md`."),
            ["notes/new_gone.md"],
        )

    def test_a_marker_must_be_attached_to_the_path_it_excuses(self) -> None:
        """"A former *result* says `X`" excused `X` on a word about the result."""
        self.assertEqual(
            self.dead("A former result says `notes/new_gone.md` remains current."),
            ["notes/new_gone.md"],
        )

    def test_a_marker_may_modify_the_noun_in_front_of_the_path(self) -> None:
        self.assertEqual(
            self.dead("the former locations `x/gone.md`, `y/gone.md` were deleted"), []
        )

    def test_a_recorded_move_is_still_writable(self) -> None:
        self.assertEqual(
            self.dead("moved unchanged from `GSH/Monoid/Recognition.lean` into `GSH/Recognition.lean`."),
            [],
        )

    def test_a_live_path_is_not_reported(self) -> None:
        self.assertEqual(self.dead("see `GSH/Recognition.lean` for the interface"), [])


class BuildDocsTests(unittest.TestCase):
    """`build_docs.sh` must never publish a partial or stale set of PDFs.

    The four documents cross-cite, so a half-published set is worse than either
    whole one. Both failures below were found by adversarial review after the
    script looked fixed, and both are injected here rather than described.
    """

    SCRIPT = ROOT / "scripts" / "ci" / "build_docs.sh"

    def fixture(self, tmp: str) -> Path:
        """A miniature repository whose `docs/pdf/` holds four known PDFs."""
        docs = Path(tmp) / "docs"
        (docs / "pdf").mkdir(parents=True)
        scripts = Path(tmp) / "scripts" / "ci"
        scripts.mkdir(parents=True)
        (scripts / "build_docs.sh").write_text(
            self.SCRIPT.read_text(encoding="utf-8"), encoding="utf-8"
        )
        for name in ("blueprint", "textbook_number_theorists",
                     "textbook_formal_language_theorists", "textbook_lean_experts"):
            (docs / f"{name}.tex").write_text("%\n", encoding="utf-8")
            (docs / "pdf" / f"{name}.pdf").write_text(f"PUBLISHED-{name}", encoding="utf-8")
        return docs

    def published(self, docs: Path) -> dict[str, str]:
        return {p.name: p.read_text(encoding="utf-8") for p in sorted((docs / "pdf").glob("*.pdf"))}

    def test_a_silent_latexmk_cannot_publish_a_stale_artefact(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            docs = self.fixture(tmp)
            # the old next-to-the-source behaviour left these behind
            (docs / "blueprint.pdf").write_text("STALE", encoding="utf-8")
            before = self.published(docs)
            result = self._run(docs, {"latexmk": "#!/bin/sh\nexit 0\n"})
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual(self.published(docs), before)

    def test_rollback_removes_a_document_that_had_no_previous_version(self) -> None:
        """Restoring backups is not enough when there was nothing to back up.

        Round three published a first-ever `blueprint.pdf`, failed the next
        `mv`, and left it behind: the "rollback" produced a directory holding a
        file that was never there.
        """
        with tempfile.TemporaryDirectory() as tmp:
            docs = self.fixture(tmp)
            (docs / "pdf" / "blueprint.pdf").unlink()
            before = self.published(docs)
            counter = Path(tmp) / "n"
            counter.write_text("0", encoding="utf-8")
            result = self._run(docs, {
                "latexmk": (
                    "#!/bin/sh\n"
                    'for a in "$@"; do case "$a" in -outdir=*) out="${a#-outdir=}";; '
                    '*.tex) src="$a";; esac; done\n'
                    'printf NEW-%s "$src" > "$out/$(basename "${src%.tex}").pdf"\n'
                ),
                "mv": (
                    "#!/bin/sh\n"
                    f'n=$(cat {counter}); n=$((n+1)); echo $n > {counter}\n'
                    'if [ "$n" = "2" ]; then exit 74; fi\n'
                    'exec /bin/mv "$@"\n'
                ),
            })
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual(self.published(docs), before, result.stderr)
            self.assertFalse((docs / "pdf" / "blueprint.pdf").exists())

    def test_a_failed_rollback_keeps_the_previous_build_and_says_so(self) -> None:
        """A rollback that destroys what it rolls back to is worse than none.

        The first version printed "rolled back" whatever happened and then
        deleted the staging directory, which held the only remaining copy of the
        previous build.
        """
        with tempfile.TemporaryDirectory() as tmp:
            docs = self.fixture(tmp)
            before = self.published(docs)
            counter = Path(tmp) / "n"
            counter.write_text("0", encoding="utf-8")
            result = self._run(docs, {
                "latexmk": (
                    "#!/bin/sh\n"
                    'for a in "$@"; do case "$a" in -outdir=*) out="${a#-outdir=}";; '
                    '*.tex) src="$a";; esac; done\n'
                    'printf NEW-%s "$src" > "$out/$(basename "${src%.tex}").pdf"\n'
                ),
                # fail the second publish...
                "mv": (
                    "#!/bin/sh\n"
                    f'n=$(cat {counter}); n=$((n+1)); echo $n > {counter}\n'
                    'if [ "$n" = "2" ]; then exit 74; fi\n'
                    'exec /bin/mv "$@"\n'
                ),
                # ...and every restore, which writes back into pdf/. Copies made
                # *into* the backup still succeed, so the failure is the restore
                # itself rather than the preparation for it.
                "cp": (
                    "#!/bin/sh\n"
                    'for last in "$@"; do :; done\n'
                    'case "$last" in pdf/*) exit 74;; esac\n'
                    'exec /bin/cp "$@"\n'
                ),
            })
            self.assertEqual(result.returncode, 75, result.stderr)
            self.assertIn("ROLLBACK FAILED", result.stderr)
            self.assertNotIn("rolled back to the previous build", result.stderr)
            kept = [line for line in result.stderr.splitlines() if "preserved, undeleted" in line]
            self.assertTrue(kept, result.stderr)
            backup = Path(kept[0].split(" in ", 1)[1].strip())
            # Round four: asserting "at least one PDF survived" would pass while
            # a partial restore had emptied the backup as it went. The whole
            # previous build has to be recoverable, byte for byte.
            recovered = {p.name: p.read_text(encoding="utf-8") for p in backup.glob("*.pdf")}
            self.assertEqual(recovered, before, "the previous build is not fully recoverable")

    def test_a_failure_midway_through_publishing_rolls_back(self) -> None:
        with tempfile.TemporaryDirectory() as tmp:
            docs = self.fixture(tmp)
            before = self.published(docs)
            counter = Path(tmp) / "n"
            counter.write_text("0", encoding="utf-8")
            result = self._run(docs, {
                "latexmk": (
                    "#!/bin/sh\n"
                    'for a in "$@"; do case "$a" in -outdir=*) out="${a#-outdir=}";; '
                    '*.tex) src="$a";; esac; done\n'
                    'printf NEW-%s "$src" > "$out/$(basename "${src%.tex}").pdf"\n'
                ),
                "mv": (
                    "#!/bin/sh\n"
                    f'n=$(cat {counter}); n=$((n+1)); echo $n > {counter}\n'
                    'if [ "$n" = "2" ]; then exit 74; fi\n'
                    'exec /bin/mv "$@"\n'
                ),
            })
            self.assertNotEqual(result.returncode, 0, result.stdout)
            self.assertEqual(self.published(docs), before, "a mixture of two builds was published")

    def _run(self, docs: Path, stubs: dict[str, str]) -> "subprocess.CompletedProcess[str]":
        bindir = docs.parent / "bin"
        bindir.mkdir(exist_ok=True)
        for name, body in stubs.items():
            stub = bindir / name
            stub.write_text(body, encoding="utf-8")
            stub.chmod(0o755)
        return subprocess.run(
            ["bash", str(docs.parent / "scripts" / "ci" / "build_docs.sh")],
            cwd=docs.parent,
            env=dict(os.environ, PATH=f"{bindir}:{os.environ['PATH']}"),
            capture_output=True, text=True,
        )


if __name__ == "__main__":
    unittest.main()
