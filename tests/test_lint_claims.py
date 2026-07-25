from __future__ import annotations

import importlib.util
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


if __name__ == "__main__":
    unittest.main()
