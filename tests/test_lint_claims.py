from __future__ import annotations

import importlib.util
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

_spec = importlib.util.spec_from_file_location(
    "lint_claims", ROOT / "scripts" / "lint_claims.py"
)
lint_claims = importlib.util.module_from_spec(_spec)
assert _spec.loader is not None
_spec.loader.exec_module(lint_claims)


ROW = (
    "| ESC-01 | Words satisfying \\|w\\|_a ≡ \\|w\\|_b mod 2 form a group language. "
    "| COMPUTED | `scripts/search.py` step [1] | hora-algebra | 2026-07-25 |"
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
        self.assertIsNotNone(lint_claims.COMPLETENESS_ATTESTATION.search(text))

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


if __name__ == "__main__":
    unittest.main()
