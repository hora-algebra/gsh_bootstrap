"""Checker for the order <= 59 coverage certificate.

`scripts/gap/coverage_le59.g` needs GAP, which CI does not have, so the audit is
run offline and its output is committed as `data/experiments/coverage_le59.tsv`.
A committed table that nothing re-derives is a claim resting on a file, so this
module verifies the parts that can be verified without GAP:

1.  COMPLETENESS.  The number of rows of each order must equal the number of
    groups of that order (OEIS A000001, CITED).  A missing group is the one
    error that would silently shrink the unresolved list.

2.  THE ABELIAN ROWS, INDEPENDENTLY.  The number of abelian groups of order n
    is prod_i p(a_i) over the prime factorisation n = prod_i q_i^{a_i}, where p
    is the integer partition function (Kronecker's classification of finite
    abelian groups).  This is computed here from scratch and compared against
    the count of `C1-abelian` verdicts, so 100 of the 299 rows are checked
    against an arithmetic identity rather than against GAP.

3.  AGREEMENT WITH THE REPOSITORY'S OWN IMPLEMENTATION.  For order <= 31 the
    unresolved set must be exactly the six groups of `FRONTIER-ORD20-01`, which
    `scripts/research/small_group_pst_coverage.py` obtains by hand-building
    every group in pure Python.  Two independent implementations, one of them
    not using GAP at all, agreeing on the overlap is the positive control for
    the extension to 59.

4.  THE CLAIM'S OWN NUMBERS.  Which groups are unresolved, which of those are
    monolithic, and the 7/7/10 split into families are pinned as sets, not as
    counts.  The first version of this file checked none of them, so
    relabelling any unresolved group above order 31 as covered passed every
    check and silently deleted an open problem -- a complete traversal of the
    wrong object, which is the defect `tools/verdict.py` exists to stop.

5.  NEGATIVE CONTROL.  Every validator above is re-run against deliberately
    corrupted tables and must reject them.  "Everything passed" and "the
    checker cannot say no" are the same output otherwise.

What is NOT checked here: that GAP's SmallGroups library is correct and
complete.  That is a CITED external input, recorded as such in the ledger row
`COVER-LE59-01`.
"""

from __future__ import annotations

import unittest
from pathlib import Path
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT / "data" / "experiments" / "coverage_le59.tsv"

MAX_ORDER = 59

#: Number of groups of order n, n <= 59.  CITED: OEIS A000001, the standard
#: classification of groups of small order.  Used as the completeness check, so
#: it is stated independently of the table it checks.
A000001: Dict[int, int] = {
    1: 1, 2: 1, 3: 1, 4: 2, 5: 1, 6: 2, 7: 1, 8: 5, 9: 2, 10: 2,
    11: 1, 12: 5, 13: 1, 14: 2, 15: 1, 16: 14, 17: 1, 18: 5, 19: 1, 20: 5,
    21: 2, 22: 2, 23: 1, 24: 15, 25: 2, 26: 2, 27: 5, 28: 4, 29: 1, 30: 4,
    31: 1, 32: 51, 33: 1, 34: 2, 35: 1, 36: 14, 37: 1, 38: 2, 39: 2, 40: 14,
    41: 1, 42: 6, 43: 1, 44: 4, 45: 2, 46: 2, 47: 1, 48: 52, 49: 2, 50: 5,
    51: 1, 52: 5, 53: 1, 54: 15, 55: 2, 56: 13, 57: 2, 58: 2, 59: 1,
}

#: The six groups of order <= 31 outside the covered class, as audited in
#: CLAIMS_LEDGER.md row FRONTIER-ORD20-01 and reproduced by
#: scripts/research/small_group_pst_coverage.py without GAP.
FRONTIER_LE31 = {
    (12, "A4"),
    (20, "C5 : C4"),
    (21, "C7 : C3"),
    (24, "SL(2,3)"),
    (24, "S4"),
    (24, "C2 x A4"),
}

#: The claim of `COVER-LE59-01` and `FAMILY-PHASE-01`, written out.  Without
#: this the checks above pass on a table whose *headline numbers* have been
#: changed: nothing else here looks at a verdict above order 31, so relabelling
#: an unresolved group as covered deletes an open problem silently.  That is the
#: `THOMAS-D2-02` failure -- a complete traversal of the wrong object -- and it
#: was live in the first version of this file.
UNRESOLVED = {
    (12, 3), (20, 3), (21, 1), (24, 3), (24, 12), (24, 13),
    (32, 6), (32, 7), (32, 8), (32, 15), (32, 44),
    (36, 3), (36, 9), (36, 11), (39, 1), (40, 3), (40, 12), (42, 1), (42, 2),
    (48, 3), (48, 28), (48, 29), (48, 30), (48, 31), (48, 32), (48, 33),
    (48, 48), (48, 49), (48, 50),
    (52, 3), (54, 5), (54, 6), (54, 8), (55, 1), (56, 11), (57, 1),
}

#: The 24 of those that are monolithic, hence the actual problem list.
MONOLITHIC_UNRESOLVED = {
    (12, 3), (20, 3), (21, 1), (24, 3), (24, 12),
    (32, 6), (32, 7), (32, 8), (32, 15), (32, 44),
    (36, 9), (39, 1), (42, 1),
    (48, 3), (48, 28), (48, 29), (48, 33),
    (52, 3), (54, 5), (54, 6), (54, 8), (55, 1), (56, 11), (57, 1),
}

#: Family sizes of FAMILY-PHASE-01: prime phase, composite phase, no split.
FAMILY_SIZES = (7, 7, 10)

VERDICTS = {
    "C1-abelian",
    "C2-nilpotent2",
    "C3-AsemiE",
    "C4-dicyclic",
    "R1-subdirect",
    "UNRESOLVED",
}


class Row:
    __slots__ = ("order", "ident", "structure", "verdict", "monolithic",
                 "phase", "abelian_normal")

    def __init__(self, fields: List[str]) -> None:
        self.order = int(fields[0])
        self.ident = int(fields[1])
        self.structure = fields[2]
        self.verdict = fields[3]
        self.monolithic = fields[4] == "true"
        self.phase = int(fields[5])
        self.abelian_normal = fields[6]


def read_table(text: str) -> List[Row]:
    rows: List[Row] = []
    for line in text.splitlines():
        if not line or line.startswith("#"):
            continue
        fields = line.split("\t")
        if fields[0] == "order":
            continue
        rows.append(Row(fields))
    return rows


def partitions(n: int) -> int:
    """p(n), the number of integer partitions, by the standard recurrence."""
    table = [1] + [0] * n
    for part in range(1, n + 1):
        for total in range(part, n + 1):
            table[total] += table[total - part]
    return table[n]


def factorize(n: int) -> Dict[int, int]:
    factors: Dict[int, int] = {}
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors[d] = factors.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        factors[n] = factors.get(n, 0) + 1
    return factors


def abelian_count(n: int) -> int:
    """Number of abelian groups of order n: prod p(a_i) over n = prod q_i^a_i.

    Kronecker's classification of finite abelian groups; the count is
    multiplicative and on a prime power q^a equals the number of partitions of
    a.  Derived here rather than tabulated, so it is independent of the table
    being checked.
    """
    total = 1
    for exponent in factorize(n).values():
        total *= partitions(exponent)
    return total


def check_completeness(rows: List[Row]) -> List[str]:
    seen: Dict[int, int] = {}
    for row in rows:
        seen[row.order] = seen.get(row.order, 0) + 1
    errors = []
    for order in range(1, MAX_ORDER + 1):
        want = A000001[order]
        got = seen.get(order, 0)
        if got != want:
            errors.append(f"order {order}: {got} rows, classification says {want}")
    return errors


def check_abelian(rows: List[Row]) -> List[str]:
    seen: Dict[int, int] = {}
    for row in rows:
        if row.verdict == "C1-abelian":
            seen[row.order] = seen.get(row.order, 0) + 1
    errors = []
    for order in range(1, MAX_ORDER + 1):
        want = abelian_count(order)
        got = seen.get(order, 0)
        if got != want:
            errors.append(
                f"order {order}: {got} rows marked abelian, "
                f"the partition formula gives {want}")
    return errors


def check_ids(rows: List[Row]) -> List[str]:
    """Each order's ids must be exactly 1..count, each once."""
    by_order: Dict[int, List[int]] = {}
    for row in rows:
        by_order.setdefault(row.order, []).append(row.ident)
    errors = []
    for order, idents in by_order.items():
        if sorted(idents) != list(range(1, len(idents) + 1)):
            errors.append(f"order {order}: ids are {sorted(idents)}")
    return errors


def check_verdict_labels(rows: List[Row]) -> List[str]:
    return [f"order {r.order} id {r.ident}: unknown verdict {r.verdict!r}"
            for r in rows if r.verdict not in VERDICTS]


def check_frontier(rows: List[Row]) -> List[str]:
    got = {(r.order, r.structure) for r in rows
           if r.verdict == "UNRESOLVED" and r.order <= 31}
    if got == FRONTIER_LE31:
        return []
    missing = FRONTIER_LE31 - got
    extra = got - FRONTIER_LE31
    errors = []
    if missing:
        errors.append(f"audited frontier group(s) not reported unresolved: {sorted(missing)}")
    if extra:
        errors.append(f"unresolved beyond the audited frontier: {sorted(extra)}")
    return errors


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


def check_unresolved_set(rows: List[Row]) -> List[str]:
    """The claim itself: which groups are unresolved, and which of those are
    monolithic.  Set equality both ways, so a group cannot be added or removed."""
    got = {(r.order, r.ident) for r in rows if r.verdict == "UNRESOLVED"}
    got_mono = {(r.order, r.ident) for r in rows
                if r.verdict == "UNRESOLVED" and r.monolithic}
    errors = []
    if got != UNRESOLVED:
        gone = sorted(UNRESOLVED - got)
        new = sorted(got - UNRESOLVED)
        if gone:
            errors.append(f"open problem(s) no longer reported unresolved: {gone}")
        if new:
            errors.append(f"unresolved group(s) not in the recorded claim: {new}")
    if got_mono != MONOLITHIC_UNRESOLVED:
        errors.append(
            f"monolithic unresolved set changed: "
            f"-{sorted(MONOLITHIC_UNRESOLVED - got_mono)} "
            f"+{sorted(got_mono - MONOLITHIC_UNRESOLVED)}")
    return errors


def check_family_partition(rows: List[Row]) -> List[str]:
    """FAMILY-PHASE-01: the 24 split 7 / 7 / 10 by phase group."""
    mono = [r for r in rows if r.verdict == "UNRESOLVED" and r.monolithic]
    prime = sum(1 for r in mono if r.phase and is_prime(r.phase))
    composite = sum(1 for r in mono if r.phase and not is_prime(r.phase))
    nosplit = sum(1 for r in mono if not r.phase)
    got = (prime, composite, nosplit)
    if got != FAMILY_SIZES:
        return [f"family sizes are {got}, the claim says {FAMILY_SIZES}"]
    if prime + composite + nosplit != len(MONOLITHIC_UNRESOLVED):
        return [f"families cover {prime + composite + nosplit} groups, "
                f"not {len(MONOLITHIC_UNRESOLVED)}"]
    return []


ALL_CHECKS = (
    ("completeness", check_completeness),
    ("abelian count", check_abelian),
    ("ids", check_ids),
    ("verdict labels", check_verdict_labels),
    ("frontier agreement", check_frontier),
    ("unresolved set", check_unresolved_set),
    ("family partition", check_family_partition),
)


class CoverageTableTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rows = read_table(TABLE.read_text(encoding="utf-8"))

    def test_table_is_present_and_sized(self) -> None:
        self.assertEqual(len(self.rows), sum(A000001.values()))

    def test_all_checks_pass(self) -> None:
        for name, check in ALL_CHECKS:
            with self.subTest(check=name):
                self.assertEqual(check(self.rows), [])

    def test_partition_function(self) -> None:
        # p(0..8); guards the arithmetic the abelian count rests on.
        self.assertEqual([partitions(k) for k in range(9)],
                         [1, 1, 2, 3, 5, 7, 11, 15, 22])

    def test_abelian_count_known_values(self) -> None:
        self.assertEqual(abelian_count(1), 1)
        self.assertEqual(abelian_count(8), 3)     # C8, C4xC2, C2^3
        self.assertEqual(abelian_count(16), 5)
        self.assertEqual(abelian_count(36), 4)    # (4 partitions of 2 x 2)
        self.assertEqual(abelian_count(59), 1)

    # ---- negative controls -------------------------------------------------
    #
    # Each validator is handed a table it must reject.  Without these, a
    # validator that returns [] unconditionally would pass every test above.

    def test_completeness_rejects_a_missing_group(self) -> None:
        damaged = [r for r in self.rows if not (r.order == 48 and r.ident == 29)]
        self.assertNotEqual(check_completeness(damaged), [])

    def test_abelian_check_rejects_a_relabelled_row(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if row.verdict == "C1-abelian":
                row.verdict = "C2-nilpotent2"
                break
        self.assertNotEqual(check_abelian(damaged), [])

    def test_abelian_check_rejects_an_invented_abelian_row(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if row.verdict == "C3-AsemiE":
                row.verdict = "C1-abelian"
                break
        self.assertNotEqual(check_abelian(damaged), [])

    def test_ids_reject_a_duplicate(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if row.order == 32 and row.ident == 7:
                row.ident = 6
                break
        self.assertNotEqual(check_ids(damaged), [])

    def test_verdict_labels_reject_an_unknown_label(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        damaged[0].verdict = "C9-wishful"
        self.assertNotEqual(check_verdict_labels(damaged), [])

    def test_frontier_rejects_a_silently_covered_frontier_group(self) -> None:
        # The dangerous direction: a group of the audited frontier reported as
        # covered would delete an open problem from the list.
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if row.order == 12 and row.structure == "A4":
                row.verdict = "C3-AsemiE"
                break
        self.assertNotEqual(check_frontier(damaged), [])

    def test_unresolved_set_rejects_a_deleted_open_problem(self) -> None:
        # The dangerous direction above order 31, where `check_frontier` does
        # not look: relabelling (48, 3) -- a Family A group -- as covered would
        # remove a problem from the list with no other check noticing.
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if (row.order, row.ident) == (48, 3):
                row.verdict = "C3-AsemiE"
                break
        self.assertNotEqual(check_unresolved_set(damaged), [])
        self.assertNotEqual(check_family_partition(damaged), [])

    def test_unresolved_set_rejects_an_invented_open_problem(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if row.order == 50 and row.verdict != "UNRESOLVED":
                row.verdict = "UNRESOLVED"
                break
        self.assertNotEqual(check_unresolved_set(damaged), [])

    def test_unresolved_set_rejects_a_flipped_monolithic_flag(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if (row.order, row.ident) == (56, 11):
                row.monolithic = False
                break
        self.assertNotEqual(check_unresolved_set(damaged), [])

    def test_family_partition_rejects_a_moved_group(self) -> None:
        # C_11 : C_5 has phase 5.  Moving it to a composite phase changes which
        # family it belongs to, and hence which mechanism is predicted to work.
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if (row.order, row.ident) == (55, 1):
                row.phase = 4
                break
        self.assertNotEqual(check_family_partition(damaged), [])

    def test_family_partition_rejects_a_dropped_decomposition(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if (row.order, row.ident) == (39, 1):
                row.phase = 0
                break
        self.assertNotEqual(check_family_partition(damaged), [])

    def test_is_prime(self) -> None:
        self.assertEqual([n for n in range(1, 20) if is_prime(n)],
                         [2, 3, 5, 7, 11, 13, 17, 19])

    def test_frontier_rejects_an_extra_unresolved_group_below_31(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if row.order <= 31 and row.verdict == "C3-AsemiE":
                row.verdict = "UNRESOLVED"
                break
        self.assertNotEqual(check_frontier(damaged), [])


if __name__ == "__main__":
    unittest.main()
