"""Checker for the order <= 60 coverage certificate and README status table.

`scripts/gap/coverage_le60.g` needs GAP, which CI does not have, so the audit is
run offline and its output is committed as `data/experiments/coverage_le60.tsv`.
A committed table that nothing re-derives is a claim resting on a file, so this
module verifies the parts that can be verified without GAP:

1.  COMPLETENESS.  The number of rows of each order must equal the number of
    groups of that order (OEIS A000001, CITED).  A missing group is the one
    error that would silently shrink the unresolved list.

2.  THE ABELIAN ROWS, INDEPENDENTLY.  The number of abelian groups of order n
    is prod_i p(a_i) over the prime factorisation n = prod_i q_i^{a_i}, where p
    is the integer partition function (Kronecker's classification of finite
    abelian groups).  This is computed here from scratch and compared against
    the count of `C1-abelian` verdicts, so all 102 abelian rows among the 312
    groups through order 60 are checked against an arithmetic identity rather
    than merely copied from the GAP verdict column.

3.  AGREEMENT WITH THE REPOSITORY'S OWN IMPLEMENTATION.  For order <= 31 the
    unresolved set must be exactly the four groups left after the PROVED A4
    result and its subdirect consequences.  The older six-group PST frontier
    is independently obtained by `scripts/research/small_group_pst_coverage.py`;
    this checker additionally pins the two now-covered rows.

4.  THE CLAIM'S OWN NUMBERS.  Which groups are unresolved, which of those are
    monolithic, and the phase group of each of the 24 are pinned per group.
    The first version of this file checked none of them, so relabelling any
    unresolved group above order 31 as covered passed every check and
    silently deleted an open problem.  The second pinned the families by the
    triple (6, 7, 11), which is invariant under exchanging a prime-phase
    group for a composite-phase one -- the exchange that misroutes which
    mechanism a group is sent to.  Both are the same defect
    `tools/verdict.py` exists to stop: a complete traversal of the wrong
    object.

5.  README COVERAGE.  The continuation of the human-facing table names every
    non-abelian `SmallGroup(n,i)` for 32 <= n <= 60 exactly once.  Its status
    must be proved exactly when the independently checked certificate has a
    positive verdict, and unknown exactly when the table says unresolved.

6.  NEGATIVE CONTROL.  Every validator above is re-run against deliberately
    corrupted tables and must reject them.  "Everything passed" and "the
    checker cannot say no" are the same output otherwise.

What is NOT checked here: that GAP's SmallGroups library is correct and
complete.  That is a CITED external input, recorded as such in the ledger rows
`COVER-LE60-POS-01` and `COVER-LE60-RESIDUAL-01`.
"""

import re
import unittest
from pathlib import Path
from typing import Dict, List, Tuple

ROOT = Path(__file__).resolve().parents[1]
TABLE = ROOT / "data" / "experiments" / "coverage_le60.tsv"
README = ROOT / "README.md"

MAX_ORDER = 60

#: Number of groups of order n, n <= 60.  CITED: OEIS A000001, the standard
#: classification of groups of small order.  Used as the completeness check, so
#: it is stated independently of the table it checks.
A000001: Dict[int, int] = {
    1: 1, 2: 1, 3: 1, 4: 2, 5: 1, 6: 2, 7: 1, 8: 5, 9: 2, 10: 2,
    11: 1, 12: 5, 13: 1, 14: 2, 15: 1, 16: 14, 17: 1, 18: 5, 19: 1, 20: 5,
    21: 2, 22: 2, 23: 1, 24: 15, 25: 2, 26: 2, 27: 5, 28: 4, 29: 1, 30: 4,
    31: 1, 32: 51, 33: 1, 34: 2, 35: 1, 36: 14, 37: 1, 38: 2, 39: 2, 40: 14,
    41: 1, 42: 6, 43: 1, 44: 4, 45: 2, 46: 2, 47: 1, 48: 52, 49: 2, 50: 5,
    51: 1, 52: 5, 53: 1, 54: 15, 55: 2, 56: 13, 57: 2, 58: 2, 59: 1, 60: 13,
}

#: The four independent groups of order <= 31 still unresolved after the
#: PROVED A4-ALLLANG-01 result and its subdirect consequences are seeded into
#: the fixpoint.  The older PST frontier has six rows: A4 is now covered
#: directly and C2 x A4 follows by subdirect reduction.
FRONTIER_LE31 = {
    (20, "C5 : C4"),
    (21, "C7 : C3"),
    (24, "SL(2,3)"),
    (24, "S4"),
}

#: The claim of `COVER-LE60-RESIDUAL-01` and `FAMILY-PHASE-01`, written out.  Without
#: this the checks above pass on a table whose *headline numbers* have been
#: changed: nothing else here looks at a verdict above order 31, so relabelling
#: an unresolved group as covered deletes an open problem silently.  That is the
#: `THOMAS-D2-02` failure -- a complete traversal of the wrong object -- and it
#: was live in the first version of this file.
UNRESOLVED = {
    (20, 3), (21, 1), (24, 3), (24, 12),
    (32, 6), (32, 7), (32, 8), (32, 15), (32, 44),
    (36, 9), (39, 1), (40, 3), (40, 12), (42, 1), (42, 2),
    (48, 3), (48, 28), (48, 29), (48, 30), (48, 32), (48, 33), (48, 48),
    (52, 3), (54, 5), (54, 6), (54, 8), (55, 1), (56, 11), (57, 1),
    (60, 5), (60, 6), (60, 7),
}

#: The 24 of those that are monolithic, hence the direct-attack problem list.
MONOLITHIC_UNRESOLVED = {
    (20, 3), (21, 1), (24, 3), (24, 12),
    (32, 6), (32, 7), (32, 8), (32, 15), (32, 44),
    (36, 9), (39, 1), (42, 1),
    (48, 3), (48, 28), (48, 29), (48, 33),
    (52, 3), (54, 5), (54, 6), (54, 8), (55, 1), (56, 11), (57, 1),
    (60, 5),
}

def is_prime(n: int) -> bool:
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True


#: The phase group order of each of the 24, which is the datum FAMILY-PHASE-01
#: partitions by.  Pinned per group rather than as family sizes: sizes alone are
#: invariant under SWAPPING one prime-phase group with one composite-phase one,
#: and that swap is not cosmetic -- family membership decides which mechanism a
#: group is sent to, so a swap routes `N-FAMILY-A-001` at a group the
#: obstruction `F20-FULL-OBS-01` proves it fails on, and skips one it should
#: reach.  0 means no split `abelian : cyclic` decomposition was found.
PHASE = {
    (20, 3): 4, (21, 1): 3, (24, 3): 0, (24, 12): 0,
    (32, 6): 4, (32, 7): 0, (32, 8): 0, (32, 15): 0, (32, 44): 0,
    (36, 9): 4, (39, 1): 3, (42, 1): 6,
    (48, 3): 3, (48, 28): 0, (48, 29): 0, (48, 33): 0,
    (52, 3): 4, (54, 5): 6, (54, 6): 6, (54, 8): 0,
    (55, 1): 5, (56, 11): 7, (57, 1): 3, (60, 5): 0,
}

#: The families as sets, derived here from PHASE so the two cannot drift apart,
#: and checked against the table independently.
FAMILY_A = {k for k, p in PHASE.items() if p and is_prime(p)}
FAMILY_B = {k for k, p in PHASE.items() if p and not is_prime(p)}
FAMILY_C = {k for k, p in PHASE.items() if not p}

#: Family sizes of FAMILY-PHASE-01: prime phase, composite phase, no split.
FAMILY_SIZES = (6, 7, 11)

VERDICTS = {
    "C1-abelian",
    "C2-nilpotent2",
    "C3-AsemiE",
    "C4-dicyclic",
    "C5-A4",
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


SMALL_GROUP_REF = re.compile(r"SmallGroup\((\d+),\s*(\d+)\)")


def check_readme_status(text: str, rows: List[Row]) -> List[str]:
    """Compare the README continuation against the certificate per group.

    The pretty <=31 table predates SmallGroup ids, so this check intentionally
    targets the new 32..60 continuation.  Every new group is named by id because
    GAP's StructureDescription is not injective (already at order 60).
    """
    expected = {
        (row.order, row.ident): (
            "unknown" if row.verdict == "UNRESOLVED" else "proved")
        for row in rows
        if 32 <= row.order <= 60 and row.verdict != "C1-abelian"
    }
    seen: Dict[Tuple[int, int], str] = {}
    errors: List[str] = []
    for line in text.splitlines():
        refs = [(int(n), int(i)) for n, i in SMALL_GROUP_REF.findall(line)]
        if not refs:
            continue
        if "**× 未知**" in line:
            status = "unknown"
        elif "**⭕️ 証明完了**" in line:
            status = "proved"
        else:
            errors.append(f"README row has SmallGroup ids but no audited status: {line}")
            continue
        for key in refs:
            if key in seen:
                errors.append(f"README repeats SmallGroup{key}")
            seen[key] = status
    missing = sorted(set(expected) - set(seen))
    extra = sorted(set(seen) - set(expected))
    wrong = sorted(key for key in set(expected) & set(seen)
                   if expected[key] != seen[key])
    if missing:
        errors.append(f"README misses non-abelian groups: {missing}")
    if extra:
        errors.append(f"README invents/out-of-range groups: {extra}")
    if wrong:
        errors.append(f"README status disagrees with certificate: {wrong}")
    return errors


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


EXPECTED_DICYCLIC = {
    (12, 1), (16, 9), (20, 1), (24, 4), (28, 1), (32, 20), (36, 1),
    (40, 4), (44, 1), (48, 8), (52, 1), (56, 3), (60, 3),
}

A4_CLOSURE = {
    (12, 3), (24, 13), (36, 3), (36, 11),
    (48, 31), (48, 49), (48, 50), (60, 9),
}


def check_dicyclic_set(rows: List[Row]) -> List[str]:
    """Pin C4 per group; the former shortcut had false positives at order 60."""
    got = {(r.order, r.ident) for r in rows if r.verdict == "C4-dicyclic"}
    if got == EXPECTED_DICYCLIC:
        return []
    return [
        f"dicyclic set changed: -{sorted(EXPECTED_DICYCLIC - got)} "
        f"+{sorted(got - EXPECTED_DICYCLIC)}"
    ]


def check_a4_closure(rows: List[Row]) -> List[str]:
    got = {
        (r.order, r.ident) for r in rows
        if r.verdict == "C5-A4"
        or ((r.order, r.ident) in A4_CLOSURE and r.verdict == "R1-subdirect")
    }
    if got == A4_CLOSURE:
        return []
    return [f"A4 closure changed: -{sorted(A4_CLOSURE - got)} "
            f"+{sorted(got - A4_CLOSURE)}"]


def check_frontier(rows: List[Row]) -> List[str]:
    got = {(r.order, r.structure) for r in rows
           if r.verdict == "UNRESOLVED" and r.order <= 31}
    a4 = next((r for r in rows if (r.order, r.ident) == (12, 3)), None)
    c2a4 = next((r for r in rows if (r.order, r.ident) == (24, 13)), None)
    if (got == FRONTIER_LE31 and a4 is not None and a4.verdict == "C5-A4"
            and c2a4 is not None and c2a4.verdict == "R1-subdirect"):
        return []
    missing = FRONTIER_LE31 - got
    extra = got - FRONTIER_LE31
    errors = []
    if missing:
        errors.append(f"audited frontier group(s) not reported unresolved: {sorted(missing)}")
    if extra:
        errors.append(f"unresolved beyond the audited frontier: {sorted(extra)}")
    if a4 is None or a4.verdict != "C5-A4":
        errors.append("A4 is not seeded by A4-ALLLANG-01")
    if c2a4 is None or c2a4.verdict != "R1-subdirect":
        errors.append("C2 x A4 is not recovered by the subdirect fixpoint")
    return errors


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
    """FAMILY-PHASE-01, per group and not by size.

    Checking only the triple (6, 7, 11) is invariant under exchanging a
    prime-phase group for a composite-phase one, and that exchange is the error
    that matters: family membership is what decides which mechanism a group is
    sent to.
    """
    mono = {(r.order, r.ident): r for r in rows
            if r.verdict == "UNRESOLVED" and r.monolithic}
    errors = []

    for key, want in sorted(PHASE.items()):
        row = mono.get(key)
        if row is None:
            errors.append(f"{key}: no monolithic unresolved row to carry a phase")
        elif row.phase != want:
            errors.append(f"{key}: phase {row.phase}, the claim says {want}")
    for key in sorted(set(mono) - set(PHASE)):
        errors.append(f"{key}: monolithic and unresolved but has no recorded phase")
    if errors:
        return errors

    got_a = {k for k, r in mono.items() if r.phase and is_prime(r.phase)}
    got_b = {k for k, r in mono.items() if r.phase and not is_prime(r.phase)}
    got_c = {k for k, r in mono.items() if not r.phase}
    for name, got, want in (("A", got_a, FAMILY_A),
                            ("B", got_b, FAMILY_B),
                            ("C", got_c, FAMILY_C)):
        if got != want:
            errors.append(f"family {name}: -{sorted(want - got)} +{sorted(got - want)}")
    if (len(got_a), len(got_b), len(got_c)) != FAMILY_SIZES:
        errors.append(
            f"family sizes are {(len(got_a), len(got_b), len(got_c))}, "
            f"the claim says {FAMILY_SIZES}")
    return errors


ALL_CHECKS = (
    ("completeness", check_completeness),
    ("abelian count", check_abelian),
    ("ids", check_ids),
    ("verdict labels", check_verdict_labels),
    ("dicyclic set", check_dicyclic_set),
    ("A4 closure", check_a4_closure),
    ("frontier agreement", check_frontier),
    ("unresolved set", check_unresolved_set),
    ("family partition", check_family_partition),
)


class CoverageTableTest(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.rows = read_table(TABLE.read_text(encoding="utf-8"))
        cls.readme = README.read_text(encoding="utf-8")

    def test_table_is_present_and_sized(self) -> None:
        self.assertEqual(len(self.rows), sum(A000001.values()))

    def test_all_checks_pass(self) -> None:
        for name, check in ALL_CHECKS:
            with self.subTest(check=name):
                self.assertEqual(check(self.rows), [])

    def test_readme_lists_every_new_nonabelian_group_once(self) -> None:
        self.assertEqual(check_readme_status(self.readme, self.rows), [])

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
        self.assertEqual(abelian_count(60), 2)

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

    def test_dicyclic_check_rejects_the_old_order60_false_positive(self) -> None:
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if (row.order, row.ident) == (60, 1):  # C5 x Dic_3, not Dic_15
                row.verdict = "C4-dicyclic"
                break
        self.assertNotEqual(check_dicyclic_set(damaged), [])

    def test_frontier_rejects_a_silently_covered_frontier_group(self) -> None:
        # The dangerous direction: a group of the audited frontier reported as
        # covered would delete an open problem from the list.
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if (row.order, row.ident) == (20, 3):
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

    def test_family_partition_rejects_a_swap_between_families(self) -> None:
        # Sizes stay (6, 7, 11) under an exchange, so a size check cannot see
        # this.  C_11 : C_5 (prime phase 5) and C_13 : C_4 (composite phase 4)
        # trade places, which would route the Family A run at a group
        # F20-FULL-OBS-01 proves the mechanism fails on.
        damaged = read_table(TABLE.read_text(encoding="utf-8"))
        for row in damaged:
            if (row.order, row.ident) == (55, 1):
                row.phase = 4
            elif (row.order, row.ident) == (52, 3):
                row.phase = 5
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

    def test_readme_check_rejects_a_missing_group(self) -> None:
        damaged = self.readme.replace("SmallGroup(60, 5)", "SmallGroup(60, 500)", 1)
        self.assertNotEqual(check_readme_status(damaged, self.rows), [])

    def test_readme_check_rejects_a_status_flip(self) -> None:
        lines = self.readme.splitlines()
        for i, line in enumerate(lines):
            if "SmallGroup(60, 5)" in line:
                lines[i] = line.replace("**× 未知**", "**⭕️ 証明完了**")
                break
        self.assertNotEqual(check_readme_status("\n".join(lines), self.rows), [])


if __name__ == "__main__":
    unittest.main()
