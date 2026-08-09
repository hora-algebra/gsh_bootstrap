#!/usr/bin/env python3
"""Independently check every positive order-60 SmallGroups witness.

GAP emits candidate multiplication tables and structural witnesses.  This
module deliberately does not import GAP: it checks the group axioms and the
stated sufficient criterion directly on each finite table.  It certifies only
the positive rows.  The complement in ``coverage_le60.tsv`` remains an
UNREVIEWED search result, not a lower bound on generalized star-height.
"""

from __future__ import annotations

from copy import deepcopy
from dataclasses import dataclass
import json
from pathlib import Path
import sys
from typing import Any, Iterable

ROOT = Path(__file__).resolve().parents[2]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from tools.verdict import Control, Run, exhaustive  # noqa: E402


CERTIFICATE = ROOT / "data" / "experiments" / "coverage_le60_witnesses.jsonl"
COVERAGE_TABLE = ROOT / "data" / "experiments" / "coverage_le60.tsv"
VERDICT_FILE = ROOT / "data" / "verdicts" / "small_group_coverage_le60.json"
SCHEMA = "gsh-small-group-witness-v1"
CLAIM_ID = "COVER-LE60-POS-01"


class AuditError(ValueError):
    """A certificate is malformed or fails its claimed structural test."""


@dataclass(frozen=True, slots=True)
class AuditReport:
    errors: list[str]
    visited: int
    positive_groups: int
    verified_groups: int
    new_nonabelian_groups: int

    @property
    def ok(self) -> bool:
        return not self.errors


@dataclass(frozen=True, slots=True)
class GroupTable:
    key: tuple[int, int]
    n: int
    mul: tuple[int, ...]
    inv: tuple[int, ...]

    def product(self, x: int, y: int) -> int:
        return self.mul[x * self.n + y]


def load_coverage(path: str | Path) -> dict[tuple[int, int], str]:
    """Load the GAP coverage table, retaining only key and verdict."""

    rows: dict[tuple[int, int], str] = {}
    header_seen = False
    for line_number, raw in enumerate(Path(path).read_text(encoding="utf-8").splitlines(), 1):
        if not raw or raw.startswith("#"):
            continue
        fields = raw.split("\t")
        if not header_seen:
            if fields[:4] != ["order", "id", "structure", "verdict"]:
                raise AuditError(f"{path}:{line_number}: unexpected TSV header")
            header_seen = True
            continue
        if len(fields) != 7:
            raise AuditError(f"{path}:{line_number}: expected 7 TSV fields")
        try:
            key = (int(fields[0]), int(fields[1]))
        except ValueError as exc:
            raise AuditError(f"{path}:{line_number}: non-integer group key") from exc
        if key in rows:
            raise AuditError(f"{path}:{line_number}: duplicate group key {key}")
        rows[key] = fields[3]
    if not header_seen:
        raise AuditError(f"{path}: missing TSV header")
    return rows


def load_certificate(path: str | Path) -> tuple[dict[str, Any], list[dict[str, Any]]]:
    """Load the JSON-lines header and positive group records."""

    lines = Path(path).read_text(encoding="utf-8").splitlines()
    if not lines:
        raise AuditError(f"{path}: empty certificate")
    try:
        items = [json.loads(line) for line in lines]
    except json.JSONDecodeError as exc:
        raise AuditError(f"{path}:{exc.lineno}: invalid JSON") from exc
    if not all(isinstance(item, dict) for item in items):
        raise AuditError(f"{path}: every line must be a JSON object")
    return items[0], items[1:]


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise AuditError(message)


def _int(value: Any, label: str) -> int:
    _require(type(value) is int, f"{label}: expected an integer")
    return value


def _index_set(value: Any, n: int, label: str) -> set[int]:
    _require(isinstance(value, list), f"{label}: expected a list")
    result = {_int(x, label) for x in value}
    _require(len(result) == len(value), f"{label}: duplicate element")
    _require(all(0 <= x < n for x in result), f"{label}: element out of range")
    return result


def _check_group(record: dict[str, Any]) -> tuple[GroupTable, int]:
    order = _int(record.get("order"), "order")
    group_id = _int(record.get("id"), "id")
    key = (order, group_id)
    _require(order >= 1 and group_id >= 1, f"{key}: invalid key")
    raw = record.get("mul")
    _require(isinstance(raw, list), f"{key}: mul is not a list")
    _require(len(raw) == order * order, f"{key}: multiplication table has wrong size")
    _require(all(type(x) is int and 0 <= x < order for x in raw),
             f"{key}: multiplication table entry out of range")
    mul = tuple(raw)
    visited = order * order

    def product(x: int, y: int) -> int:
        return mul[x * order + y]

    for x in range(order):
        _require(product(0, x) == x and product(x, 0) == x,
                 f"{key}: element 0 is not a two-sided identity")
    visited += 2 * order

    for x in range(order):
        for y in range(order):
            xy = product(x, y)
            for z in range(order):
                _require(product(xy, z) == product(x, product(y, z)),
                         f"{key}: multiplication is not associative")
                visited += 1

    inverses: list[int] = []
    for x in range(order):
        choices = [y for y in range(order)
                   if product(x, y) == 0 and product(y, x) == 0]
        _require(len(choices) == 1, f"{key}: element {x} lacks a unique two-sided inverse")
        inverses.append(choices[0])
        visited += order
    return GroupTable(key, order, mul, tuple(inverses)), visited


def _check_subgroup(table: GroupTable, subset: set[int], label: str) -> int:
    n = table.n
    _require(0 in subset, f"{table.key}: {label} omits the identity")
    for x in subset:
        _require(table.inv[x] in subset, f"{table.key}: {label} is not inverse-closed")
        for y in subset:
            _require(table.product(x, y) in subset,
                     f"{table.key}: {label} is not product-closed")
    return len(subset) + len(subset) ** 2


def _check_abelian(table: GroupTable) -> int:
    for x in range(table.n):
        for y in range(table.n):
            _require(table.product(x, y) == table.product(y, x),
                     f"{table.key}: C1 witness is nonabelian")
    return table.n ** 2


def _check_class_two(table: GroupTable) -> int:
    """Check [G,G] <= Z(G), which is equivalent to nilpotency class <= 2."""

    visited = 0
    for x in range(table.n):
        for y in range(table.n):
            comm = table.product(
                table.product(table.inv[x], table.inv[y]), table.product(x, y))
            for z in range(table.n):
                _require(table.product(comm, z) == table.product(z, comm),
                         f"{table.key}: C2 commutator is not central")
                visited += 1
    return visited


def _check_split(table: GroupTable, witness: Any) -> int:
    _require(isinstance(witness, dict), f"{table.key}: C3 witness is not an object")
    _require(set(witness) == {"normal", "complement"},
             f"{table.key}: C3 witness has wrong fields")
    normal = _index_set(witness["normal"], table.n, f"{table.key}: C3 normal")
    complement = _index_set(
        witness["complement"], table.n, f"{table.key}: C3 complement")
    visited = _check_subgroup(table, normal, "C3 normal")
    visited += _check_subgroup(table, complement, "C3 complement")
    for x in normal:
        for y in normal:
            _require(table.product(x, y) == table.product(y, x),
                     f"{table.key}: C3 normal subgroup is nonabelian")
    visited += len(normal) ** 2
    for e in complement:
        _require(table.product(e, e) == 0,
                 f"{table.key}: C3 complement does not have exponent two")
    visited += len(complement)
    for x in complement:
        for y in complement:
            _require(table.product(x, y) == table.product(y, x),
                     f"{table.key}: C3 complement is nonabelian")
    visited += len(complement) ** 2
    for g in range(table.n):
        for a in normal:
            conjugate = table.product(table.product(table.inv[g], a), g)
            _require(conjugate in normal, f"{table.key}: C3 subgroup is not normal")
    visited += table.n * len(normal)
    _require(normal & complement == {0}, f"{table.key}: C3 factors intersect nontrivially")
    products = {table.product(a, e) for a in normal for e in complement}
    visited += len(normal) * len(complement)
    _require(products == set(range(table.n)), f"{table.key}: C3 factors do not cover G")
    return visited


def _check_index_two(table: GroupTable, witness: Any) -> int:
    """C6: an abelian subgroup of index two, split or not.

    Krasner--Kaloujnine embeds ``G`` into ``A wr C2 = (A x A) : C2``, which is
    split abelian-by-elementary-abelian-2, so ``G`` divides a group of the C3
    class and PST-GRP-03 applies whether or not ``G`` splits over ``A``.  Index
    two makes ``A`` normal automatically, so subgroup closure, commutativity,
    and the exact index are the entire premise to check.
    """

    _require(isinstance(witness, dict) and set(witness) == {"subgroup"},
             f"{table.key}: C6 witness has wrong fields")
    subgroup = _index_set(witness["subgroup"], table.n, f"{table.key}: C6 subgroup")
    _require(2 * len(subgroup) == table.n,
             f"{table.key}: C6 subgroup does not have index two")
    visited = _check_subgroup(table, subgroup, "C6 subgroup")
    for x in subgroup:
        for y in subgroup:
            _require(table.product(x, y) == table.product(y, x),
                     f"{table.key}: C6 subgroup is nonabelian")
    return visited + len(subgroup) ** 2


def _powers(table: GroupTable, x: int) -> list[int]:
    result = [0]
    current = 0
    while True:
        current = table.product(current, x)
        if current == 0:
            return result
        _require(current not in result, f"{table.key}: malformed power cycle")
        result.append(current)


def _check_dicyclic(table: GroupTable, witness: Any) -> int:
    _require(isinstance(witness, dict) and set(witness) == {"x", "y"},
             f"{table.key}: C4 witness has wrong fields")
    x = _int(witness["x"], f"{table.key}: C4 x")
    y = _int(witness["y"], f"{table.key}: C4 y")
    _require(0 <= x < table.n and 0 <= y < table.n, f"{table.key}: C4 index out of range")
    _require(table.n % 4 == 0 and table.n >= 8, f"{table.key}: C4 order is not 4n, n>=2")
    n = table.n // 4
    powers = _powers(table, x)
    _require(len(powers) == 2 * n, f"{table.key}: C4 x has wrong order")
    _require(y not in powers, f"{table.key}: C4 y belongs to <x>")
    _require(table.product(y, y) == powers[n], f"{table.key}: C4 square relation fails")
    conjugate = table.product(table.product(table.inv[y], x), y)
    _require(conjugate == table.inv[x], f"{table.key}: C4 inversion relation fails")
    normal_forms = set(powers) | {table.product(a, y) for a in powers}
    _require(normal_forms == set(range(table.n)), f"{table.key}: C4 generators do not cover G")
    return 3 * len(powers) + 5


def _even_permutations_four() -> set[tuple[int, int, int, int]]:
    from itertools import permutations

    result = set()
    for perm in permutations(range(4)):
        inversions = sum(perm[i] > perm[j] for i in range(4) for j in range(i + 1, 4))
        if inversions % 2 == 0:
            result.add(perm)
    return result


A4 = _even_permutations_four()


def _perm_product(left: tuple[int, ...], right: tuple[int, ...]) -> tuple[int, ...]:
    # GAP uses right actions: i^(g*h) = (i^g)^h.
    return tuple(right[left[i]] for i in range(4))


def _check_a4(table: GroupTable, witness: Any) -> int:
    _require(table.n == 12, f"{table.key}: C5 table does not have order 12")
    _require(isinstance(witness, dict) and set(witness) == {"permutation_images"},
             f"{table.key}: C5 witness has wrong fields")
    raw = witness["permutation_images"]
    _require(isinstance(raw, list) and len(raw) == 12,
             f"{table.key}: C5 image list has wrong size")
    images: list[tuple[int, ...]] = []
    for image in raw:
        _require(isinstance(image, list) and len(image) == 4,
                 f"{table.key}: C5 image is not a four-point permutation")
        perm = tuple(_int(x, f"{table.key}: C5 permutation") for x in image)
        _require(perm in A4, f"{table.key}: C5 image is not an even permutation")
        images.append(perm)
    _require(set(images) == A4, f"{table.key}: C5 map is not a bijection onto A4")
    for x in range(12):
        for y in range(12):
            _require(images[table.product(x, y)] == _perm_product(images[x], images[y]),
                     f"{table.key}: C5 map is not a homomorphism")
    return 12 * 12 + 12


def _check_subdirect(
    table: GroupTable,
    witness: Any,
    verified: dict[tuple[int, int], GroupTable],
) -> int:
    _require(isinstance(witness, dict) and set(witness) == {"quotients"},
             f"{table.key}: R1 witness has wrong fields")
    quotients = witness["quotients"]
    _require(isinstance(quotients, list) and len(quotients) == 2,
             f"{table.key}: R1 needs exactly two quotient maps")
    kernels: list[set[int]] = []
    visited = 0
    for position, quotient in enumerate(quotients, 1):
        label = f"{table.key}: R1 quotient {position}"
        _require(isinstance(quotient, dict) and set(quotient) == {"target", "map"},
                 f"{label} has wrong fields")
        target_raw = quotient["target"]
        _require(isinstance(target_raw, list) and len(target_raw) == 2,
                 f"{label} has malformed target")
        target_key = (_int(target_raw[0], label), _int(target_raw[1], label))
        _require(target_key in verified,
                 f"{label} target {target_key} is not an already verified positive group")
        target = verified[target_key]
        _require(target.n < table.n, f"{label} target is not strictly smaller")
        mapping = quotient["map"]
        _require(isinstance(mapping, list) and len(mapping) == table.n,
                 f"{label} map has wrong size")
        _require(all(type(x) is int and 0 <= x < target.n for x in mapping),
                 f"{label} map value is out of range")
        _require(mapping[0] == 0, f"{label} does not preserve the identity")
        for x in range(table.n):
            for y in range(table.n):
                _require(mapping[table.product(x, y)] == target.product(mapping[x], mapping[y]),
                         f"{label} is not a homomorphism")
        visited += table.n ** 2
        _require(set(mapping) == set(range(target.n)), f"{label} is not surjective")
        kernel = {x for x, image in enumerate(mapping) if image == 0}
        _require(1 < len(kernel) < table.n, f"{label} kernel is not nontrivial and proper")
        kernels.append(kernel)
        visited += table.n
    _require(kernels[0] != kernels[1], f"{table.key}: R1 kernels are identical")
    _require(kernels[0] & kernels[1] == {0},
             f"{table.key}: R1 kernel intersection is nontrivial")
    return visited


def _check_criterion(
    table: GroupTable,
    verdict: str,
    witness: Any,
    verified: dict[tuple[int, int], GroupTable],
) -> int:
    if verdict == "C1-abelian":
        _require(witness == {}, f"{table.key}: C1 witness should be empty")
        return _check_abelian(table)
    if verdict == "C2-nilpotent2":
        _require(witness == {}, f"{table.key}: C2 witness should be empty")
        return _check_class_two(table)
    if verdict == "C3-AsemiE":
        return _check_split(table, witness)
    if verdict == "C4-dicyclic":
        return _check_dicyclic(table, witness)
    if verdict == "C6-KKindex2":
        return _check_index_two(table, witness)
    if verdict == "C5-A4":
        return _check_a4(table, witness)
    if verdict == "R1-subdirect":
        return _check_subdirect(table, witness, verified)
    raise AuditError(f"{table.key}: unknown positive verdict {verdict!r}")


def audit_certificate(
    header: dict[str, Any],
    records: Iterable[dict[str, Any]],
    coverage: dict[tuple[int, int], str],
) -> AuditReport:
    """Check the exact positive key set, all group tables, and all witnesses."""

    materialized = list(records)
    expected = {key: verdict for key, verdict in coverage.items() if verdict != "UNRESOLVED"}
    new_nonabelian = sum(
        1 for (order, _), verdict in expected.items()
        if 32 <= order <= 60 and verdict != "C1-abelian"
    )
    visited = 0
    verified: dict[tuple[int, int], GroupTable] = {}
    try:
        _require(isinstance(header, dict), "certificate header is not an object")
        _require(set(header) == {"schema", "max_order", "positive_groups"},
                 "certificate header has wrong fields")
        _require(header["schema"] == SCHEMA, f"certificate schema is not {SCHEMA}")
        _require(header["max_order"] == 60, "certificate max_order is not 60")
        _require(header["positive_groups"] == len(expected),
                 "certificate positive_groups disagrees with coverage table")

        by_key: dict[tuple[int, int], dict[str, Any]] = {}
        for record in materialized:
            _require(isinstance(record, dict), "certificate record is not an object")
            _require(set(record) == {"order", "id", "verdict", "mul", "witness"},
                     "certificate record has wrong fields")
            key = (_int(record["order"], "record order"), _int(record["id"], "record id"))
            _require(key not in by_key, f"duplicate certificate record {key}")
            by_key[key] = record
        _require(set(by_key) == set(expected),
                 "certificate keys are not exactly the positive coverage-table keys")

        for key in sorted(by_key):
            record = by_key[key]
            _require(record["verdict"] == expected[key],
                     f"{key}: certificate verdict disagrees with coverage table")
            table, group_visits = _check_group(record)
            visited += group_visits
            visited += _check_criterion(
                table, record["verdict"], record["witness"], verified)
            verified[key] = table
    except (AuditError, KeyError, TypeError) as exc:
        return AuditReport(
            errors=[str(exc)],
            visited=visited,
            positive_groups=len(expected),
            verified_groups=len(verified),
            new_nonabelian_groups=new_nonabelian,
        )
    return AuditReport(
        errors=[],
        visited=visited,
        positive_groups=len(expected),
        verified_groups=len(verified),
        new_nonabelian_groups=new_nonabelian,
    )


def _record(records: list[dict[str, Any]], key: tuple[int, int]) -> dict[str, Any]:
    return next(record for record in records if (record["order"], record["id"]) == key)


def _mutation_controls(
    header: dict[str, Any],
    records: list[dict[str, Any]],
    coverage: dict[tuple[int, int], str],
) -> list[Control]:
    """Perturb each load-bearing witness form in the claim's vocabulary."""

    mutations: list[tuple[str, str, Any]] = []

    missing = deepcopy(records)
    missing[:] = [r for r in missing if (r["order"], r["id"]) != (60, 3)]
    mutations.append(("missing positive row", "remove the positive group SmallGroup(60,3)", missing))

    abelian = deepcopy(records)
    _record(abelian, (6, 2))["mul"] = list(_record(abelian, (6, 1))["mul"])
    mutations.append(("nonabelian C1 table", "replace a C1 table by the nonabelian order-six table", abelian))

    class_two = deepcopy(records)
    _record(class_two, (16, 3))["mul"] = list(_record(class_two, (16, 7))["mul"])
    mutations.append(("class-three C2 table", "replace a C2 table by a class-three order-sixteen table", class_two))

    split = deepcopy(records)
    _record(split, (34, 1))["witness"]["complement"].pop()
    mutations.append(("incomplete C3 complement", "remove one element from a C3 complement", split))

    dicyclic = deepcopy(records)
    _record(dicyclic, (60, 3))["witness"]["x"] = 0
    mutations.append(("identity C4 generator", "replace the C4 cyclic generator by the identity", dicyclic))

    index_two = deepcopy(records)
    _record(index_two, (32, 15))["witness"]["subgroup"].pop()
    mutations.append(("incomplete C6 subgroup", "remove one element from the C6 index-two subgroup", index_two))

    a4 = deepcopy(records)
    images = _record(a4, (12, 3))["witness"]["permutation_images"]
    images[1], images[2] = images[2], images[1]
    mutations.append(("nonhomomorphic C5 map", "swap two images in the claimed A4 isomorphism", a4))

    subdirect = deepcopy(records)
    mapping = _record(subdirect, (60, 9))["witness"]["quotients"][0]["map"]
    mapping[1] = (mapping[1] + 1) % 12
    mutations.append(("broken R1 map", "change one image in a claimed quotient homomorphism", subdirect))

    forward = deepcopy(records)
    quotient = _record(forward, (36, 3))["witness"]["quotients"][0]
    quotient["target"] = [60, 9]
    quotient["map"] = [0] * 36
    mutations.append(("forward R1 target", "replace an R1 target by a later larger positive group", forward))

    unknown = deepcopy(records)
    quotient = _record(unknown, (60, 1))["witness"]["quotients"][0]
    quotient["target"] = [20, 3]
    quotient["map"] = [0] * 60
    mutations.append(("unknown R1 target", "replace an R1 target by an unresolved group", unknown))

    controls = []
    for name, mutation, damaged in mutations:
        controls.append(Control(
            name=name,
            mutation=mutation,
            rejected=not audit_certificate(header, damaged, coverage).ok,
        ))
    return controls


def main() -> int:
    coverage = load_coverage(COVERAGE_TABLE)
    header, records = load_certificate(CERTIFICATE)
    report = audit_certificate(header, records, coverage)
    controls = _mutation_controls(header, records, coverage)
    passed = report.ok and all(control.rejected for control in controls)
    detail = (
        f"verified {report.verified_groups}/{report.positive_groups} positive tables; "
        f"the order-32..60 nonabelian increment is {report.new_nonabelian_groups}; "
        f"visited {report.visited} finite table obligations"
    )
    if report.errors:
        detail += f"; first error: {report.errors[0]}"
    run = Run(script="scripts/ci/verify_small_group_witnesses.py")
    run.add(exhaustive(
        "positive SmallGroups witness audit through order 60",
        CLAIM_ID,
        passed=passed,
        universe=max(report.visited, 1),
        detail=detail,
        controls=controls,
        covers="claim",
        rationale=(
            "The row claims only that every positive table in the committed order-60 "
            "coverage table satisfies one named sufficient structural criterion.  The "
            "certificate keys are checked for exact equality with those positive rows; "
            "every multiplication table is checked as a group; and C1-C5/R1 are checked "
            "directly.  SmallGroups catalogue completeness and every residual row are "
            "explicitly outside this computed claim."
        ),
    ))
    return run.finish(VERDICT_FILE)


if __name__ == "__main__":
    raise SystemExit(main())
