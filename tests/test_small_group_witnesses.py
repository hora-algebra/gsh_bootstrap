"""Acceptance and mutation tests for the order-60 positive witness audit."""

from __future__ import annotations

from copy import deepcopy
import hashlib
from pathlib import Path
import re
import unittest

from scripts.ci.verify_small_group_witnesses import (
    CERTIFICATE,
    COVERAGE_TABLE,
    audit_certificate,
    load_certificate,
    load_coverage,
)

ROOT = Path(__file__).resolve().parents[1]
MANIFEST = ROOT / "data" / "experiments" / "small_group_coverage_le60.md"


class SmallGroupWitnessTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.header, cls.records = load_certificate(CERTIFICATE)
        cls.coverage = load_coverage(COVERAGE_TABLE)

    def audit(self, records=None):
        return audit_certificate(
            self.header,
            self.records if records is None else records,
            self.coverage,
        )

    def record(self, records, key):
        return next(
            record for record in records
            if (record["order"], record["id"]) == key
        )

    def test_all_positive_groups_are_independently_verified(self) -> None:
        report = self.audit()
        self.assertEqual(report.errors, [])
        self.assertEqual(report.positive_groups, 281)
        self.assertEqual(report.verified_groups, 281)
        self.assertEqual(report.new_nonabelian_groups, 138)
        self.assertGreater(report.visited, 1_000_000)

    def test_manifest_hashes_are_current(self) -> None:
        pattern = re.compile(r"^\| `([^`]+)` \| `([0-9a-f]{64})` \|$")
        recorded = dict(
            match.groups()
            for line in MANIFEST.read_text(encoding="utf-8").splitlines()
            if (match := pattern.match(line))
        )
        required = {
            "scripts/gap/coverage_le60.g",
            "data/experiments/coverage_le60.tsv",
            "data/experiments/coverage_le60_witnesses.jsonl",
            "scripts/ci/verify_small_group_witnesses.py",
            "tests/test_small_group_witnesses.py",
            "tests/test_coverage_le60.py",
            "data/verdicts/small_group_coverage_le60.json",
        }
        self.assertEqual(set(recorded), required)
        for relative, expected in sorted(recorded.items()):
            with self.subTest(artifact=relative):
                actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
                self.assertEqual(actual, expected)

    def test_missing_new_positive_group_is_rejected(self) -> None:
        damaged = [
            record for record in deepcopy(self.records)
            if (record["order"], record["id"]) != (60, 3)
        ]
        self.assertFalse(audit_certificate(
            self.header, damaged, self.coverage).ok)

    def test_group_axioms_reject_a_single_corrupted_table_cell(self) -> None:
        damaged = deepcopy(self.records)
        self.record(damaged, (5, 1))["mul"][1] = 0
        self.assertFalse(self.audit(damaged).ok)

    def test_abelian_checker_rejects_a_nonabelian_table(self) -> None:
        damaged = deepcopy(self.records)
        self.record(damaged, (6, 2))["mul"] = list(
            self.record(damaged, (6, 1))["mul"])
        self.assertFalse(self.audit(damaged).ok)

    def test_class_two_checker_rejects_a_class_three_group(self) -> None:
        damaged = deepcopy(self.records)
        self.record(damaged, (16, 3))["mul"] = list(
            self.record(damaged, (16, 7))["mul"])
        self.assertFalse(self.audit(damaged).ok)

    def test_split_witness_rejects_a_missing_complement_element(self) -> None:
        damaged = deepcopy(self.records)
        witness = self.record(damaged, (34, 1))["witness"]
        witness["complement"].pop()
        self.assertFalse(self.audit(damaged).ok)

    def test_dicyclic_witness_rejects_the_identity_as_generator(self) -> None:
        damaged = deepcopy(self.records)
        self.record(damaged, (60, 3))["witness"]["x"] = 0
        self.assertFalse(self.audit(damaged).ok)

    def test_a4_witness_rejects_a_nonhomomorphic_bijection(self) -> None:
        damaged = deepcopy(self.records)
        images = self.record(damaged, (12, 3))["witness"]["permutation_images"]
        images[1], images[2] = images[2], images[1]
        self.assertFalse(self.audit(damaged).ok)

    def test_subdirect_witness_rejects_a_broken_quotient_map(self) -> None:
        damaged = deepcopy(self.records)
        mapping = self.record(damaged, (60, 9))["witness"]["quotients"][0]["map"]
        mapping[1] = (mapping[1] + 1) % 12
        self.assertFalse(self.audit(damaged).ok)

    def test_subdirect_witness_rejects_a_forward_reference(self) -> None:
        damaged = deepcopy(self.records)
        quotient = self.record(damaged, (36, 3))["witness"]["quotients"][0]
        quotient["target"] = [60, 9]
        quotient["map"] = [0] * 36
        self.assertFalse(self.audit(damaged).ok)

    def test_subdirect_witness_allows_distinct_maps_to_the_same_target(self) -> None:
        record = self.record(self.records, (48, 42))
        quotients = record["witness"]["quotients"]
        self.assertEqual(quotients[0]["target"], quotients[1]["target"])
        self.assertNotEqual(quotients[0]["map"], quotients[1]["map"])
        self.assertTrue(self.audit().ok)

    def test_unknown_group_cannot_be_used_as_a_subdirect_target(self) -> None:
        damaged = deepcopy(self.records)
        quotient = self.record(damaged, (60, 1))["witness"]["quotients"][0]
        quotient["target"] = [20, 3]
        quotient["map"] = [0] * 60
        self.assertFalse(self.audit(damaged).ok)


if __name__ == "__main__":
    unittest.main()
