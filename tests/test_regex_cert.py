from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from tools.regex_cert import CertificateError, check_certificate, load_and_check

ROOT = Path(__file__).resolve().parents[1]


class RegexCertificateTests(unittest.TestCase):
    def test_height_zero_ends_in_a(self) -> None:
        report = load_and_check(ROOT / "data/certificates/height0_ends_a.json")
        self.assertTrue(report.ok)
        self.assertEqual(report.actual_height, 0)
        self.assertEqual(report.expression_states, 2)

    def test_height_one_even_number_of_a(self) -> None:
        report = load_and_check(ROOT / "data/certificates/height1_even_a.json")
        self.assertTrue(report.ok)
        self.assertEqual(report.actual_height, 1)
        self.assertEqual(report.expression_states, 2)

    def test_wrong_target_returns_shortest_witness(self) -> None:
        path = ROOT / "data/certificates/height0_ends_a.json"
        data = json.loads(path.read_text(encoding="utf-8"))
        bad = copy.deepcopy(data)
        bad["target_dfa"]["accept"] = ["q0"]
        report = check_certificate(bad)
        self.assertFalse(report.ok)
        self.assertIsNotNone(report.witness)

    def test_false_height_claim_is_rejected(self) -> None:
        path = ROOT / "data/certificates/height1_even_a.json"
        data = json.loads(path.read_text(encoding="utf-8"))
        data["claimed_height"] = 0
        with self.assertRaises(CertificateError):
            check_certificate(data)

    def test_empty_alphabet(self) -> None:
        data = {
            "schema": "gsh-regex-certificate-v1",
            "alphabet": [],
            "claimed_height": 0,
            "expression": {"op": "eps"},
            "target_dfa": {
                "states": ["q"],
                "start": "q",
                "accept": ["q"],
                "transitions": {"q": {}},
            },
        }
        self.assertTrue(check_certificate(data).ok)


if __name__ == "__main__":
    unittest.main()
