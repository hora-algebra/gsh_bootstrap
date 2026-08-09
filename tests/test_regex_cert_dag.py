"""Tests for the shared-DAG certificate schema (`gsh-regex-certificate-v2`).

The load-bearing test is `test_dag_agrees_with_its_own_unfolding`: it builds a
DAG, unfolds it into the v1 tree the DAG denotes, and checks that the two give
the same height and the same automaton. That is the soundness argument in
`tools/regex_cert.py` executed on a concrete instance rather than asserted.

Everything else is a negative control. A checker that accepted a cyclic table,
a dangling reference, or an understated height would report success on
certificates that denote nothing, so each of those is given its own test.
"""

from __future__ import annotations

import copy
import unittest

from tools.regex_cert import (
    CertificateError,
    check_certificate,
    dag_star_height,
    parse_regex_dag,
)


def all_words_dfa(alphabet: list[str]) -> dict:
    """One-state DFA accepting every word."""

    return {
        "states": ["q"],
        "start": "q",
        "accept": ["q"],
        "transitions": {"q": {symbol: "q" for symbol in alphabet}},
    }


def dag_certificate(alphabet: list[str], nodes: dict, root: str, height: int,
                    target: dict) -> dict:
    return {
        "schema": "gsh-regex-certificate-v2",
        "alphabet": alphabet,
        "claimed_height": height,
        "expression_dag": {"root": root, "nodes": nodes},
        "target_dfa": target,
    }


def unfold(nodes: dict, node_id: str) -> dict:
    """The v1 tree a DAG node denotes. Exponential by construction."""

    node = nodes[node_id]
    op = node["op"]
    if op in {"empty", "eps"}:
        return {"op": op}
    if op == "letter":
        return {"op": "letter", "value": node["value"]}
    if op in {"compl", "star"}:
        return {"op": op, "arg": unfold(nodes, node["arg"])}
    return {"op": op, "args": [unfold(nodes, child) for child in node["args"]]}


#: `even` is the height-one even-number-of-`a` language, shared by both arms of
#: the union, so the DAG has one copy where the tree has two.
SHARED_NODES = {
    "a": {"op": "letter", "value": "a"},
    "b": {"op": "letter", "value": "b"},
    "aa": {"op": "concat", "args": ["a", "a"]},
    "even": {"op": "star", "arg": "aa"},
    "even_b": {"op": "concat", "args": ["even", "b"]},
    "root": {"op": "union", "args": ["even", "even_b"]},
}


class SharedDagTests(unittest.TestCase):
    def test_dag_agrees_with_its_own_unfolding(self) -> None:
        alphabet = ["a", "b"]
        # `(aa)* ∪ (aa)*b`, written out by hand: an even run of `a`, optionally
        # followed by a single closing `b`. Writing the target independently
        # makes the test stronger than "the two readings agree with each other".
        target = {
            "states": ["even", "odd", "closed", "dead"],
            "start": "even",
            "accept": ["even", "closed"],
            "transitions": {
                "even": {"a": "odd", "b": "closed"},
                "odd": {"a": "even", "b": "dead"},
                "closed": {"a": "dead", "b": "dead"},
                "dead": {"a": "dead", "b": "dead"},
            },
        }
        dag = dag_certificate(alphabet, SHARED_NODES, "root", 1, target)
        tree = {
            "schema": "gsh-regex-certificate-v1",
            "alphabet": alphabet,
            "claimed_height": 1,
            "expression": unfold(SHARED_NODES, "root"),
            "target_dfa": target,
        }
        from_dag = check_certificate(dag)
        from_tree = check_certificate(tree)
        self.assertTrue(from_dag.ok, from_dag.witness)
        self.assertTrue(from_tree.ok, from_tree.witness)
        self.assertEqual(from_dag.actual_height, from_tree.actual_height)
        self.assertEqual(from_dag.expression_states, from_tree.expression_states)
        self.assertEqual(from_dag.expression_nodes, len(SHARED_NODES))
        self.assertIsNone(from_tree.expression_nodes)

    def test_sharing_beats_an_unfolding_no_machine_could_write(self) -> None:
        # n_{k+1} = concat(n_k, n_k) doubles the tree at every level while
        # adding one DAG node. Each n_k denotes `a*`, so the automaton stays at
        # one state and only the representation explodes.
        depth = 40
        nodes: dict = {
            "a": {"op": "letter", "value": "a"},
            "s0": {"op": "star", "arg": "a"},
        }
        for k in range(depth):
            nodes[f"s{k + 1}"] = {"op": "concat", "args": [f"s{k}", f"s{k}"]}
        root = f"s{depth}"

        tree_nodes = 2  # star over letter
        for _ in range(depth):
            tree_nodes = 1 + 2 * tree_nodes
        self.assertGreater(tree_nodes, 10 ** 12)
        self.assertEqual(len(nodes), depth + 2)

        report = check_certificate(
            dag_certificate(["a"], nodes, root, 1, all_words_dfa(["a"]))
        )
        self.assertTrue(report.ok, report.witness)
        self.assertEqual(report.actual_height, 1)
        self.assertEqual(report.expression_states, 1)
        self.assertEqual(report.expression_nodes, depth + 2)

    def test_height_is_the_deepest_nesting_not_the_deepest_path(self) -> None:
        # Sharing a starred node under another star must still count 2.
        nodes = {
            "a": {"op": "letter", "value": "a"},
            "s": {"op": "star", "arg": "a"},
            "ss": {"op": "star", "arg": "s"},
            "root": {"op": "union", "args": ["s", "ss"]},
        }
        dag = parse_regex_dag({"root": "root", "nodes": nodes}, ["a"])
        self.assertEqual(dag_star_height(dag), 2)
        with self.assertRaises(CertificateError) as caught:
            check_certificate(
                dag_certificate(["a"], nodes, "root", 1, all_words_dfa(["a"]))
            )
        self.assertIn("star height 2", str(caught.exception))


class CommittedCertificateTests(unittest.TestCase):
    """The one v2 certificate in the repository, pinned.

    `scripts/check.sh` already re-checks every file in `data/certificates/`, so
    this test is not the gate. It pins the numbers, so that a change which
    silently makes the certificate describe a different language, or a
    different-sized object, fails here with the numbers visible rather than
    passing quietly.
    """

    def test_c7c3_sub9_identity_fibre(self) -> None:
        from pathlib import Path

        from tools.regex_cert import load_and_check

        root = Path(__file__).resolve().parents[1]
        report = load_and_check(
            root / "data/certificates/height1_c7c3_sub9_identity.json"
        )
        self.assertTrue(report.ok, report.witness)
        self.assertEqual(report.actual_height, 1)
        self.assertEqual(report.expression_nodes, 11470)
        # The target is the word-problem automaton over nine letters: one state
        # per group element plus the sink the sub-alphabet cannot leave.
        self.assertEqual(report.target_states, 21)
        self.assertEqual(report.expression_states, 21)


class DagRejectionTests(unittest.TestCase):
    """Each test corrupts a valid certificate in exactly one way."""

    def valid(self) -> dict:
        return dag_certificate(
            ["a"],
            {
                "a": {"op": "letter", "value": "a"},
                "root": {"op": "star", "arg": "a"},
            },
            "root",
            1,
            all_words_dfa(["a"]),
        )

    def test_the_valid_certificate_passes(self) -> None:
        self.assertTrue(check_certificate(self.valid()).ok)

    def test_cycle_is_rejected(self) -> None:
        bad = self.valid()
        bad["expression_dag"]["nodes"]["a"] = {"op": "star", "arg": "root"}
        with self.assertRaises(CertificateError) as caught:
            check_certificate(bad)
        self.assertIn("cycle", str(caught.exception))

    def test_self_loop_is_rejected(self) -> None:
        # `a` is kept as a second operand so that the self-loop is the only
        # defect; pointing the root only at itself would orphan `a` and the
        # reachability check would fire first, testing the wrong thing.
        bad = self.valid()
        bad["expression_dag"]["nodes"]["root"] = {"op": "union", "args": ["a", "root"]}
        with self.assertRaises(CertificateError) as caught:
            check_certificate(bad)
        self.assertIn("cycle", str(caught.exception))

    def test_dangling_reference_is_rejected(self) -> None:
        bad = self.valid()
        bad["expression_dag"]["nodes"]["root"] = {"op": "star", "arg": "missing"}
        with self.assertRaises(CertificateError) as caught:
            check_certificate(bad)
        self.assertIn("dangling", str(caught.exception))

    def test_unreachable_node_is_rejected(self) -> None:
        bad = self.valid()
        bad["expression_dag"]["nodes"]["orphan"] = {"op": "letter", "value": "a"}
        with self.assertRaises(CertificateError) as caught:
            check_certificate(bad)
        self.assertIn("unreachable", str(caught.exception))

    def test_root_outside_the_table_is_rejected(self) -> None:
        bad = self.valid()
        bad["expression_dag"]["root"] = "nowhere"
        with self.assertRaises(CertificateError):
            check_certificate(bad)

    def test_letter_outside_the_alphabet_is_rejected(self) -> None:
        bad = self.valid()
        bad["expression_dag"]["nodes"]["a"] = {"op": "letter", "value": "z"}
        with self.assertRaises(CertificateError) as caught:
            check_certificate(bad)
        self.assertIn("not in the alphabet", str(caught.exception))

    def test_unknown_operator_is_rejected(self) -> None:
        bad = self.valid()
        bad["expression_dag"]["nodes"]["root"] = {"op": "intersect", "args": ["a"]}
        with self.assertRaises(CertificateError):
            check_certificate(bad)

    def test_wrong_target_returns_a_shortest_witness(self) -> None:
        bad = self.valid()
        bad["target_dfa"]["accept"] = []
        report = check_certificate(bad)
        self.assertFalse(report.ok)
        self.assertEqual(report.witness, ())

    def test_v1_certificate_may_not_carry_a_dag(self) -> None:
        bad = self.valid()
        bad["schema"] = "gsh-regex-certificate-v1"
        with self.assertRaises(CertificateError) as caught:
            check_certificate(bad)
        self.assertIn("expression", str(caught.exception))

    def test_v2_certificate_may_not_carry_a_tree(self) -> None:
        bad = copy.deepcopy(self.valid())
        del bad["expression_dag"]
        bad["expression"] = {"op": "star", "arg": {"op": "letter", "value": "a"}}
        with self.assertRaises(CertificateError) as caught:
            check_certificate(bad)
        self.assertIn("expression_dag", str(caught.exception))

    def test_unknown_schema_is_rejected(self) -> None:
        bad = self.valid()
        bad["schema"] = "gsh-regex-certificate-v3"
        with self.assertRaises(CertificateError):
            check_certificate(bad)


if __name__ == "__main__":
    unittest.main()
