"""Argument handling of `scripts/research/metacyclic_full_alphabet.py`.

The script has to serve two callers that pull in opposite directions.
`scripts/ci/run_research.py` invokes every research script with **no
arguments** and reads the exit code, so the no-argument run must succeed; and
the reason the script exists is to run an arbitrary member of the family, so
`--p/--q` must work.

Making `--target` an argparse default satisfies the first and silently kills
the second: `args.target` is then never `None`, the `--p/--q` branch becomes
unreachable, and `--p 13 --q 3` is rejected for "contradicting" a target the
caller never named.  That is exactly what happened, so the resolution order is
pinned here rather than left to be rediscovered.

These tests exercise argument resolution only.  They stop before the expensive
sections, so the file stays cheap enough to live in the fast tier while the
script itself is in `SLOW`.
"""

from __future__ import annotations

import subprocess
import sys
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "research" / "metacyclic_full_alphabet.py"

#: The header line the script prints once its parameters are resolved, which is
#: what these tests read.  Cheaper and less brittle than importing the module.
HEADER = "target "


def run(*args: str, timeout: int = 120) -> subprocess.CompletedProcess:
    return subprocess.run(
        [sys.executable, str(SCRIPT), *args],
        capture_output=True, text=True, timeout=timeout, cwd=ROOT,
    )


def header_of(result: subprocess.CompletedProcess) -> str:
    for line in result.stdout.splitlines():
        if line.startswith(HEADER):
            return line
    return ""


class MetacyclicCliTest(unittest.TestCase):
    def test_no_arguments_resolves_to_the_positive_control(self) -> None:
        # What run_research.py invokes.  It must be (7, 3), because that is the
        # instance whose answer c7c3_full_alphabet.py already recorded.
        result = run("--exhaustive-length", "1", "--sweep", "10")
        self.assertIn("p=7, q=3, r=2", header_of(result))

    def test_explicit_p_and_q_are_not_shadowed(self) -> None:
        # The regression: with --target defaulted this raised
        # "--p 13 contradicts --target C_7:C_3".
        result = run("--p", "13", "--q", "3", "--exhaustive-length", "1",
                     "--sweep", "10")
        self.assertIn("p=13, q=3", header_of(result))
        self.assertNotIn("contradicts", result.stdout + result.stderr)

    def test_generator_is_derived_and_has_order_exactly_q(self) -> None:
        # r = 3 is the order-3 element of (Z/13)^*; the point of deriving it
        # rather than tabulating it is that a wrong r would still "work".
        result = run("--p", "13", "--q", "3", "--exhaustive-length", "1",
                     "--sweep", "10")
        self.assertIn("r=3", header_of(result))
        self.assertIn("(1, 3, 9)", header_of(result))

    def test_named_target_and_contradicting_p_is_refused(self) -> None:
        result = run("--target", "C13C3", "--p", "7")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("contradicts", result.stdout + result.stderr)

    def test_r_override_of_the_wrong_order_is_refused(self) -> None:
        # 2 has order 12 mod 13, not 3.  A generator of the wrong order would
        # define a different group while every downstream section still ran.
        result = run("--p", "13", "--q", "3", "--r", "2")
        self.assertNotEqual(result.returncode, 0)

    def test_non_invertible_generator_is_refused_and_does_not_hang(self) -> None:
        # r = 0 has no multiplicative order, and the naive order loop never
        # terminates on it: 0 * 0 % p stays 0.  Before the guard this hung, and
        # a hang is the one failure a caller cannot tell from a slow run -- the
        # timeout below is the assertion, not a safety net.
        for value in ("0", "13", "-13"):
            with self.subTest(r=value):
                result = run("--p", "13", "--q", "3", "--r", value, timeout=30)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("not invertible", result.stdout + result.stderr)

    def test_unknown_target_is_refused(self) -> None:
        result = run("--target", "C99C7")
        self.assertNotEqual(result.returncode, 0)

    def test_composite_phase_target_still_fails(self) -> None:
        # F_20 has q = 4.  F20-FULL-OBS-01 establishes that this mechanism
        # fails there, so a zero exit status would mean the generalization had
        # broken a COMPUTED row rather than extended anything.
        result = run("--target", "F20")
        self.assertEqual(result.returncode, 1)
        self.assertIn("exact total=291; certified=0; failed=291", result.stdout)
        self.assertIn("witness=g(e=2,b=0)", result.stdout)


if __name__ == "__main__":
    unittest.main()
