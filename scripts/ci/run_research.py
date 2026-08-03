#!/usr/bin/env python3
"""Re-run the research scripts, so that a broken one is noticed.

Until now `scripts/check.sh` ran five things and none of them was a research
script.  The twenty-five programs that produced the recorded mathematical
results were run once by hand, their output was transcribed into
`CLAIMS_LEDGER.md`, and after that only the transcription was ever checked.  A
script could be broken, or deleted, and CI stayed green:
`closure_lemmas_check.py` had in fact been un-runnable from the repository root
for some time, because it never inserted the root on `sys.path`, and nothing
noticed.

**What this catches, and what it does not.**  It catches a script that crashes,
that stops importing, that hangs, or that starts exiting non-zero.  It does not
check that a script's *verdict* is unchanged, because most of these scripts
print a human-readable verdict and exit 0 either way — and several of the
"FAIL" lines they print are intended negative results, which is to say
mathematics rather than regression.  Turning those into exit codes one script at
a time is what `data/verdicts/PENDING.md` tracks; this runner is the floor
underneath that work, not a substitute for it.

Two tiers, because the slow half is twelve times the fast half:

  --fast   runs on every push, alongside the rest of `check.sh`
  --slow   the long ones, for the scheduled job
  --all    both

Timings are measured, not assumed; `--time` reprints them so the tiers can be
rebalanced when a script grows.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESEARCH = ROOT / "scripts" / "research"

#: Measured on 2026-07-25; anything at or above this many seconds goes to the
#: scheduled job. The split is by observation rather than by topic, so a script
#: that gets slower is moved rather than silently making every push slower.
SLOW_SECONDS = 6.0
SLOW = {
    "a4_attempt.py",
    "a5_check.py",
    "c7c3_full_alphabet.py",
    "f20_block_decomposition.py",
    "f20_fibration_geometry.py",
    "f20_subalphabet_obstruction.py",
    "a4_full3.py",
    "a4_first_return_token.py",
}

#: A script whose exit status is not yet a verdict. Listed so the exception is
#: visible: these are re-run for crashes only, and moving one out of this set
#: means its exit code has become meaningful.
TIMEOUT_SECONDS = 300


def scripts(tier: str) -> list[Path]:
    every = sorted(RESEARCH.glob("*.py"))
    if tier == "all":
        return every
    slow = tier == "slow"
    return [path for path in every if (path.name in SLOW) == slow]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--tier", choices=("fast", "slow", "all"), default="fast")
    parser.add_argument("--time", action="store_true", help="print each runtime")
    args = parser.parse_args()

    selected = scripts(args.tier)
    print(f"Re-running {len(selected)} research script(s) [{args.tier}]")
    failures: list[str] = []
    total = 0.0
    for path in selected:
        start = time.monotonic()
        try:
            done = subprocess.run(
                [sys.executable, str(path.relative_to(ROOT))],
                cwd=ROOT,
                capture_output=True,
                text=True,
                timeout=TIMEOUT_SECONDS,
            )
            code: int | str = done.returncode
            tail = done.stdout.strip().splitlines()[-1:] or done.stderr.strip().splitlines()[-3:]
        except subprocess.TimeoutExpired:
            code, tail = "timeout", []
        elapsed = time.monotonic() - start
        total += elapsed
        ok = code == 0
        if not ok:
            failures.append(f"{path.name} (exit {code})")
            for line in tail:
                print(f"      {line}")
        stamp = f" {elapsed:5.1f}s" if args.time else ""
        print(f"  [{'ok' if ok else 'FAIL'}]{stamp} {path.name}")

    print(f"\n{len(selected) - len(failures)}/{len(selected)} ran clean in {total:.1f}s")
    if failures:
        print("FAILED: " + ", ".join(failures), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
