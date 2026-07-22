#!/usr/bin/env python3
"""Write a reproducibility manifest for an agent or computational run."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import platform
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def command_output(args: list[str]) -> str | None:
    try:
        return subprocess.check_output(args, cwd=ROOT, text=True, stderr=subprocess.DEVNULL).strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for block in iter(lambda: handle.read(1 << 20), b""):
            digest.update(block)
    return digest.hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("task_dir", type=Path)
    parser.add_argument("--prompt", type=Path)
    parser.add_argument("--model", default="unspecified")
    parser.add_argument("--time-limit-minutes", type=int, default=0)
    parser.add_argument("--verification-reserve-percent", type=int, default=30)
    args = parser.parse_args()
    task_dir = args.task_dir.resolve()
    if not task_dir.is_dir():
        parser.error(f"not a directory: {task_dir}")
    prompt = args.prompt.resolve() if args.prompt else task_dir / "TASK.md"
    if not prompt.is_file():
        parser.error(f"prompt not found: {prompt}")
    manifest = {
        "schema": "gsh-run-manifest-v1",
        "created_utc": datetime.now(timezone.utc).isoformat(),
        "task_dir": str(task_dir.relative_to(ROOT) if task_dir.is_relative_to(ROOT) else task_dir),
        "prompt": str(prompt.relative_to(ROOT) if prompt.is_relative_to(ROOT) else prompt),
        "prompt_sha256": sha256(prompt),
        "git_commit": command_output(["git", "rev-parse", "HEAD"]),
        "git_dirty": bool(command_output(["git", "status", "--porcelain"])),
        "model": args.model,
        "time_limit_minutes": args.time_limit_minutes,
        "verification_reserve_percent": args.verification_reserve_percent,
        "lean_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "python": platform.python_version(),
        "platform": platform.platform(),
        "commands_to_rerun": [],
        "input_files": [],
        "output_files": [],
        "notes": "",
    }
    output = task_dir / "manifest.json"
    output.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(output)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
