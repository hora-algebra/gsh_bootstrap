#!/usr/bin/env python3
"""Create a durable agent task packet from the project template."""

from __future__ import annotations

import argparse
from pathlib import Path
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
TEMPLATE = ROOT / "prompts/templates/TASK_PACKET.md"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("slug", help="lowercase letters, digits, and hyphens")
    parser.add_argument("--title", default="")
    args = parser.parse_args()
    if not re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", args.slug):
        parser.error("slug must match [a-z0-9]+(-[a-z0-9]+)*")
    destination = ROOT / "tasks" / args.slug
    if destination.exists():
        parser.error(f"task already exists: {destination}")
    destination.mkdir(parents=True)
    text = TEMPLATE.read_text(encoding="utf-8")
    if args.title:
        text = f"# {args.title}\n\n" + "\n".join(text.splitlines()[1:]).lstrip()
    (destination / "TASK.md").write_text(text, encoding="utf-8")
    for name, heading in [
        ("CONTEXT.md", "Context Packet"),
        ("SOURCES.md", "Primary Sources"),
        ("ACCEPTANCE.md", "Acceptance Tests"),
        ("KNOWN_FAILURES.md", "Known Failures"),
        ("CHECKPOINT.md", "Current Checkpoint"),
    ]:
        (destination / name).write_text(f"# {heading}\n\n", encoding="utf-8")
    print(destination)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
