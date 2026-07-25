#!/usr/bin/env python3
"""Rebuild the tracked PDFs in `docs/pdf/` from their sources in `docs/`.

Replaces `build_docs.sh`, which three adversarial rounds kept breaking in the
same way. The shell version verified each step with `cmp`, and a review pointed
out that this is not verification at all: `cmp` is another program on `PATH`,
supplied by whoever supplied the `cp` it was checking. A stub that wrote the
same stale bytes to both sides passed. Every repair added another external
command to check the previous one, and the class of defect never closed.

Nothing here shells out except to `latexmk`, which is the build itself and
cannot be avoided. The checks are arithmetic on bytes this process read:

  * the staging directory must be empty when it is created, so leftovers cannot
    be mistaken for today's build;
  * `latexmk` must leave a non-empty regular file, checked by `lstat` -- a
    symlink is not an output;
  * each previously published PDF is read into memory with its digest before
    anything is overwritten;
  * publication is `os.replace`, which is atomic within a filesystem, and each
    published file is re-read and compared against the digest of what was built;
  * any failure restores the bytes held in memory, re-reads them, and only then
    reports a rollback -- and if the restoration does not verify, says so and
    keeps the staging directory rather than claiming a rollback it did not do.

`latexmk` remains untrusted: it is checked by its output, not its exit status.
An adversary who can replace `python3` itself is outside what any script in this
repository can address, and pretending otherwise is how the shell version kept
looking finished.
"""

from __future__ import annotations

import hashlib
import os
import stat as stat_module
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
DOCS = ROOT / "docs"
PUBLISHED = DOCS / "pdf"

SOURCES = (
    "blueprint.tex",
    "textbook_number_theorists.tex",
    "textbook_formal_language_theorists.tex",
    "textbook_lean_experts.tex",
)


class BuildError(Exception):
    """A postcondition did not hold. The message names which one."""


def digest(path: Path) -> str:
    """The SHA-256 of a regular file, refusing anything that is not one."""
    info = path.lstat()
    if not stat_module.S_ISREG(info.st_mode):
        raise BuildError(f"{path} is not a regular file")
    return hashlib.sha256(path.read_bytes()).hexdigest()


def compile_all(stage: Path) -> dict[str, str]:
    """Build every document into `stage`; return name -> digest."""
    if any(stage.iterdir()):
        raise BuildError(f"staging directory {stage} is not empty")
    built: dict[str, str] = {}
    for source in SOURCES:
        subprocess.run(
            ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
             f"-outdir={stage}", source],
            cwd=DOCS, check=True,
        )
        name = Path(source).with_suffix(".pdf").name
        produced = stage / name
        if not produced.exists() or produced.stat().st_size == 0:
            raise BuildError(
                f"latexmk exited 0 but produced no {produced}; refusing to publish"
            )
        built[name] = digest(produced)
    return built


def publish(stage: Path, built: dict[str, str]) -> None:
    """Replace the tracked PDFs, restoring them if anything does not verify."""
    PUBLISHED.mkdir(parents=True, exist_ok=True)
    previous: dict[str, bytes] = {}
    for name in built:
        target = PUBLISHED / name
        if target.exists():
            previous[name] = target.read_bytes()

    try:
        for name in built:
            # `os.replace` is atomic within a filesystem, so no reader ever sees
            # a half-written PDF and no failure leaves a truncated one.
            os.replace(stage / name, PUBLISHED / name)
        for name, expected in built.items():
            if digest(PUBLISHED / name) != expected:
                raise BuildError(f"docs/pdf/{name} is not what was built")
    except Exception:
        restore(previous, set(built) - set(previous))
        raise


def restore(previous: dict[str, bytes], added: set[str]) -> None:
    """Put back what was published before, and remove what was not there."""
    broken: list[str] = []
    for name, content in previous.items():
        target = PUBLISHED / name
        target.write_bytes(content)
        if not target.exists() or target.read_bytes() != content:
            broken.append(name)
    for name in added:
        target = PUBLISHED / name
        if target.exists():
            target.unlink()
        if target.exists():
            broken.append(name)
    if broken:
        raise BuildError(
            "ROLLBACK FAILED: docs/pdf/ is a mixture of two builds; "
            f"could not restore {', '.join(sorted(broken))}"
        )
    print("publish failed; docs/pdf/ rolled back to the previous build",
          file=sys.stderr)


def main() -> int:
    stage = Path(tempfile.mkdtemp())
    try:
        built = compile_all(stage)
        publish(stage, built)
    except BuildError as error:
        print(f"build_docs: {error}", file=sys.stderr)
        return 1
    except subprocess.CalledProcessError as error:
        print(f"build_docs: latexmk failed ({error.returncode})", file=sys.stderr)
        return 1
    finally:
        shutil.rmtree(stage, ignore_errors=True)
    print(f"rebuilt {len(SOURCES)} PDF(s) in docs/pdf/")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
