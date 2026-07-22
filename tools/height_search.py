"""Bottom-up synthesis search for height-≤1 generalized regular expressions.

The search enumerates generalized regular expressions over a fixed alphabet in
order of increasing syntactic size (AST node count), restricted to syntactic
star height ≤ 1: a star may only be applied to a star-free (height-0)
subexpression.  Every enumerated expression is compiled to a canonical minimal
DFA with the exact constructions of ``tools.regex_cert``, and expressions are
deduplicated by language: a new expression is kept only if its language is new,
or if it realizes an already-seen language at strictly smaller syntactic
height (height-0 realizations matter because only they may go under a star).

The search stops as soon as the target language appears, and emits a
``gsh-regex-certificate-v1`` certificate that is re-verified independently by
``tools.regex_cert.check_certificate``.

Honesty contract (README rule 1): a completed search up to ``max_size`` that
does *not* find the target proves only "no height-≤1 expression of size ≤
max_size in this grammar"; it is never evidence of star height ≥ 2.  If
``max_states`` pruning discarded any expression, even that bounded statement
no longer holds, and the result reports the search as incomplete.
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Hashable

from tools.regex_cert import (
    DFA,
    GRegex,
    _concat,
    _product,
    _star,
    check_certificate,
    compile_regex,
)
from tools.targets import TARGETS, build_target

DfaKey = tuple[Hashable, ...]


def dfa_key(machine: DFA) -> DfaKey:
    """Hashable identity of a canonical minimal DFA (language identity)."""

    canonical = machine.canonical()
    return (
        canonical.alphabet,
        len(canonical.states),
        tuple(sorted(canonical.accept)),
        tuple(
            canonical.step(state, symbol)
            for state in sorted(canonical.states)
            for symbol in canonical.alphabet
        ),
    )


def format_regex(expr: GRegex) -> str:
    """Human-readable rendering: union `|` < concat (juxtaposition) < `*`/`~`."""

    def render(node: GRegex, parent_level: int) -> str:
        if node.op == "empty":
            text, level = "0", 3
        elif node.op == "eps":
            text, level = "e", 3
        elif node.op == "letter":
            text, level = str(node.value), 3
        elif node.op == "star":
            text, level = render(node.args[0], 3) + "*", 2
        elif node.op == "compl":
            text, level = "~" + render(node.args[0], 3), 2
        elif node.op == "concat":
            text, level = "".join(render(arg, 1) for arg in node.args), 1
        elif node.op == "union":
            text, level = "|".join(render(arg, 0) for arg in node.args), 0
        else:
            raise AssertionError(f"unknown op {node.op}")
        return f"({text})" if level < parent_level else text

    return render(expr, 0)


def regex_size(expr: GRegex) -> int:
    """AST node count; the enumeration order of the search."""

    return 1 + sum(regex_size(arg) for arg in expr.args)


@dataclass(frozen=True)
class Entry:
    expr: GRegex
    dfa: DFA
    height: int


@dataclass
class SearchResult:
    found: bool
    target_states: int
    max_size: int
    completed_size: int
    languages_seen: int
    pruned: int
    elapsed_seconds: float
    expr: GRegex | None = None
    height: int | None = None
    size: int | None = None

    @property
    def complete(self) -> bool:
        """True when the negative statement "no expr of size ≤ completed_size" holds."""

        return self.pruned == 0

    def summary(self) -> str:
        if self.found:
            assert self.expr is not None
            return (
                f"FOUND height={self.height} size={self.size}: {format_regex(self.expr)}"
            )
        qualifier = "complete" if self.complete else f"INCOMPLETE (pruned {self.pruned})"
        return (
            f"not found up to size {self.completed_size} ({qualifier}); "
            "this is a search result, not a lower bound"
        )


def _new_layer(
    size: int,
    layers: dict[int, list[Entry]],
    alphabet: tuple[str, ...],
    max_states: int,
) -> tuple[list[Entry], int]:
    """Yield candidate entries of the given size (before language dedup)."""

    candidates: list[Entry] = []
    pruned = 0

    def emit(expr: GRegex, dfa: DFA, height: int) -> None:
        nonlocal pruned
        if max_states and len(dfa.states) > max_states:
            pruned += 1
            return
        candidates.append(Entry(expr, dfa, height))

    if size == 1:
        for expr in [GRegex("empty"), GRegex("eps")] + [
            GRegex("letter", value=letter) for letter in alphabet
        ]:
            emit(expr, compile_regex(expr, alphabet), 0)
        return candidates, pruned

    for entry in layers.get(size - 1, []):
        emit(
            GRegex("compl", (entry.expr,)),
            entry.dfa.complemented().minimized(),
            entry.height,
        )
        if entry.height == 0:
            emit(GRegex("star", (entry.expr,)), _star(entry.dfa), 1)

    for left_size in range(1, size - 1):
        right_size = size - 1 - left_size
        for left in layers.get(left_size, []):
            for right in layers.get(right_size, []):
                height = max(left.height, right.height)
                if left_size <= right_size:  # union is commutative
                    emit(
                        GRegex("union", (left.expr, right.expr)),
                        _product(left.dfa, right.dfa, lambda x, y: x or y),
                        height,
                    )
                emit(
                    GRegex("concat", (left.expr, right.expr)),
                    _concat(left.dfa, right.dfa),
                    height,
                )
    return candidates, pruned


def search(
    target: DFA,
    max_size: int,
    *,
    max_states: int = 0,
    verbose: bool = False,
) -> SearchResult:
    """Enumerate height-≤1 expressions by size until the target language appears."""

    target_min = target.minimized()
    target_key = dfa_key(target_min)
    alphabet = target_min.alphabet

    started = time.monotonic()
    best_height: dict[DfaKey, int] = {}
    layers: dict[int, list[Entry]] = {}
    pruned_total = 0

    for size in range(1, max_size + 1):
        candidates, pruned = _new_layer(size, layers, alphabet, max_states)
        pruned_total += pruned
        kept: list[Entry] = []
        for entry in candidates:
            key = dfa_key(entry.dfa)
            previous = best_height.get(key)
            if previous is not None and previous <= entry.height:
                continue
            best_height[key] = entry.height
            kept.append(entry)
            if key == target_key:
                return SearchResult(
                    found=True,
                    target_states=len(target_min.states),
                    max_size=max_size,
                    completed_size=size - 1,
                    languages_seen=len(best_height),
                    pruned=pruned_total,
                    elapsed_seconds=time.monotonic() - started,
                    expr=entry.expr,
                    height=entry.height,
                    size=size,
                )
        layers[size] = kept
        if verbose:
            elapsed = time.monotonic() - started
            print(
                f"size {size}: kept {len(kept)} new languages "
                f"(total {len(best_height)}, pruned {pruned_total}, {elapsed:.1f}s)",
                file=sys.stderr,
            )
    return SearchResult(
        found=False,
        target_states=len(target_min.states),
        max_size=max_size,
        completed_size=max_size,
        languages_seen=len(best_height),
        pruned=pruned_total,
        elapsed_seconds=time.monotonic() - started,
    )


def certificate_for(result: SearchResult, target: DFA) -> dict:
    """Build and independently re-verify a certificate for a successful search."""

    if not result.found or result.expr is None or result.height is None:
        raise ValueError("certificate_for requires a successful search result")
    certificate = {
        "schema": "gsh-regex-certificate-v1",
        "alphabet": list(target.alphabet),
        "claimed_height": result.height,
        "expression": result.expr.to_json(),
        "target_dfa": target.minimized().to_json(),
        "provenance": {
            "tool": "tools.height_search",
            "expression_size": result.size,
            "pretty": format_regex(result.expr),
        },
    }
    report = check_certificate(certificate)
    if not report.ok:
        raise AssertionError(
            f"internal error: synthesized expression failed independent check: {report}"
        )
    return certificate


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Search for a height-≤1 generalized regex matching a target language."
    )
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--target", help="named target from tools.targets")
    group.add_argument(
        "--target-json",
        type=Path,
        help="path to a JSON file holding a target_dfa object (certificate format)",
    )
    group.add_argument("--list", action="store_true", help="list named targets and exit")
    parser.add_argument("--max-size", type=int, default=10, help="largest AST size to try")
    parser.add_argument(
        "--max-states",
        type=int,
        default=0,
        help="discard intermediate DFAs above this state count (0 = keep all; "
        "any pruning makes a negative result inconclusive even below max-size)",
    )
    parser.add_argument("--out", type=Path, help="write the verified certificate JSON here")
    parser.add_argument("--quiet", action="store_true", help="suppress per-size progress")
    args = parser.parse_args(argv)

    if args.list:
        for name in sorted(TARGETS):
            print(f"{name}: {TARGETS[name].description}")
        return 0

    if args.target:
        target = build_target(args.target)
    elif args.target_json:
        from tools.regex_cert import parse_target_dfa

        data = json.loads(args.target_json.read_text(encoding="utf-8"))
        alphabet = data.get("alphabet", ["a", "b"])
        target = parse_target_dfa(data["target_dfa"] if "target_dfa" in data else data, alphabet)
    else:
        parser.error("one of --target, --target-json, --list is required")

    result = search(
        target,
        args.max_size,
        max_states=args.max_states,
        verbose=not args.quiet,
    )
    print(result.summary())
    print(
        f"target: {result.target_states} states | languages seen: {result.languages_seen} | "
        f"{result.elapsed_seconds:.1f}s"
    )
    if result.found:
        certificate = certificate_for(result, target)
        print("independent re-check: ok")
        if args.out:
            args.out.write_text(json.dumps(certificate, indent=2), encoding="utf-8")
            print(f"certificate written to {args.out}")
    return 0 if result.found else 1


if __name__ == "__main__":
    sys.exit(main())
