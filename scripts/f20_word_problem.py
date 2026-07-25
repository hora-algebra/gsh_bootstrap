#!/usr/bin/env python3
"""Exact height-one certificate for one two-generator F_20 word problem.

The proved language is the identity fibre of the single morphism

    a |-> (x |-> x + 1),    b |-> (x |-> 2*x)

from {a,b}* to AGL(1,5).  This is *not* a proof of
``HeightOneForGroup F_20``.

The generalized-regex AST, recursive matcher, exact DFA compiler,
equivalence checker, and certificate JSON translator are imported from
``scripts/weis_l2_full_gsh1.py`` verbatim rather than reimplemented.  The
target-specific compact certificate writer below follows that module's
``write_certificate`` serialization pattern.

The W-atom construction is derived explicitly with phase letter ``b`` and
counted letter ``a``.  For phase r:

    opener = (a* b)^r
    X      = a | b a* b a* b a* b
    tail_s = (b a*)^s, 0 <= s < 4.

After the opener, every word has a unique factorization X* tail_s.  If t is
the number of X-tokens and B is the total number of b's, then

    B = r + 4*f + s,    t = N_r + f,

where f is the number of long tokens.  Thus N_r modulo 5 is determined by
t modulo 5 and B modulo 20.  The final expression uses the smaller
specialization B = 0 mod 4: the no-b case is handled separately, while for
B = 4u > 0 the four token residues satisfy one weighted congruence.  All
checks are deterministic and exhaustive where bounded; language equivalence
is a complete product-automaton proof.
"""

from __future__ import annotations

import argparse
import itertools
import json
from collections import deque
from pathlib import Path
import subprocess
import sys
import time

REPO = Path(__file__).resolve().parents[1]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from scripts.weis_l2_full_gsh1 import (  # noqa: E402
    AL,
    EMPTY,
    EPS,
    TOP,
    cat,
    compile_dfa,
    d_accepts,
    d_min,
    dfa,
    equivalence_counterexample,
    height,
    inter,
    lit,
    match,
    neg,
    power,
    star,
    to_cert_json,
    union,
)


# ---------------- F_20 = AGL(1,5) ground truth ----------------

Affine = tuple[int, int]  # (alpha, beta) denotes x |-> alpha*x + beta
IDENTITY: Affine = (1, 0)
GEN: dict[str, Affine] = {"a": (1, 1), "b": (2, 0)}
COEFFICIENTS = (1, 3, 4, 2)


def compose(left: Affine, right: Affine) -> Affine:
    """Apply ``left`` first and ``right`` second."""

    alpha, beta = left
    gamma, delta = right
    return ((gamma * alpha) % 5, (gamma * beta + delta) % 5)


def affine_power(g: Affine, exponent: int) -> Affine:
    out = IDENTITY
    for _ in range(exponent):
        out = compose(out, g)
    return out


def affine_order(g: Affine) -> int:
    out = IDENTITY
    for exponent in range(1, 21):
        out = compose(out, g)
        if out == IDENTITY:
            return exponent
    raise AssertionError(f"element has no order <= 20: {g}")


def generated_group() -> set[Affine]:
    elements = {IDENTITY}
    queue = deque([IDENTITY])
    while queue:
        g = queue.popleft()
        for c in AL:
            h = compose(g, GEN[c])
            if h not in elements:
                elements.add(h)
                queue.append(h)
    return elements


def phi_direct(word: str) -> Affine:
    out = IDENTITY
    for c in word:
        out = compose(out, GEN[c])
    return out


def phi_coordinates(word: str) -> Affine:
    """The plan's closed coordinate formula, computed independently."""

    number_of_b = word.count("b")
    alpha = pow(2, number_of_b, 5)
    beta = 0
    b_after = 0
    for c in reversed(word):
        if c == "b":
            b_after += 1
        else:
            beta = (beta + pow(2, b_after, 5)) % 5
    return (alpha, beta)


def staged_counts(word: str) -> tuple[int, int, int, int]:
    phase = 0
    counts = [0, 0, 0, 0]
    for c in word:
        if c == "b":
            phase = (phase + 1) % 4
        else:
            counts[phase] += 1
    return tuple(counts)


def arithmetic_identity_test(word: str) -> bool:
    counts = staged_counts(word)
    weighted = sum(c * n for c, n in zip(COEFFICIENTS, counts))
    return word.count("b") % 4 == 0 and weighted % 5 == 0


def word_problem_dfa():
    states = sorted(generated_group())
    index = {g: i for i, g in enumerate(states)}
    transitions = [
        {c: index[compose(g, GEN[c])] for c in AL}
        for g in states
    ]
    return d_min(dfa(transitions, index[IDENTITY], [index[IDENTITY]])), states


# ---------------- generalized height-one expression ----------------

la, lb = lit("a"), lit("b")
ASTAR = neg(cat(TOP, lb, TOP))  # words without b, i.e. a*; star-free
STEP = cat(ASTAR, lb)
LONG_TOKEN = cat(lb, ASTAR, lb, ASTAR, lb, ASTAR, lb)
TOKEN = union(la, LONG_TOKEN)
TAILS = [power(cat(lb, ASTAR), s) for s in range(4)]


def opener(r: int):
    return power(STEP, r)


def token_count_mod_5(j: int):
    """Unique TOKEN-factorizations having j tokens modulo 5."""

    j %= 5
    return cat(power(TOKEN, j), star(power(TOKEN, 5)))


TOKEN_RESIDUES = tuple(token_count_mod_5(j) for j in range(5))


def phase_token_residue(r: int, j: int):
    """Words with positive b-count divisible by 4 and phase-r token count j.

    Under the surrounding four-phase intersection, the phase-1 opener forces
    at least one b, and the selected tails force the same total b-count to be
    0 modulo 4 in every phase view.
    """

    if not 0 <= r < 4:
        raise ValueError(f"phase must be in 0..3, got {r}")
    tail = (-r) % 4
    return cat(opener(r), TOKEN_RESIDUES[j % 5], TAILS[tail])


def low_b_count(r: int):
    """Words with fewer than r occurrences of b (star-free).

    Such words never reach phase r, so N_r = 0 for them, and they have no
    opener factorization; they must be added to the h = 0 atom by hand.
    """

    if r == 0:
        return EMPTY
    return union(*(cat(power(STEP, i), ASTAR) for i in range(r)))


def b_count_mod_20(q: int):
    """Words whose number of b's is q modulo 20."""

    q %= 20
    return cat(star(power(STEP, 20)), power(STEP, q), ASTAR)


B20_RESIDUES = tuple(b_count_mod_20(q) for q in range(20))
B_MOD_4_ZERO = cat(star(power(STEP, 4)), ASTAR)


def staged_atom(r: int, h: int):
    """W_{r,h} = { w : N_r(w) = h mod 5 }, the transparent W atom.

    With t the number of TOKEN factors, f the number of long tokens, s the
    tail index and B the total b-count: B = r + 4f + s and t = N_r + f.  So
    fixing t mod 5 = j and N_r mod 5 = h forces f = j - h (mod 5), hence
    B = r + s + 4*((j-h) mod 5) (mod 20); conversely B mod 20 together with
    t mod 5 pins down N_r mod 5.
    """

    if not 0 <= r < 4:
        raise ValueError(f"phase must be in 0..3, got {r}")
    h %= 5
    terms = []
    for s in range(4):
        for j in range(5):
            q = (r + s + 4 * ((j - h) % 5)) % 20
            terms.append(
                inter(
                    cat(opener(r), TOKEN_RESIDUES[j], TAILS[s]),
                    B20_RESIDUES[q],
                )
            )
    body = union(*terms)
    return union(low_b_count(r), body) if r > 0 and h == 0 else body


W = tuple(tuple(staged_atom(r, h) for h in range(5)) for r in range(4))


def assemble_expression_atoms():
    """The transparent assembly: a Boolean combination of the 20 W atoms.

    beta = N_0 + 3 N_1 + 4 N_2 + 2 N_3 mod 5, paired as (h0 + 3 h1) and
    (4 h2 + 2 h3) to keep the term count at 100 rather than 500.
    """

    first_pair = []
    second_pair = []
    for residue in range(5):
        first_pair.append(
            union(
                *(
                    inter(W[0][h0], W[1][h1])
                    for h0 in range(5)
                    for h1 in range(5)
                    if (h0 + 3 * h1) % 5 == residue
                )
            )
        )
        second_pair.append(
            union(
                *(
                    inter(W[2][h2], W[3][h3])
                    for h2 in range(5)
                    for h3 in range(5)
                    if (4 * h2 + 2 * h3) % 5 == residue
                )
            )
        )
    weighted_zero = union(
        *(inter(first_pair[r], second_pair[-r % 5]) for r in range(5))
    )
    return inter(B_MOD_4_ZERO, weighted_zero)


def assemble_expression():
    """Compact W-scheme specialization for the F_20 identity fibre."""

    first_pair = []
    second_pair = []
    for residue in range(5):
        first_pair.append(
            union(
                *(
                    inter(phase_token_residue(0, j0), phase_token_residue(1, j1))
                    for j0 in range(5)
                    for j1 in range(5)
                    if (j0 + 3 * j1) % 5 == residue
                )
            )
        )
        second_pair.append(
            union(
                *(
                    inter(phase_token_residue(2, j2), phase_token_residue(3, j3))
                    for j2 in range(5)
                    for j3 in range(5)
                    if (4 * j2 + 2 * j3) % 5 == residue
                )
            )
        )
    # If B = 4u > 0, token residues are
    #   j0=N0+u, j1=N1+u-1, j2=N2+u-1, j3=N3+u-1.
    # Their weighted sum is the target weighted N-sum plus 1 modulo 5.
    positive_b_identity = union(
        *(inter(first_pair[r], second_pair[(1 - r) % 5]) for r in range(5))
    )
    no_b_identity = star(power(la, 5))
    return union(no_b_identity, positive_b_identity)


EXPRESSION = assemble_expression()
EXPRESSION_ATOMS = assemble_expression_atoms()


# ---------------- compact certificate ----------------

def write_certificate(path: Path, expr, target, states: list[Affine]) -> Path:
    state_name = {g: f"g_{g[0]}_{g[1]}" for g in states}
    target_data = {
        "states": [state_name[g] for g in states],
        "start": state_name[IDENTITY],
        "accept": [state_name[IDENTITY]],
        "transitions": {
            state_name[g]: {
                c: state_name[compose(g, GEN[c])]
                for c in AL
            }
            for g in states
        },
    }
    data = {
        "schema": "gsh-regex-certificate-v1",
        "description": (
            "The identity fibre of the two-generator morphism from {a,b}* "
            "to F_20 = AGL(1,5), a -> (x -> x+1), b -> (x -> 2x), has "
            "generalized star-height at most 1. This certificate does not "
            "claim HeightOneForGroup F_20. Generated deterministically by "
            "scripts/f20_word_problem.py --certificate."
        ),
        "alphabet": list(AL),
        "claimed_height": 1,
        "expression": to_cert_json(expr),
        "target_dfa": target_data,
    }
    assert len(target["t"]) == 20
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8") as fh:
        fh.write("{\n")
        for key in ("schema", "description", "alphabet", "claimed_height"):
            fh.write(f"  {json.dumps(key)}: {json.dumps(data[key])},\n")
        fh.write(
            '  "expression": '
            + json.dumps(data["expression"], separators=(",", ":"))
            + ",\n"
        )
        fh.write(
            '  "target_dfa": '
            + json.dumps(data["target_dfa"], separators=(",", ":"))
            + "\n}\n"
        )
    return path


def all_words(max_length: int):
    for length in range(max_length + 1):
        for letters in itertools.product(AL, repeat=length):
            yield "".join(letters)


def fail(check: int, message: str) -> "NoReturn":
    print(f"[{check}] FAIL: {message}")
    raise SystemExit(1)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--certificate",
        nargs="?",
        const=REPO / "data/certificates/height1_f20_word_problem.json",
        type=Path,
        help="write and independently verify a certificate (optional path)",
    )
    args = parser.parse_args()

    started = time.time()

    # 1. Group and coordinate formula.
    group = generated_group()
    order_a = affine_order(GEN["a"])
    order_b = affine_order(GEN["b"])
    if len(group) != 20 or order_a != 5 or order_b != 4:
        fail(
            1,
            f"|<a,b>|={len(group)}, order(a)={order_a}, order(b)={order_b}",
        )
    checked = 0
    for word in all_words(12):
        checked += 1
        direct = phi_direct(word)
        formula = phi_coordinates(word)
        if direct != formula:
            fail(1, f"coordinate formula mismatch on {word!r}: {direct} != {formula}")
    print(
        f"[1] PASS: |<phi(a),phi(b)>|=20; order(phi(a))=5; "
        f"order(phi(b))=4; coordinate formula agrees on {checked} words "
        f"(length <= 12)."
    )

    # 2. Arithmetic characterization.
    checked = 0
    for word in all_words(14):
        checked += 1
        direct = phi_direct(word) == IDENTITY
        arithmetic = arithmetic_identity_test(word)
        if direct != arithmetic:
            counts = staged_counts(word)
            fail(
                2,
                f"arithmetic characterization mismatch on {word!r}; "
                f"phi={phi_direct(word)}, N={counts}",
            )
    print(
        f"[2] PASS: arithmetic characterization agrees with phi(w)=identity "
        f"on all {checked} words (length <= 14)."
    )

    # 3. Syntactic generalized star-height.
    actual_height = height(EXPRESSION)
    if actual_height != 1:
        fail(3, f"height(E)={actual_height}, expected 1")
    atom_heights = sorted({height(W[r][h]) for r in range(4) for h in range(5)})
    if atom_heights != [1] or height(EXPRESSION_ATOMS) != 1:
        fail(3, f"W-atom heights are {atom_heights}, expected [1]")
    print(
        "[3] PASS: height(E)=1; all 20 W-atoms and the transparent assembly "
        "also have height 1."
    )

    # 3b. Each W atom really is the staged-count language it claims to be.
    #     Without this, only the assembled language is validated, and a wrong
    #     atom compensated by a wrong assembly would still pass check 5.
    atom_words = list(all_words(12))
    matcher_words = [w for w in atom_words if len(w) <= 8]
    for r in range(4):
        for h in range(5):
            atom = compile_dfa(W[r][h])
            for word in atom_words:
                if d_accepts(atom, word) != (staged_counts(word)[r] % 5 == h):
                    fail(
                        3,
                        f"W-atom (r={r}, h={h}) disagrees with "
                        f"N_{r} = {h} mod 5 on {word!r}",
                    )
            for word in matcher_words:
                if match(W[r][h], word, 0, len(word), {}) != (
                    staged_counts(word)[r] % 5 == h
                ):
                    fail(
                        3,
                        f"W-atom (r={r}, h={h}): the recursive matcher "
                        f"disagrees on {word!r}",
                    )
    print(
        f"[3b] PASS: each of the 20 W-atoms equals {{w : N_r = h mod 5}} — "
        f"compiled DFA on all {len(atom_words)} words (length <= 12), "
        f"independent matcher on {len(matcher_words)} words (length <= 8)."
    )

    # 4. Exact compilation.
    compile_started = time.time()
    compiled = compile_dfa(EXPRESSION)
    if len(compiled["t"]) != 20:
        fail(4, f"minimal compiled DFA has {len(compiled['t'])} states, expected 20")
    print(
        f"[4] PASS: compile_dfa(E) minimizes to exactly 20 states "
        f"({time.time() - compile_started:.1f}s)."
    )

    # 5. Complete product-reachability equivalence proof.
    target, states = word_problem_dfa()
    witness = equivalence_counterexample(compiled, target)
    if witness is not None:
        fail(5, f"NOT EQUIVALENT; shortest counterexample={witness!r}")
    print(
        "[5] PASS: EQUIVALENT to the 20-state F_20 word-problem DFA "
        "(complete product reachability)."
    )

    # 5b. The transparent atom assembly proves the same language.  The compact
    #     expression above is only a size optimization for the certificate; the
    #     mathematical content is the W-atom Boolean combination.
    compiled_atoms = compile_dfa(EXPRESSION_ATOMS)
    if len(compiled_atoms["t"]) != 20:
        fail(
            5,
            f"atom assembly minimizes to {len(compiled_atoms['t'])} states, "
            f"expected 20",
        )
    witness = equivalence_counterexample(compiled_atoms, target)
    if witness is not None:
        fail(5, f"atom assembly NOT EQUIVALENT; counterexample={witness!r}")
    print(
        "[5b] PASS: the transparent W-atom assembly independently compiles to "
        "20 states and is EQUIVALENT to the same target."
    )

    # 6. Independent recursive matcher cross-validation.
    checked = 0
    for word in all_words(8):
        checked += 1
        by_compiler = d_accepts(compiled, word)
        by_matcher = match(EXPRESSION, word, 0, len(word), {})
        by_group = phi_direct(word) == IDENTITY
        if not (by_compiler == by_matcher == by_group):
            fail(
                6,
                f"disagreement on {word!r}: compiler={by_compiler}, "
                f"matcher={by_matcher}, group={by_group}",
            )
    print(
        f"[6] PASS: match(), compile_dfa(E), and direct group evaluation "
        f"agree on all {checked} words (length <= 8)."
    )

    # 7. Optional certificate, checked by a separate Python process.
    if args.certificate is None:
        print("[7] PASS: certificate emission not requested (use --certificate).")
    else:
        path = args.certificate
        if not path.is_absolute():
            path = REPO / path
        write_certificate(path, EXPRESSION, target, states)
        verifier = subprocess.run(
            [sys.executable, str(REPO / "scripts/check_certificate.py"), str(path)],
            cwd=REPO,
            text=True,
            capture_output=True,
            check=False,
        )
        verdict = verifier.stdout.strip() or verifier.stderr.strip()
        if verifier.returncode != 0:
            fail(7, f"certificate verifier exit={verifier.returncode}: {verdict}")
        print(f"[7] PASS: wrote {path.relative_to(REPO)}.")
        print(f"[certificate] {verdict}")

    print(f"[done] all requested checks PASS ({time.time() - started:.1f}s total).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
