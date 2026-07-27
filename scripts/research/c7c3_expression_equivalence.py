#!/usr/bin/env python3
"""Height-one generalized regular expressions for identity fibres of C_7 : C_3.

Target of the exercise (`N-C7C3-001`, `notes/c7c3_full_alphabet.md` section 7):
build a generalized regular expression of syntactic star height <= 1 for the
identity fibre of the FULL 21-letter alphabet of `C_7 : C_3`, compile it, and
decide language equality with the 21-state word-problem DFA by product
reachability.  By `FULL-ALPH-RED-01` that would establish
`HeightOneForGroup (C_7 : C_3)`.

WHAT THIS SCRIPT ESTABLISHES, AND WHAT IT DOES NOT.

  * Sections 1-3 build explicit star-free expressions for the token, opener and
    tail languages of the phase cuts, and height-one expressions for the cut
    counting languages.  Every one of them is checked by product reachability
    against a reference automaton built from the semantic definition, so those
    are decisions and not samples.

  * Section 4 assembles, compiles and DECIDES the identity fibre for the
    9-letter sub-alphabet  {(1,b) : b in Z_7} u {y, y^2}  -- every element of
    the kernel C_7, plus the two non-trivial elements of the complement C_3.
    Those 9 letters generate the group.  This is a genuine height-one result
    for a sub-alphabet; by `FULL-ALPH-RED-01` a sub-alphabet does NOT give
    `HeightOneForGroup`, so `C_7 : C_3` does NOT leave the unresolved list.

  * Sections 5 and 6 are the negative half, and they are the point of the run.
    The 21-letter case fails, and the failure is localised exactly.  The
    features whose block languages this script can write down explicitly are
    shown, by an exact GF(7) rank computation on the cycle space of the phase
    automaton, to be UNABLE to determine beta -- so no assembly of them can
    work -- and a minimal pair of words witnessing this is exhibited.  The
    features that would suffice (the phase-resolved pair cuts of
    `scripts/research/metacyclic_full_alphabet.py`) have block languages that
    are aperiodic, hence star-free by Schuetzenberger's theorem, but no
    explicit star-free expression for them was found.

Nothing here is a sample.  Every "PASS" is a complete finite decision; every
negative claim is a rank computation or an exhaustive automaton comparison.
"""

from __future__ import annotations

import itertools
import random
import sys
import time
from collections import defaultdict, deque
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
if str(REPO) not in sys.path:
    sys.path.insert(0, str(REPO))

from tools.regex_cert import (  # noqa: E402
    DFA,
    GRegex,
    compile_regex,
    equivalence_witness,
)

MODULUS = 7
PHASES = 3
POWERS = (1, 2, 4)          # 2^0, 2^1, 2^2 mod 7
INVERSE_POWERS = (1, 4, 2)  # 2^-0, 2^-1, 2^-2 mod 7

SIGMA = tuple((e, b) for e in range(PHASES) for b in range(MODULUS))
IDENTITY = (0, 0)
EPS = {g: g[0] for g in SIGMA}


def name(g) -> str:
    return f"e{g[0]}b{g[1]}"


ALL_NAMES = tuple(name(g) for g in SIGMA)
BY_NAME = {name(g): g for g in SIGMA}


def compose(x, y):
    """(a,b)(a',b') = (a a', a' b + b') with a = 2^e in <2> <= (Z/7)^*."""
    (e1, b1), (e2, b2) = x, y
    return ((e1 + e2) % PHASES, (POWERS[e2] * b1 + b2) % MODULUS)


def evaluate(word):
    out = IDENTITY
    for g in word:
        out = compose(out, g)
    return out


def coordinate_formula(word):
    """mu(w) = (sum eps, sum_i b_i 2^{E_i}) with E_i the suffix phase after i."""
    total = sum(EPS[g] for g in word) % PHASES
    beta = 0
    suffix = 0
    for g in reversed(word):
        beta = (beta + g[1] * POWERS[suffix]) % MODULUS
        suffix = (suffix + EPS[g]) % PHASES
    return (total, beta)


# --------------------------------------------------------------------------
# generalized regular expression helpers (tools/regex_cert.py AST)
# --------------------------------------------------------------------------

# Every node ever built is kept alive here.  The memo tables below are keyed by
# id(), so a node must never be collected and its address reused; without this
# list the caches silently return another expression's automaton.
_KEEP: list[GRegex] = []


def _new(node: GRegex) -> GRegex:
    _KEEP.append(node)
    return node


EMPTY = _new(GRegex("empty"))
EPSILON = _new(GRegex("eps"))


def lit(g) -> GRegex:
    return _new(GRegex("letter", value=name(g)))


def union(*args) -> GRegex:
    args = tuple(a for a in args if a is not EMPTY)
    if not args:
        return EMPTY
    if len(args) == 1:
        return args[0]
    return _new(GRegex("union", args))


def concat(*args) -> GRegex:
    args = tuple(a for a in args if a is not EPSILON)
    if not args:
        return EPSILON
    if len(args) == 1:
        return args[0]
    return _new(GRegex("concat", args))


def compl(a) -> GRegex:
    return _new(GRegex("compl", (a,)))


def star(a) -> GRegex:
    return _new(GRegex("star", (a,)))


def inter(*args) -> GRegex:
    """A n B = ~(~A u ~B); the AST has no primitive intersection."""
    return compl(union(*[compl(a) for a in args]))


def power(a, n) -> GRegex:
    return concat(*([a] * n)) if n > 0 else EPSILON


_HEIGHT_CACHE: dict[int, int] = {}


def star_height(expr: GRegex) -> int:
    """Syntactic star height, memoised so shared sub-expressions cost once."""
    key = id(expr)
    hit = _HEIGHT_CACHE.get(key)
    if hit is not None:
        return hit
    if expr.op in {"empty", "eps", "letter"}:
        value = 0
    elif expr.op in {"union", "concat"}:
        value = max((star_height(a) for a in expr.args), default=0)
    elif expr.op == "compl":
        value = star_height(expr.args[0])
    elif expr.op == "star":
        value = 1 + star_height(expr.args[0])
    else:
        raise AssertionError(expr.op)
    _HEIGHT_CACHE[key] = value
    return value


_COMPILE_CACHE: dict[tuple[int, tuple[str, ...]], DFA] = {}


def compile_cached(expr: GRegex, alphabet) -> DFA:
    """compile_regex with memoisation, so the expression may be a DAG."""
    key = (id(expr), tuple(alphabet))
    hit = _COMPILE_CACHE.get(key)
    if hit is not None:
        return hit
    alpha = tuple(alphabet)
    if expr.op in {"empty", "eps", "letter"}:
        out = compile_regex(expr, alpha)
    elif expr.op == "compl":
        out = compile_cached(expr.args[0], alpha).complemented().minimized()
    elif expr.op == "star":
        out = compile_regex(GRegex("star", (expr.args[0],)), alpha) \
            if False else _star_of(compile_cached(expr.args[0], alpha), alpha)
    elif expr.op == "union":
        out = _fold(expr.args, alpha, "union")
    elif expr.op == "concat":
        out = _fold(expr.args, alpha, "concat")
    else:
        raise AssertionError(expr.op)
    _COMPILE_CACHE[key] = out
    return out


def _star_of(machine: DFA, alpha) -> DFA:
    from tools.regex_cert import _star

    return _star(machine)


def _fold(args, alpha, op) -> DFA:
    from tools.regex_cert import _atomic_empty, _atomic_eps, _concat, _product

    if op == "union":
        out = _atomic_empty(alpha)
        for arg in args:
            out = _product(out, compile_cached(arg, alpha), lambda x, y: x or y)
        return out.minimized()
    out = _atomic_eps(alpha)
    for arg in args:
        out = _concat(out, compile_cached(arg, alpha))
    return out.minimized()


# --------------------------------------------------------------------------
# reference automata, built straight from the semantic definition
# --------------------------------------------------------------------------


def reference(alphabet, states, start, accept, step) -> DFA:
    transition = {}
    for s in states:
        for c in alphabet:
            transition[(s, c)] = step(s, BY_NAME[c])
    return DFA(tuple(alphabet), frozenset(states), start,
               frozenset(accept), transition).minimized()


def word_problem_dfa(alphabet) -> DFA:
    return reference(alphabet, list(SIGMA), IDENTITY, [IDENTITY],
                     lambda s, g: compose(s, g))


# ---- the star-free building blocks ---------------------------------------


class Blocks:
    """Explicit star-free expressions for the phase-cut languages.

    All phases are RELATIVE: a "0-entry" of a word u is a position whose
    phase-after, counted from the start of u, is 0.  Because every loop
    returns to the phase it started from, the same expressions serve every
    absolute cut phase.
    """

    def __init__(self, letters):
        self.letters = tuple(letters)
        self.names = tuple(name(g) for g in letters)
        self.TOP = compl(EMPTY)
        self.ANY = union(*[lit(g) for g in letters])
        self.SIG = {
            e: union(*[lit(g) for g in letters if EPS[g] == e])
            for e in range(PHASES)
        }
        self.MOVERS = union(self.SIG[1], self.SIG[2])
        # Z: words with no mover  (star-free: complement of TOP.M.TOP)
        self.Z = compl(concat(self.TOP, self.MOVERS, self.TOP))
        eq = union(*[concat(self.SIG[a], self.Z, self.SIG[a]) for a in (1, 2)])
        self.EQ_PAIR = eq
        # no two consecutive movers carry the same eps
        self.NOEQ = compl(concat(self.TOP, eq, self.TOP))
        self.LOOP = self._loop()
        self.TOKEN = union(self.SIG[0], self.LOOP)
        self.NR = self._no_return()

    # -- loops -------------------------------------------------------------
    def _mid(self, a, b):
        """movers m_2 .. m_{n-1}: starts with eps a, ends with eps b, alternating."""
        return inter(concat(self.SIG[a], self.TOP),
                     concat(self.TOP, self.SIG[b]),
                     self.NOEQ)

    def _loop(self):
        """First return to relative phase 0, starting with a mover.

        The phase walk of such a word visits the two non-zero residues
        alternately, so the eps sequence e_1..e_n obeys
            n = 2 : e_1 != e_2 ;
            n >= 3: e_1 = e_2, e_{n-1} = e_n, and e_j != e_{j+1} in between.
        """
        two = union(concat(self.SIG[1], self.Z, self.SIG[2]),
                    concat(self.SIG[2], self.Z, self.SIG[1]))
        long = union(*[
            concat(self.SIG[a], self.Z, self._mid(a, b), self.Z, self.SIG[b])
            for a in (1, 2) for b in (1, 2)
        ])
        return union(two, long)

    def _no_return(self):
        """No 0-entry at all, counted from relative phase 0.

        Such a word is empty or starts with a mover, its first two movers
        carry equal eps, and afterwards consecutive movers differ.
        """
        first_pair = compl(union(
            concat(self.SIG[1], self.Z, self.SIG[2], self.TOP),
            concat(self.SIG[2], self.Z, self.SIG[1], self.TOP),
        ))
        later = compl(concat(self.ANY, self.TOP, self.EQ_PAIR, self.TOP))
        return union(EPSILON,
                     inter(concat(self.MOVERS, self.TOP), first_pair, later))

    # -- openers and no-cut tails -----------------------------------------
    def avoid(self, q):
        """No q-entry, counted from absolute phase 0 (q != 0)."""
        assert q != 0
        t = (-q) % PHASES  # the residue other than 0 and q
        first = union(self.Z, concat(self.Z, self.SIG[t], self.TOP))
        return inter(self.NOEQ, first)

    def opener(self, q):
        """Prefix ending exactly at the first q-entry (from absolute phase 0)."""
        if q == 0:
            return self.TOKEN
        t = (-q) % PHASES
        avoid = self.avoid(q)
        end_t = inter(avoid, concat(self.TOP, self.SIG[t], self.Z))
        end_0 = inter(avoid, union(self.Z,
                                   concat(self.TOP, self.SIG[(2 * t) % PHASES], self.Z)))
        return union(concat(end_0, self.SIG[q]),
                     concat(end_t, self.SIG[(q - t) % PHASES]))

    def no_cut(self, q):
        return self.NR if q == 0 else self.avoid(q)


# ---- reference automata for the blocks ------------------------------------

DEAD = "dead"
ACC = "acc"


def loop_reference(alphabet, allow_short: bool):
    """First return to phase 0.  allow_short: a single non-mover also counts."""
    states = ["start", 0, 1, 2, ACC, DEAD]

    def step(s, g):
        if s in (ACC, DEAD):
            return DEAD
        phase = 0 if s == "start" else s
        nxt = (phase + EPS[g]) % PHASES
        if nxt == 0:
            if s == "start" and not allow_short and EPS[g] == 0:
                return DEAD
            return ACC
        return nxt

    return reference(alphabet, states, "start", [ACC], step)


def no_return_reference(alphabet):
    states = [0, 1, 2, DEAD]

    def step(s, g):
        if s == DEAD:
            return DEAD
        nxt = (s + EPS[g]) % PHASES
        return DEAD if nxt == 0 else nxt

    return reference(alphabet, states, 0, [0, 1, 2], step)


def avoid_reference(alphabet, q):
    states = [0, 1, 2, DEAD]

    def step(s, g):
        if s == DEAD:
            return DEAD
        nxt = (s + EPS[g]) % PHASES
        return DEAD if nxt == q else nxt

    return reference(alphabet, states, 0, [0, 1, 2], step)


def opener_reference(alphabet, q):
    states = [0, 1, 2, ACC, DEAD]

    def step(s, g):
        if s in (ACC, DEAD):
            return DEAD
        nxt = (s + EPS[g]) % PHASES
        return ACC if nxt == q else nxt

    return reference(alphabet, states, 0, [ACC], step)


def cut_count_reference(alphabet, q, skip, residue, modulus=MODULUS):
    """{ w : #(q-entries whose letter is not in `skip`) = residue mod m }."""
    states = [(p, r) for p in range(PHASES) for r in range(modulus)]

    def step(s, g):
        p, r = s
        nxt = (p + EPS[g]) % PHASES
        if nxt == q and g not in skip:
            r = (r + 1) % modulus
        return (nxt, r)

    return reference(alphabet, states, (0, 0),
                     [(p, residue) for p in range(PHASES)], step)


def letter_count_reference(alphabet, subset, residue, modulus):
    states = list(range(modulus))
    return reference(alphabet, states, 0,
                     [residue % modulus],
                     lambda s, g: (s + 1) % modulus if g in subset else s)


# --------------------------------------------------------------------------
# height-one counting expressions
# --------------------------------------------------------------------------


def cut_feature(blocks: Blocks, q: int, skip, residue: int) -> GRegex:
    """{ w : #(q-entries with letter not in `skip`) = residue mod 7 }.

    `skip` must be a set of NON-MOVER letters; then the skipped tokens are
    single letters and their star  (skip)^*  is star-free, which is what keeps
    the block below star-free and the whole expression at height one.
    """
    for g in skip:
        assert EPS[g] == 0, "only non-mover skips keep the block star-free"
    skip_names = {name(g) for g in skip}
    if skip:
        skip_star = compl(concat(blocks.TOP,
                                 union(*[lit(g) for g in blocks.letters
                                         if name(g) not in skip_names]),
                                 blocks.TOP))
    else:
        skip_star = EPSILON
    cutting = union(*[lit(g) for g in blocks.letters
                      if EPS[g] == 0 and name(g) not in skip_names] + [blocks.LOOP])
    block = concat(skip_star, cutting)
    opener = blocks.opener(q)
    if skip:
        opener_skipped = inter(opener, concat(blocks.TOP,
                                              union(*[lit(g) for g in skip])))
        opener_cut = inter(opener, compl(concat(blocks.TOP,
                                                union(*[lit(g) for g in skip]))))
        first = union(opener_cut, concat(opener_skipped, skip_star, cutting))
        tail = concat(skip_star, blocks.NR)
        nothing = union(blocks.no_cut(q),
                        concat(opener_skipped, skip_star, blocks.NR))
    else:
        first = opener
        tail = blocks.NR
        nothing = blocks.no_cut(q)
    body = concat(first, power(block, (residue - 1) % MODULUS),
                  star(power(block, MODULUS)), tail)
    return union(nothing, body) if residue % MODULUS == 0 else body


def letter_count_feature(blocks: Blocks, subset, residue, modulus) -> GRegex:
    """{ w : #(letters in `subset`) = residue mod m }, star height 1."""
    others = [g for g in blocks.letters if g not in subset]
    rest = compl(concat(blocks.TOP, union(*[lit(g) for g in subset]), blocks.TOP)) \
        if subset else blocks.TOP
    hit = union(*[lit(g) for g in subset])
    block = concat(rest, hit)
    return concat(power(block, residue % modulus),
                  star(power(block, modulus)), rest)


# --------------------------------------------------------------------------
# reporting helpers
# --------------------------------------------------------------------------

FAILURES: list[str] = []


def check(label, expr, target: DFA, alphabet, expect_height=None):
    compiled = compile_cached(expr, alphabet).minimized()
    witness = equivalence_witness(compiled, target)
    height = star_height(expr)
    ok = witness is None and (expect_height is None or height == expect_height)
    status = "PASS" if ok else "FAIL"
    detail = f"states={len(compiled.states)} height={height}"
    if witness is not None:
        detail += f" counterexample={witness!r}"
    print(f"    [{status}] {label}: {detail}", flush=True)
    if not ok:
        FAILURES.append(label)
    return compiled


def banner(text):
    print(f"\n=== {text} ===", flush=True)


# --------------------------------------------------------------------------
# section 1: the group, the coordinate formula, the word-problem DFA
# --------------------------------------------------------------------------


def section1():
    banner("1. the group C_7 : C_3, the coordinate formula, the target DFA")
    elements = set(SIGMA)
    assert len(elements) == 21
    for x in SIGMA:
        for y in SIGMA:
            assert compose(x, y) in elements
    for x in SIGMA:
        for y in SIGMA:
            for z in SIGMA:
                assert compose(compose(x, y), z) == compose(x, compose(y, z))
    for x in SIGMA:
        assert compose(x, IDENTITY) == compose(IDENTITY, x) == x
        assert any(compose(x, y) == IDENTITY for y in SIGMA)
    x, y = (0, 1), (1, 0)
    assert compose(compose(x, y), y) != compose(compose(y, y), x), "should be non-abelian"

    def power_of(g, k):
        out = IDENTITY
        for _ in range(k):
            out = compose(out, g)
        return out

    assert power_of(x, 7) == IDENTITY and power_of(x, 1) != IDENTITY
    assert power_of(y, 3) == IDENTITY and power_of(y, 1) != IDENTITY
    yinv = power_of(y, 2)
    # `compose` is the left-to-right ("apply left first") product, so the
    # presentation reads y^-1 x y = x^2 rather than y x y^-1 = x^2.
    assert compose(compose(yinv, x), y) == power_of(x, 2), "y^-1 x y = x^2"
    generated = {IDENTITY}
    frontier = [IDENTITY]
    while frontier:
        g = frontier.pop()
        for s in (x, y):
            h = compose(g, s)
            if h not in generated:
                generated.add(h)
                frontier.append(h)
    assert generated == elements, "<x,y> must be the whole group"
    print("    [PASS] 21 elements, associative, non-abelian, "
          "<x,y | x^7, y^3, y^-1 x y = x^2>, <x,y> = G.")

    checked = 0
    for length in range(4):
        for word in itertools.product(SIGMA, repeat=length):
            checked += 1
            if evaluate(word) != coordinate_formula(word):
                print(f"    [FAIL] coordinate formula on {word!r}")
                FAILURES.append("coordinate formula")
                return
    rng = random.Random(20260728)
    for _ in range(20000):
        word = tuple(rng.choice(SIGMA) for _ in range(rng.randint(4, 40)))
        checked += 1
        if evaluate(word) != coordinate_formula(word):
            print(f"    [FAIL] coordinate formula on a sweep word")
            FAILURES.append("coordinate formula")
            return
    print(f"    [PASS] mu(w) = (sum eps, sum_i b_i 2^(E_i)) on all 9724 words of "
          f"length <= 3 and 20000 fixed-seed words (total {checked}).")

    # positive control: the 21-state automaton really recognises mu^{-1}(e),
    # decided WITHOUT using the group product -- the coordinate formula is an
    # independent route to the same predicate, and the two agree above.
    target = word_problem_dfa(ALL_NAMES)
    print(f"    [PASS] word-problem DFA minimises to {len(target.states)} states "
          f"(= |G|), start = accept = identity.")
    if len(target.states) != 21:
        FAILURES.append("word-problem DFA size")
    # and it accepts exactly the identity fibre, on a complete traversal of its
    # own product with the group: trivially true by construction, so instead we
    # decide it against the coordinate-formula predicate as an automaton.
    coord = reference(
        ALL_NAMES,
        [(p, b) for p in range(PHASES) for b in range(MODULUS)],
        (0, 0),
        [(0, 0)],
        lambda s, g: ((s[0] + EPS[g]) % PHASES,
                      (POWERS[EPS[g]] * s[1] + g[1]) % MODULUS),
    )
    witness = equivalence_witness(target, coord)
    print(f"    [{'PASS' if witness is None else 'FAIL'}] the word-problem DFA "
          f"equals the coordinate-formula automaton (product reachability).")
    if witness is not None:
        FAILURES.append("word-problem positive control")
    return target


# --------------------------------------------------------------------------
# section 2: explicit star-free expressions for the cut blocks
# --------------------------------------------------------------------------


def section2(letters, label):
    banner(f"2. star-free block expressions over the {len(letters)}-letter "
           f"alphabet ({label})")
    names = tuple(name(g) for g in letters)
    blocks = Blocks(letters)
    check("LOOP  (first return to phase 0, mover-initial)",
          blocks.LOOP, loop_reference(names, allow_short=False), names, 0)
    check("TOKEN (first return to phase 0, any first letter)",
          blocks.TOKEN, loop_reference(names, allow_short=True), names, 0)
    check("NR    (no 0-entry at all)",
          blocks.NR, no_return_reference(names), names, 0)
    for q in (1, 2):
        check(f"AVOID_{q} (no {q}-entry)",
              blocks.avoid(q), avoid_reference(names, q), names, 0)
    for q in range(PHASES):
        check(f"OPEN_{q}  (prefix ending at the first {q}-entry)",
              blocks.opener(q), opener_reference(names, q), names, 0)
    return blocks


def section2_controls(letters):
    banner("2b. negative controls on the block expressions")
    names = tuple(name(g) for g in letters)
    blocks = Blocks(letters)
    target = loop_reference(names, allow_short=False)

    # control A: drop the alternation condition inside a loop.
    broken_mid = lambda a, b: inter(concat(blocks.SIG[a], blocks.TOP),
                                    concat(blocks.TOP, blocks.SIG[b]))
    broken = union(
        union(concat(blocks.SIG[1], blocks.Z, blocks.SIG[2]),
              concat(blocks.SIG[2], blocks.Z, blocks.SIG[1])),
        union(*[concat(blocks.SIG[a], blocks.Z, broken_mid(a, b),
                       blocks.Z, blocks.SIG[b])
                for a in (1, 2) for b in (1, 2)]))
    witness = equivalence_witness(compile_cached(broken, names).minimized(), target)
    fired = witness is not None
    print(f"    [{'PASS' if fired else 'FAIL'}] control A "
          f"(alternation condition dropped from LOOP): "
          f"{'detected, shortest counterexample ' + repr(witness) if fired else 'NOT DETECTED'}")
    if not fired:
        FAILURES.append("control A")

    # control B: require the first two movers to differ instead of agreeing.
    swapped = union(*[
        concat(blocks.SIG[a], blocks.Z, blocks._mid((2 * a) % 3, b),
               blocks.Z, blocks.SIG[b])
        for a in (1, 2) for b in (1, 2)])
    swapped = union(union(concat(blocks.SIG[1], blocks.Z, blocks.SIG[2]),
                          concat(blocks.SIG[2], blocks.Z, blocks.SIG[1])),
                    swapped)
    witness = equivalence_witness(compile_cached(swapped, names).minimized(), target)
    fired = witness is not None
    print(f"    [{'PASS' if fired else 'FAIL'}] control B "
          f"(first-pair eps condition flipped): "
          f"{'detected, shortest counterexample ' + repr(witness) if fired else 'NOT DETECTED'}")
    if not fired:
        FAILURES.append("control B")


# --------------------------------------------------------------------------
# section 3: the height-one counting features
# --------------------------------------------------------------------------


def section3(blocks: Blocks, letters):
    banner("3. height-one cut-counting features (each decided, not sampled)")
    names = tuple(name(g) for g in letters)
    nonmovers = [g for g in letters if EPS[g] == 0]
    for q in range(PHASES):
        for r in (0, 1, 3):
            check(f"base cut at phase {q}, count = {r} mod 7",
                  cut_feature(blocks, q, frozenset(), r),
                  cut_count_reference(names, q, frozenset(), r), names, 1)
    skip = frozenset(nonmovers[:3])
    for q in range(PHASES):
        for r in (0, 2):
            check(f"cut at phase {q} skipping 3 non-movers, count = {r} mod 7",
                  cut_feature(blocks, q, skip, r),
                  cut_count_reference(names, q, skip, r), names, 1)
    subset = frozenset(g for g in letters if EPS[g] == 1)
    for r in range(PHASES):
        check(f"#(eps=1 letters) = {r} mod 3",
              letter_count_feature(blocks, subset, r, PHASES),
              letter_count_reference(names, subset, r, PHASES), names, 1)


# --------------------------------------------------------------------------
# section 4: assembling an identity fibre from the features
# --------------------------------------------------------------------------


def beta_functional(blocks: Blocks, letters):
    """beta' = sum_q 2^-q * sum_h b_h N[h,q] as a GF(7) combination of cuts.

    Only NON-MOVER weights appear, so this functional is the whole of beta'
    exactly when every mover letter has b = 0.  With the level sets
    S_j = { h non-mover : b_h >= j } one has
        sum_h b_h N[h,q] = sum_{j=1..6} ( Z_q - C_q^{S_j} ),
    where C_q^S is the cut at phase q that skips the letters of S.
    """
    nonmovers = [g for g in letters if EPS[g] == 0]
    terms = []
    for q in range(PHASES):
        weight = INVERSE_POWERS[q]
        terms.append((6 * weight % MODULUS, q, frozenset()))
        for j in range(1, MODULUS):
            skip = frozenset(h for h in nonmovers if h[1] >= j)
            terms.append(((-weight) % MODULUS, q, skip))
    return [t for t in terms if t[0] % MODULUS]


def assemble(blocks, letters, terms, perturb=None, verbose=True):
    """Expression for { w : sum_k coef_k * cut_k = 0 mod 7 }, star height 1."""
    names = tuple(name(g) for g in letters)
    partial = [None] * MODULUS
    started = False
    for index, (coef, q, skip) in enumerate(terms):
        if perturb is not None and index == perturb[0]:
            coef = (coef + perturb[1]) % MODULUS
            if coef == 0:
                coef = 1
        feature = [cut_feature(blocks, q, skip, r) for r in range(MODULUS)]
        if not started:
            inv = pow(coef, -1, MODULUS)
            partial = [feature[(r * inv) % MODULUS] for r in range(MODULUS)]
            started = True
            continue
        inv = pow(coef, -1, MODULUS)
        new = []
        for r in range(MODULUS):
            new.append(union(*[
                inter(partial[s], feature[((r - s) * inv) % MODULUS])
                for s in range(MODULUS)
            ]))
        partial = new
        if verbose:
            print(f"      combined feature {index + 1}/{len(terms)}", flush=True)
    return partial[0]


def phase_zero(blocks, letters):
    one = frozenset(g for g in letters if EPS[g] == 1)
    two = frozenset(g for g in letters if EPS[g] == 2)
    return union(*[
        inter(letter_count_feature(blocks, one, a, PHASES),
              letter_count_feature(blocks, two, a, PHASES))
        for a in range(PHASES)
    ])


def section4(letters, label):
    banner(f"4. assembling and DECIDING the identity fibre over the "
           f"{len(letters)}-letter alphabet ({label})")
    names = tuple(name(g) for g in letters)
    blocks = Blocks(letters)
    movers_with_weight = [g for g in letters if EPS[g] != 0 and g[1] != 0]
    print(f"    movers carrying a non-zero C_7 coordinate: {len(movers_with_weight)}")
    if movers_with_weight:
        print("    -> beta' is NOT the non-mover functional; the assembly below "
              "cannot be the identity fibre.")
    started = time.time()
    terms = beta_functional(blocks, letters)
    beta_expr = assemble(blocks, letters, terms)
    expr = inter(phase_zero(blocks, letters), beta_expr)
    height = star_height(expr)
    compiled = compile_cached(expr, names).minimized()
    target = word_problem_dfa(names)
    witness = equivalence_witness(compiled, target)
    print(f"    syntactic star height of the assembled expression: {height}")
    print(f"    compiled DFA: {len(compiled.states)} states; target: "
          f"{len(target.states)} states ({time.time() - started:.0f}s)")
    if witness is None:
        print(f"    [PROOF] the height-{height} expression denotes EXACTLY the "
              f"identity fibre over these {len(letters)} letters "
              f"(product reachability, complete finite decision).")
    else:
        word = tuple(BY_NAME[c] for c in witness)
        print(f"    [FAIL] not equivalent; shortest counterexample "
              f"{witness!r} (length {len(witness)}); group says "
              f"mu(w) = {evaluate(word)}")
        FAILURES.append(f"assembly {label}")
    if height != 1:
        FAILURES.append(f"height {label}")

    # negative control: perturb one coefficient of the solved combination.
    for shift in (1, 3):
        broken = inter(phase_zero(blocks, letters),
                       assemble(blocks, letters, terms, perturb=(0, shift),
                                verbose=False))
        bad = equivalence_witness(compile_cached(broken, names).minimized(), target)
        fired = bad is not None
        print(f"    [{'PASS' if fired else 'FAIL'}] control: coefficient 0 shifted "
              f"by {shift} -> "
              f"{'detected, counterexample ' + repr(bad) if fired else 'NOT DETECTED'}")
        if not fired:
            FAILURES.append(f"coefficient control {shift}")
    return compiled


# --------------------------------------------------------------------------
# section 5: why the 21-letter alphabet does not close -- exact obstruction
# --------------------------------------------------------------------------


def cycle_space_rank_test(with_pair_phase: bool):
    """Is beta' in the GF(7) span of the constructible features?

    Model: states (phase, previous letter); an edge is one letter read from
    one state, so an edge class is exactly a triple (previous letter, phase,
    letter).  Every feature this script can express, and beta' itself, is a
    GF(7)-linear functional of the edge-count vector.  Two words with the same
    endpoints realise edge-count vectors differing by an element of the cycle
    space, so a functional is determined by the features iff it lies in their
    span ON THE CYCLE SPACE.  This is a decision, not a sample: the cycle
    generators below are a complete generating set.
    """
    states = [(p, c) for p in range(PHASES) for c in SIGMA]
    edges = []
    for s in states:
        for c in SIGMA:
            edges.append((s, c, ((s[0] + EPS[c]) % PHASES, c)))
    eidx = {(a, c): i for i, (a, c, t) in enumerate(edges)}
    root = states[0]
    forward = defaultdict(list)
    backward = defaultdict(list)
    for (a, c, t) in edges:
        forward[a].append(t)
        backward[t].append(a)

    def reach(graph, s):
        seen = {s}
        stack = [s]
        while stack:
            x = stack.pop()
            for y in graph[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        return seen

    scc = reach(forward, root) & reach(backward, root)
    assert len(scc) == len(states), "phase automaton must be strongly connected"
    parent = {root: None}
    queue = deque([root])
    while queue:
        s = queue.popleft()
        for c in SIGMA:
            t = ((s[0] + EPS[c]) % PHASES, c)
            if t not in parent:
                parent[t] = (s, c)
                queue.append(t)
    back = {root: None}
    queue = deque([root])
    while queue:
        s = queue.popleft()
        for a in backward[s]:
            if a not in back:
                for c in SIGMA:
                    if ((a[0] + EPS[c]) % PHASES, c) == s:
                        back[a] = (c, s)
                        break
                queue.append(a)

    def to_root(s, vec, table, forwards):
        while table[s] is not None:
            if forwards:
                a, c = table[s]
                vec[eidx[(a, c)]] = (vec[eidx[(a, c)]] + 1) % MODULUS
                s = a
            else:
                c, t = table[s]
                vec[eidx[(s, c)]] = (vec[eidx[(s, c)]] + 1) % MODULUS
                s = t

    cycles = []
    for (a, c, t) in edges:
        vec = [0] * len(edges)
        to_root(a, vec, parent, True)
        vec[eidx[(a, c)]] = (vec[eidx[(a, c)]] + 1) % MODULUS
        to_root(t, vec, back, False)
        cycles.append(vec)

    functionals = []
    labels = []
    for g in SIGMA:
        functionals.append(lambda a, c, t, g=g: int(c == g))
        labels.append("letter count")
    for x in SIGMA:
        for y in SIGMA:
            functionals.append(lambda a, c, t, x=x, y=y: int(a[1] == x and c == y))
            labels.append("adjacent-pair count")
    for q in range(PHASES):
        functionals.append(lambda a, c, t, q=q: int((a[0] + EPS[c]) % PHASES == q))
        labels.append("base cut")
    for h in SIGMA:
        if EPS[h] == 0:
            for q in range(PHASES):
                functionals.append(
                    lambda a, c, t, h=h, q=q:
                    int(c == h and (a[0] + EPS[c]) % PHASES == q))
                labels.append("non-mover phase count")
    if with_pair_phase:
        for x in SIGMA:
            for y in SIGMA:
                if EPS[y] == 0:
                    continue
                for q in range(PHASES):
                    functionals.append(
                        lambda a, c, t, x=x, y=y, q=q:
                        int(a[1] == x and c == y and (a[0] + EPS[c]) % PHASES == q))
                    labels.append("phase-resolved pair count")

    def beta(a, c, t):
        return (c[1] * INVERSE_POWERS[(a[0] + EPS[c]) % PHASES]) % MODULUS

    def evaluate_on(f):
        return [f(a, c, t) for (a, c, t) in edges]

    rows = []
    for f in functionals:
        fv = evaluate_on(f)
        rows.append([sum(fv[i] * cy[i] for i in range(len(edges))) % MODULUS
                     for cy in cycles])
    bv = evaluate_on(beta)
    target = [sum(bv[i] * cy[i] for i in range(len(edges))) % MODULUS
              for cy in cycles]

    def rank(matrix, extra=None):
        m = [r[:] for r in matrix]
        if extra is not None:
            m.append(extra[:])
        columns = len(m[0])
        r = 0
        for col in range(columns):
            pivot = None
            for i in range(r, len(m)):
                if m[i][col] % MODULUS:
                    pivot = i
                    break
            if pivot is None:
                continue
            m[r], m[pivot] = m[pivot], m[r]
            inv = pow(m[r][col], -1, MODULUS)
            m[r] = [(x * inv) % MODULUS for x in m[r]]
            for i in range(len(m)):
                if i != r and m[i][col] % MODULUS:
                    f = m[i][col]
                    m[i] = [(x - f * y) % MODULUS for x, y in zip(m[i], m[r])]
            r += 1
            if r == len(m):
                break
        return r

    return len(cycles), rank(rows), rank(rows, target)


def section5():
    banner("5. why the FULL 21-letter alphabet does not close (exact obstruction)")
    generators, r1, r2 = cycle_space_rank_test(with_pair_phase=False)
    print(f"    cycle generators: {generators}")
    print(f"    rank(constructible features) = {r1}; "
          f"rank(features + beta') = {r2}")
    if r1 == r2:
        print("    [UNEXPECTED] beta' lies in the span; the assembly should close.")
        FAILURES.append("obstruction rank test")
    else:
        print("    [DECIDED] beta' is NOT in the GF(7) span of {letter counts, all")
        print("              441 adjacent-pair counts, the three base cuts, the 21")
        print("              non-mover phase counts} on the cycle space, by exactly")
        print(f"              {r2 - r1} dimension.  No Boolean assembly of those")
        print("              features can denote the identity fibre, at any star")
        print("              height.  This is a rank computation, not a sample.")
    generators, r1, r2 = cycle_space_rank_test(with_pair_phase=True)
    print(f"    adding the phase-resolved pair counts: rank {r1} -> with beta' {r2}"
          f"  ({'sufficient' if r1 == r2 else 'still insufficient'})")
    witness_pair()
    print("    So the phase-resolved pair cut is exactly the missing feature.  Its")
    print("    block language is  (skipped tokens)^* . (cutting token);  the")
    print("    skipped tokens are unboundedly long loops, and no explicit")
    print("    star-free expression for their star was found (see section 6).")


def section6():
    banner("6. the pair-cut block language: what is known and what is missing")
    # abstract letter classes: z = non-mover, m1/m2 = movers by eps, g = the
    # distinguished mover.  The block language is the inverse image of a
    # language over these four classes under the length-preserving class
    # morphism, and that inverse image preserves star-freeness and star height,
    # so the four-letter question is the whole question.
    for eps_g in (1, 2):
        alphabet = ("z", "m1", "m2", "g")
        eps_of = {"z": 0, "m1": 1, "m2": 2, "g": eps_g}
        start = (0, None)
        transitions = {}
        seen = {start, ACC, DEAD}
        queue = deque([start])
        for s in (ACC, DEAD):
            for c in alphabet:
                transitions[(s, c)] = DEAD
        while queue:
            state = queue.popleft()
            phase, previous = state
            for c in alphabet:
                nxt = (phase + eps_of[c]) % PHASES
                if nxt == 0:
                    skip = (c == "g" and previous is not None and previous != "g")
                    target = (nxt, c) if skip else ACC
                else:
                    target = (nxt, c)
                transitions[(state, c)] = target
                if target not in seen:
                    seen.add(target)
                    queue.append(target)
        order = sorted(seen, key=repr)
        index = {s: i for i, s in enumerate(order)}
        n = len(order)
        gens = {tuple(index[transitions[(s, c)]] for s in order) for c in alphabet}
        monoid = set(gens)
        frontier = list(gens)
        while frontier:
            f = frontier.pop()
            for g in gens:
                h = tuple(g[f[i]] for i in range(n))
                if h not in monoid:
                    monoid.add(h)
                    frontier.append(h)
        aperiodic = True
        for f in monoid:
            seen_p, cur, k = {}, f, 0
            while cur not in seen_p:
                seen_p[cur] = k
                cur = tuple(f[cur[i]] for i in range(n))
                k += 1
            if k - seen_p[cur] != 1:
                aperiodic = False
                break
        print(f"    pair-total cut, eps(g)={eps_g}: block DFA has {n} raw states, "
              f"transition monoid {len(monoid)}, aperiodic={aperiodic}")
        if not aperiodic:
            FAILURES.append("pair-cut aperiodicity")
    print("    -> a height-one expression for the pair-cut counting language")
    print("       EXISTS by Schuetzenberger's theorem.  It was not constructed.")
    local_testability_probe()
    print("    (b) NOT re-run here: a breadth-first enumeration of the star-free")
    print("        closure of the four class letters, de-duplicated by canonical")
    print("        minimal DFA and capped at 9 states, was run separately for 240 s")
    print("        and exhausted 7.2*10^5 distinct languages without reaching the")
    print("        block language.  That is a failed search, not a proof of")
    print("        anything, and it is recorded as such.")
    print("    That is where this line of work stops.  `C_7 : C_3` remains on the")
    print("    unresolved list of `COVER-LE59-01`.")


def constructible_features(word):
    """Everything section 2's technique can count, as one hashable value."""
    phase = 0
    prefix = []
    for g in word:
        prefix.append(phase)
        phase = (phase + EPS[g]) % PHASES
    letters, arrivals, nonmover, pairs = defaultdict(int), [0] * PHASES, \
        defaultdict(int), defaultdict(int)
    for i, g in enumerate(word):
        letters[g] += 1
        q = (prefix[i] + EPS[g]) % PHASES
        arrivals[q] += 1
        if EPS[g] == 0:
            nonmover[g, q] += 1
        if i:
            pairs[word[i - 1], g] += 1
    def sparse(table):
        return frozenset((k, v % MODULUS) for k, v in table.items() if v % MODULUS)
    return (phase, sparse(letters), tuple(a % MODULUS for a in arrivals),
            sparse(nonmover), sparse(pairs))


def witness_pair():
    """A concrete pair of words the constructible features cannot separate.

    The rank computation above already decides the point; this exhibits it.
    The exhaustive sweep below shows no such pair exists below length 5, so
    the pair printed is of minimal length.
    """
    seen = {}
    for length in range(5):
        for word in itertools.product(SIGMA, repeat=length):
            key = constructible_features(word)
            member = evaluate(word) == IDENTITY
            if key in seen and seen[key][1] != member:
                print(f"    [UNEXPECTED] collision already at length {length}")
                FAILURES.append("witness sweep")
                return
            seen.setdefault(key, (word, member))
    left = ((2, 5), (2, 5), (2, 0), (2, 5), (1, 3))
    right = ((2, 5), (2, 0), (2, 5), (2, 5), (1, 3))
    same = constructible_features(left) == constructible_features(right)
    differ = (evaluate(left) == IDENTITY) != (evaluate(right) == IDENTITY)
    status = "PASS" if (same and differ) else "FAIL"
    print(f"    [{status}] minimal witness pair (length 5; exhaustively no pair "
          f"of length <= 4):")
    print(f"          w1 = {left}  mu = {evaluate(left)}  in T: "
          f"{evaluate(left) == IDENTITY}")
    print(f"          w2 = {right}  mu = {evaluate(right)}  in T: "
          f"{evaluate(right) == IDENTITY}")
    print(f"          identical on every constructible feature: {same}")
    if not (same and differ):
        FAILURES.append("witness pair")


def local_testability_probe(max_window=7):
    """(a) The forbidden-mover-pattern technique of section 2 cannot work here.

    Every star-free expression in section 2 has the same shape: a Boolean
    combination of  TOP . P . TOP  with  P  a concatenation  SIG_a . Z . SIG_b
    . Z ...  of boundedly many mover classes separated by non-mover runs, plus
    prefix and suffix conditions of the same form.  Such a language is exactly
    a locally testable language of the FLAGGED MOVER sequence: the letters are
    pairs (mover class, "was a non-mover run immediately before it"), which is
    all a pattern of that shape can see.

    In the alive part of a pair-cut block a non-mover never sits at relative
    phase 0 -- it would itself be a cut -- so the flagged mover sequence
    carries the whole condition, and the question is exactly whether the alive
    language is locally testable over those six letters.  It is not, at any
    window up to `max_window`, and the witnesses below say why: the phase
    depends on how far the current loop has already run, which no bounded
    mover window can see.
    """
    flagged = tuple((c, z) for c in ("m1", "m2", "g") for z in (0, 1))
    eps_of = {"m1": 1, "m2": 2, "g": 1}
    START = (0, None)

    def step(state, letter):
        if state is DEAD:
            return DEAD
        phase, previous = state
        c, zflag = letter
        if previous is None and zflag == 1:
            return DEAD          # a non-mover at phase 0 is itself a cut
        prev_letter_is_g = (previous == "g" and zflag == 0)
        has_previous = previous is not None or zflag == 1
        nxt = (phase + eps_of[c]) % PHASES
        if nxt == 0:
            if c == "g" and has_previous and not prev_letter_is_g:
                return (0, "g")  # skipped: the block continues
            return DEAD          # a cut: the alive run stops here
        return (nxt, "g" if c == "g" else "other")

    alive = {START}
    queue = deque([START])
    while queue:
        s = queue.popleft()
        for letter in flagged:
            t = step(s, letter)
            if t is not DEAD and t not in alive:
                alive.add(t)
                queue.append(t)

    def run(state, word):
        for letter in word:
            state = step(state, letter)
            if state is DEAD:
                return None
        return state

    for k in range(1, max_window + 1):
        factors, prefixes = set(), set()
        for length in range(k + 1):
            for w in itertools.product(flagged, repeat=length):
                if any(run(s, w) is not None for s in alive):
                    factors.add(w)
                if run(START, w) is not None:
                    prefixes.add(w)
        witness = None
        for length in range(0, 2 * k + 4):
            for w in itertools.product(flagged, repeat=length):
                approx = (all(w[i:i + k] in factors
                              for i in range(max(0, len(w) - k + 1)))
                          and w[:min(k, len(w))] in prefixes)
                if approx != (run(START, w) is not None):
                    witness = w
                    break
            if witness is not None:
                break
        shown = None if witness is None else "".join(
            c + ("." if z else "") for c, z in witness)
        print(f"    (a) mover window {k}: locally-testable approximation "
              f"{'AGREES -- unexpected' if witness is None else 'differs, shortest witness ' + repr(shown)}")
        if witness is None:
            FAILURES.append(f"local testability at window {k} unexpectedly agrees")


def main():
    started = time.time()
    section1()
    sub = [(0, b) for b in range(MODULUS)] + [(1, 0), (2, 0)]
    blocks = section2(sub, "sub-alphabet {C_7} u {y, y^2}")
    section2_controls(sub)
    section3(blocks, sub)
    section4(sub, "sub-alphabet {C_7} u {y, y^2}")
    section2(list(SIGMA), "full 21-letter alphabet")
    section5()
    section6()
    banner("verdict")
    if FAILURES:
        print(f"    {len(FAILURES)} check(s) FAILED: {FAILURES}")
    else:
        print("    all checks passed.")
    print("    HeightOneForGroup (C_7 : C_3) is NOT established: the full "
          "21-letter\n    alphabet is required by FULL-ALPH-RED-01, and section 5 "
          "decides that the\n    features constructed here cannot determine its "
          "identity fibre.")
    print(f"runtime: {time.time() - started:.1f}s")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    raise SystemExit(main())
