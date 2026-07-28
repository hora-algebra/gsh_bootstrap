#!/usr/bin/env python3
"""Assemble the identity fibre of `C_7 : C_3` over the FULL 21-letter alphabet.

By `FULL-ALPH-RED-01` a generalized regular expression of star height <= 1 for
`{ w : mu(w) = e }` over all 21 letters establishes `HeightOneForGroup
(C_7 : C_3)`, which would remove the group from the 24 unresolved groups of
`COVER-LE59-01`.  `notes/c7c3_expression_obstruction.md` localises the single
missing ingredient: a height-one counting language for the PHASE-RESOLVED PAIR
CUT, whose star-free block language was finally constructed by
`scripts/research/schutzenberger_size_probe.py` (shared DAG, 11,131 nodes).

WHAT THIS SCRIPT ADDS, IN ORDER.

  1. A GF(7) identity that was not previously available.  `beta'` is NOT a
     combination of the pair-cut counts alone; section 5 of
     `c7c3_expression_equivalence.py` decides that the constructible family
     misses it by one dimension, and the family that closes the gap there is
     the FULL phase-resolved pair count `#{i : w_{i-1} = x, w_i = y, P_i = q}`
     including `x = y`.  The `x = y` part is exactly the part whose block
     language is NOT aperiodic (a run of `y`s cycles the phase), so it is not
     constructible at all.  Section 1 below removes the need for it: because
     `2^0 + 2^1 + 2^2 = 7 = 0 mod 7`, a maximal run of one letter contributes
     to `beta'` an amount depending only on the arrival phase of its FIRST and
     of its LAST position, ADDITIVELY.  So `beta'` is a GF(7) combination of
     run-START and run-END counts, and both are pair cuts with `x != y`.

  2. Section 2 builds the run-start feature (the phase-resolved pair cut) as a
     height-one expression from the Schuetzenberger block, and DECIDES it
     against a reference automaton built from the semantic definition.

  3. Section 3 builds the run-end feature as the REVERSAL of the run-start
     feature -- reversal preserves star height -- and decides that too.

  4. Section 4 reproduces the 9-letter assembly of `c7c3_expression_
     equivalence.py` section 4 with this script's own combinator (positive
     control), then attempts the full 21-letter assembly under an explicit
     budget.

Every "PASS" is a complete finite decision by product reachability or by an
exhaustive traversal of a finite accumulator automaton.  No claim here rests on
testing finitely many words.  Where a budget is exhausted the script says so,
with the state count, the time and the peak RSS at that point; it never
truncates silently.
"""

from __future__ import annotations

import argparse
import itertools
import resource
import sys
import time
from collections import defaultdict, deque
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
for _p in (str(REPO), str(HERE)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from tools.regex_cert import (  # noqa: E402
    DFA,
    GRegex,
    _atomic_empty,
    _atomic_eps,
    _atomic_letter,
    _concat,
    _product,
    _star,
    equivalence_witness,
)

import c7c3_expression_equivalence as EQ  # noqa: E402
import schutzenberger_size_probe as SZ  # noqa: E402

MOD = EQ.MODULUS          # 7
PH = EQ.PHASES            # 3
POW = EQ.POWERS           # 2^q
INV = EQ.INVERSE_POWERS   # 2^-q
SIGMA = EQ.SIGMA
EPS = EQ.EPS
IDENTITY = EQ.IDENTITY
name = EQ.name
ALL_NAMES = EQ.ALL_NAMES

FAILURES: list[str] = []


def banner(text: str) -> None:
    print()
    print("=== " + text + " ===", flush=True)


def note(status: str, text: str) -> None:
    print(f"    [{status}] {text}", flush=True)
    if status == "FAIL":
        FAILURES.append(text)


def peak_rss_mb() -> float:
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / (1024 * 1024)


# --------------------------------------------------------------------------
# expression plumbing: hash-consed builder with a star, DAG compile, DAG height
# --------------------------------------------------------------------------


class Build(SZ.Builder):
    """`SZ.Builder` plus the one operator the star-free construction never uses.

    The counting languages of section 2 are height ONE, so they need a star;
    everything below it stays star-free.  Nodes are hash-consed and kept alive
    by the parent class, which is what makes the `id()`-keyed caches sound.
    """

    def star(self, arg: GRegex) -> GRegex:
        return self._node("star", (arg,), None)

    def top(self) -> GRegex:
        return self.compl(self.EMPTY)

    def power(self, arg: GRegex, n: int) -> GRegex:
        return self.concat([arg] * n) if n > 0 else self.EPS

    def inter(self, args) -> GRegex:
        return self.compl(self.union([self.compl(a) for a in args]))


def star_height(root: GRegex) -> int:
    """Syntactic star height of a shared DAG, computed without recursion."""
    height: dict[int, int] = {}
    for node in SZ._post_order(root):
        kids = [height[id(a)] for a in node.args]
        if node.op in {"empty", "eps", "letter"}:
            height[id(node)] = 0
        elif node.op in {"union", "concat"}:
            height[id(node)] = max(kids, default=0)
        elif node.op == "compl":
            height[id(node)] = kids[0]
        elif node.op == "star":
            height[id(node)] = 1 + kids[0]
        else:
            raise AssertionError(node.op)
    return height[id(root)]


def dag_nodes(root: GRegex) -> int:
    return len(SZ._post_order(root))


def measure_size(root: GRegex) -> tuple[int, int]:
    """(distinct nodes, nodes of the fully unfolded tree).

    `SZ.measure` cannot be reused: it raises on a `star` node, because the
    construction it was written for is star-free by design and these counting
    languages are not.
    """
    order = SZ._post_order(root)
    tree: dict[int, int] = {}
    for node in order:
        tree[id(node)] = 1 + sum(tree[id(a)] for a in node.args)
    return len(order), tree[id(root)]


class Budget:
    def __init__(self, seconds: float) -> None:
        self.seconds = seconds
        self.started = time.time()
        self.worst_states = 0

    def left(self) -> float:
        return self.seconds - (time.time() - self.started)

    def check(self, where: str) -> None:
        if self.left() <= 0:
            raise TimeoutError(
                f"budget of {self.seconds:.0f}s exhausted at {where}; "
                f"largest automaton so far {self.worst_states} states, "
                f"peak RSS {peak_rss_mb():.0f} MB"
            )


def compile_dag(root: GRegex, alphabet, memo: dict, budget: Budget | None = None,
                where: str = "") -> DFA:
    """Compile a shared expression DAG, exactly as `SZ.compile_dag` does.

    `compile_regex` of `tools/regex_cert.py` recurses on the syntax TREE, which
    is impossible here: the unfolded tree of the Schuetzenberger block has ~10^68
    nodes.  This walks the DAG and memoises on node identity while performing the
    very same automaton operations (`_atomic_*`, `_product`, `_concat`, `_star`),
    so the audit boundary of the checker is preserved.  `SZ.compile_dag` is the
    same function without `star`, which the height-one counting languages need.
    """
    alpha = tuple(alphabet)
    # Post-order that STOPS at nodes already compiled.  `SZ._post_order` walks
    # the whole DAG every time; here a memoised sub-expression -- the 11,131-node
    # Schuetzenberger block, above all -- must not be descended into again, both
    # because it is slow and because holding its 11,131 intermediate automata is
    # what the peak RSS is made of.
    order: list[GRegex] = []
    seen: set[int] = set()
    stack: list[tuple[GRegex, bool]] = [(root, False)]
    while stack:
        node, expanded = stack.pop()
        if expanded:
            order.append(node)
            continue
        if id(node) in seen or id(node) in memo:
            continue
        seen.add(id(node))
        stack.append((node, True))
        for child in node.args:
            if id(child) not in seen and id(child) not in memo:
                stack.append((child, False))
    for node in order:
        if id(node) in memo:
            continue
        if budget is not None:
            budget.check(where or "compile")
        if node.op == "empty":
            out = _atomic_empty(alpha)
        elif node.op == "eps":
            out = _atomic_eps(alpha)
        elif node.op == "letter":
            out = _atomic_letter(alpha, node.value)
        elif node.op == "compl":
            out = memo[id(node.args[0])].complemented().minimized()
        elif node.op == "star":
            out = _star(memo[id(node.args[0])])
        elif node.op == "union":
            acc = _atomic_empty(alpha)
            for arg in node.args:
                acc = _product(acc, memo[id(arg)], lambda x, y: x or y)
            out = acc.minimized()
        elif node.op == "concat":
            acc = _atomic_eps(alpha)
            for arg in node.args:
                acc = _concat(acc, memo[id(arg)])
            out = acc.minimized()
        else:
            raise AssertionError(node.op)
        memo[id(node)] = out
        if budget is not None:
            budget.worst_states = max(budget.worst_states, len(out.states))
    return memo[id(root)]


def compile_isolated(root: GRegex, alphabet, memo: dict, budget: Budget | None,
                     where: str) -> DFA:
    """Compile into a scratch table and publish only the root's automaton.

    The block expression has 11,131 nodes and every one of them compiles to an
    automaton; keeping all of them for each of the 24 blocks needed below is
    several gigabytes.  Only the root is ever referenced again, so the rest is
    dropped as soon as it is used.
    """
    scratch: dict = {}
    out = compile_dag(root, alphabet, scratch, budget, where)
    memo[id(root)] = out
    scratch.clear()
    return out


def rewrite(root: GRegex, builder: Build, leaf) -> GRegex:
    """Rebuild a DAG with every `letter` node replaced by `leaf(value)`."""
    memo: dict[int, GRegex] = {}
    for node in SZ._post_order(root):
        if node.op == "letter":
            memo[id(node)] = leaf(node.value)
        elif node.op == "empty":
            memo[id(node)] = builder.EMPTY
        elif node.op == "eps":
            memo[id(node)] = builder.EPS
        elif node.op == "compl":
            memo[id(node)] = builder.compl(memo[id(node.args[0])])
        elif node.op == "star":
            memo[id(node)] = builder.star(memo[id(node.args[0])])
        elif node.op == "union":
            memo[id(node)] = builder.union([memo[id(a)] for a in node.args])
        elif node.op == "concat":
            memo[id(node)] = builder.concat([memo[id(a)] for a in node.args])
        else:
            raise AssertionError(node.op)
    return memo[id(root)]


def reverse_expr(root: GRegex, builder: Build) -> GRegex:
    """The expression for the reversed language.

    Reversal commutes with union and star, reverses the factors of a
    concatenation, and commutes with complement because reversal is a bijection
    of `A*`.  It therefore preserves syntactic star height exactly.
    """
    memo: dict[int, GRegex] = {}
    for node in SZ._post_order(root):
        if node.op == "letter":
            memo[id(node)] = builder.lit(node.value)
        elif node.op == "empty":
            memo[id(node)] = builder.EMPTY
        elif node.op == "eps":
            memo[id(node)] = builder.EPS
        elif node.op == "compl":
            memo[id(node)] = builder.compl(memo[id(node.args[0])])
        elif node.op == "star":
            memo[id(node)] = builder.star(memo[id(node.args[0])])
        elif node.op == "union":
            memo[id(node)] = builder.union([memo[id(a)] for a in node.args])
        elif node.op == "concat":
            memo[id(node)] = builder.concat(
                [memo[id(a)] for a in reversed(node.args)])
        else:
            raise AssertionError(node.op)
    return memo[id(root)]


def build_reference(alphabet, start, step, is_accept) -> DFA:
    """Reachable-part DFA from a transition function on hashable states."""
    states = {start}
    queue = deque([start])
    transition = {}
    while queue:
        s = queue.popleft()
        for c in alphabet:
            t = step(s, EQ.BY_NAME[c])
            transition[(s, c)] = t
            if t not in states:
                states.add(t)
                queue.append(t)
    return DFA(tuple(alphabet), frozenset(states), start,
               frozenset(s for s in states if is_accept(s)), transition).minimized()


def decide(left: DFA, right: DFA):
    """Product reachability.  Returns (equal, witness, product states visited)."""
    return SZ.decide_equality(left, right)


# --------------------------------------------------------------------------
# section 1: the run decomposition of beta'
# --------------------------------------------------------------------------


def beta_prime(word) -> int:
    """sum_i b_i 2^{-P_i}, with P_i the prefix phase INCLUDING position i.

    `mu(w) = (T, beta)` with `beta = 2^T beta'`, so on `T = 0` the identity
    fibre is `{ T = 0 and beta' = 0 }`.  (`EQ.coordinate_formula` uses the
    suffix form; section 1 checks the two agree.)
    """
    phase, out = 0, 0
    for g in word:
        phase = (phase + EPS[g]) % PH
        out = (out + g[1] * INV[phase]) % MOD
    return out


def solve_run_coefficients(e: int):
    """A_e, B_e with (run contribution) = A_e(first phase) + B_e(last phase).

    A maximal run of one letter of `eps = e` and `C_7`-weight 1, whose first
    position arrives at phase p and whose last arrives at phase p', contributes
    `sum_{j<L} 2^{-(p + j e)}` to `beta'`.  Three consecutive terms sum to
    `2^0 + 2^1 + 2^2 = 7 = 0`, so the contribution depends only on `L mod 3`,
    and `L mod 3` is determined by `(p, p')` because `e` is invertible mod 3.
    The table is then searched for an ADDITIVE representation; that it exists is
    the point, and the search is exhaustive over the 7^6 candidates.
    """
    table = {}
    for p in range(PH):
        for s in range(PH):  # s = L mod 3
            last = (p + (s - 1) * e) % PH if s else (p + 2 * e) % PH
            table[(p, last)] = sum(INV[(p + j * e) % PH] for j in range(s)) % MOD
    for A in itertools.product(range(MOD), repeat=PH):
        for B in itertools.product(range(MOD), repeat=PH):
            if all((A[p] + B[q]) % MOD == v for (p, q), v in table.items()):
                return A, B, table
    return None, None, table


def section1(coefficients):
    banner("1. beta' as run-start plus run-end counts (exact GF(7) identity)")
    print("    A maximal run of a single letter contributes to beta' an amount")
    print("    that depends only on the arrival phase of its first and of its")
    print("    last position, ADDITIVELY, because 2^0 + 2^1 + 2^2 = 0 mod 7.")
    for e in (1, 2):
        A, B, table = coefficients[e]
        if A is None:
            note("FAIL", f"no additive (A,B) for eps={e}: {table}")
            return
        note("PASS", f"eps={e}: A={A}, B={B}  (exhaustive GF(7) search over "
                     f"{MOD ** 6} candidates; the 9 (start,end) values are "
                     f"{[table[k] for k in sorted(table)]})")

    # the identity, decided on a finite accumulator automaton.
    #   state = (phase, previous letter, beta' so far, right-hand side so far)
    # `right` accumulates the constructible features only: non-mover phase
    # counts, run STARTS with a previous letter (i >= 1), run ENDS with a
    # following letter (i <= n-2).  The two boundary runs are added at the end
    # from the first and last letter, which the state carries.
    A1, B1, _ = coefficients[1]
    A2, B2, _ = coefficients[2]
    AB = {1: (A1, B1), 2: (A2, B2)}

    start = (0, None, 0, 0, None)  # phase, prev, beta', rhs, first letter
    states = {start}
    queue = deque([start])
    transition = {}
    while queue:
        s = queue.popleft()
        phase, prev, beta, rhs, first = s
        for g in SIGMA:
            nphase = (phase + EPS[g]) % PH
            nbeta = (beta + g[1] * INV[nphase]) % MOD
            nrhs = rhs
            if EPS[g] == 0:
                nrhs = (nrhs + g[1] * INV[nphase]) % MOD
            else:
                A, B = AB[EPS[g]]
                if prev is not None and prev != g:
                    nrhs = (nrhs + g[1] * A[nphase]) % MOD
            if prev is not None and EPS[prev] != 0 and prev != g:
                A, B = AB[EPS[prev]]
                nrhs = (nrhs + prev[1] * B[phase]) % MOD
            t = (nphase, g, nbeta, nrhs, first if first is not None else g)
            transition[(s, g)] = t
            if t not in states:
                states.add(t)
                queue.append(t)

    def closed(s):
        """rhs plus the two boundary corrections, evaluated at end of word."""
        phase, prev, beta, rhs, first = s
        out = rhs
        if first is not None and EPS[first] != 0:
            A, _ = AB[EPS[first]]
            out = (out + first[1] * A[EPS[first]]) % MOD
        if prev is not None and EPS[prev] != 0:
            _, B = AB[EPS[prev]]
            out = (out + prev[1] * B[phase]) % MOD
        return out

    bad = [s for s in states if s[2] != closed(s)]
    print(f"    accumulator automaton: {len(states)} reachable states "
          f"(phase x previous letter x beta' x right-hand side x first letter)")
    if bad:
        note("FAIL", f"the identity fails in {len(bad)} reachable states, "
                     f"e.g. {bad[0]}")
    else:
        note("PASS", "beta'(w) = sum_h b_h 2^-q N[h,q] (h a non-mover) "
                     "+ sum_y b_y ( sum_p A(p) RS'[y,p] + sum_p B(p) RE'[y,p] ) "
                     "+ boundary(first letter, last letter), for EVERY word: "
                     "decided by exhausting the accumulator automaton, not "
                     "sampled.")

    # cross-check that beta' is the coordinate the group actually needs.
    mismatch = 0
    for length in range(4):
        for word in itertools.product(SIGMA, repeat=length):
            total = sum(EPS[g] for g in word) % PH
            want = EQ.evaluate(word) == IDENTITY
            got = (total == 0 and beta_prime(word) == 0)
            mismatch += want != got
    if mismatch:
        note("FAIL", f"beta' does not define the identity fibre ({mismatch})")
    else:
        note("PASS", "mu(w) = e  <->  (total phase = 0 and beta'(w) = 0), on all "
                     "9724 words of length <= 3, and by the coordinate formula "
                     "of `c7c3_expression_equivalence.py` section 1 in general.")
    return AB


# --------------------------------------------------------------------------
# section 1b: the rank test of the obstruction note, with the new family
# --------------------------------------------------------------------------


def rank_test(extra: str):
    """Is beta' in the GF(7) span of a feature family, on the cycle space?

    Same model and same cycle generators as `cycle_space_rank_test` of
    `c7c3_expression_equivalence.py`: states are (phase, previous letter), an
    edge is one letter read from one state, and a functional of edge counts is
    determined by the features exactly when it lies in their span on the cycle
    space.  `extra` selects what is added to the always-present family (letter
    counts, base cuts, non-mover phase counts).
    """
    states = [(p, c) for p in range(PH) for c in SIGMA]
    edges = [(s, c, ((s[0] + EPS[c]) % PH, c)) for s in states for c in SIGMA]
    eidx = {(a, c): i for i, (a, c, t) in enumerate(edges)}
    root = states[0]
    backward = defaultdict(list)
    for (a, c, t) in edges:
        backward[t].append(a)
    parent = {root: None}
    queue = deque([root])
    while queue:
        s = queue.popleft()
        for c in SIGMA:
            t = ((s[0] + EPS[c]) % PH, c)
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
                    if ((a[0] + EPS[c]) % PH, c) == s:
                        back[a] = (c, s)
                        break
                queue.append(a)

    def to_root(s, vec, table, forwards):
        while table[s] is not None:
            if forwards:
                a, c = table[s]
                vec[eidx[(a, c)]] = (vec[eidx[(a, c)]] + 1) % MOD
                s = a
            else:
                c, t = table[s]
                vec[eidx[(s, c)]] = (vec[eidx[(s, c)]] + 1) % MOD
                s = t

    cycles = []
    for (a, c, t) in edges:
        vec = [0] * len(edges)
        to_root(a, vec, parent, True)
        vec[eidx[(a, c)]] = (vec[eidx[(a, c)]] + 1) % MOD
        to_root(t, vec, back, False)
        cycles.append(vec)

    functionals = []
    for g in SIGMA:
        functionals.append(lambda a, c, t, g=g: int(c == g))
    for q in range(PH):
        functionals.append(lambda a, c, t, q=q: int((a[0] + EPS[c]) % PH == q))
    for h in SIGMA:
        if EPS[h] == 0:
            for q in range(PH):
                functionals.append(
                    lambda a, c, t, h=h, q=q:
                    int(c == h and (a[0] + EPS[c]) % PH == q))
    if extra == "runs":
        # run starts: previous letter differs, own letter is a mover
        for y in SIGMA:
            if EPS[y] == 0:
                continue
            for q in range(PH):
                functionals.append(
                    lambda a, c, t, y=y, q=q:
                    int(c == y and a[1] != y and (a[0] + EPS[c]) % PH == q))
                # run ends: the PREVIOUS letter is the mover, this one differs
                functionals.append(
                    lambda a, c, t, y=y, q=q:
                    int(a[1] == y and c != y and a[0] == q))
    elif extra == "pairs":
        for x in SIGMA:
            for y in SIGMA:
                functionals.append(
                    lambda a, c, t, x=x, y=y: int(a[1] == x and c == y))
    elif extra != "none":
        raise AssertionError(extra)

    def beta(a, c, t):
        return (c[1] * INV[(a[0] + EPS[c]) % PH]) % MOD

    rows = []
    for f in functionals:
        fv = [f(a, c, t) for (a, c, t) in edges]
        rows.append([sum(fv[i] * cy[i] for i in range(len(edges))) % MOD
                     for cy in cycles])
    bv = [beta(a, c, t) for (a, c, t) in edges]
    target = [sum(bv[i] * cy[i] for i in range(len(edges))) % MOD
              for cy in cycles]

    def rank(matrix, extra_row=None):
        m = [r[:] for r in matrix]
        if extra_row is not None:
            m.append(extra_row[:])
        columns = len(m[0])
        r = 0
        for col in range(columns):
            pivot = next((i for i in range(r, len(m)) if m[i][col] % MOD), None)
            if pivot is None:
                continue
            m[r], m[pivot] = m[pivot], m[r]
            inv = pow(m[r][col], -1, MOD)
            m[r] = [(x * inv) % MOD for x in m[r]]
            for i in range(len(m)):
                if i != r and m[i][col] % MOD:
                    f = m[i][col]
                    m[i] = [(x - f * y) % MOD for x, y in zip(m[i], m[r])]
            r += 1
            if r == len(m):
                break
        return r

    return len(cycles), rank(rows), rank(rows, target)


def section1b():
    banner("1b. the same rank test as the obstruction note, on the new family")
    for label, key in (("letter counts + base cuts + non-mover phase counts",
                        "none"),
                       ("... + all 441 adjacent-pair counts", "pairs"),
                       ("... + run-start and run-end phase counts", "runs")):
        gens, r1, r2 = rank_test(key)
        verdict = "IN THE SPAN" if r1 == r2 else f"OUT by {r2 - r1}"
        print(f"    {label:<52} rank {r1:>5} -> {r2:<5}  beta' {verdict}",
              flush=True)
        if key == "runs" and r1 != r2:
            note("FAIL", "the run family does not span beta' after all")
        if key == "pairs" and r1 == r2:
            note("FAIL", "the adjacent-pair family unexpectedly spans beta'")


# --------------------------------------------------------------------------
# section 2: the phase-resolved pair cut, as a height-one counting language
# --------------------------------------------------------------------------

CLASS_ALPHABET = ("z", "m1", "m2", "g")


def class_map(y):
    """The letter-to-letter morphism 21 letters -> {z, m1, m2, g} for `y`."""
    e = EPS[y]
    assert e != 0
    out = {}
    for g in SIGMA:
        if g == y:
            out[g] = "g"
        elif EPS[g] == 0:
            out[g] = "z"
        else:
            out[g] = f"m{EPS[g]}"
    return out


def block_expression(eps_g: int, seconds: float):
    """The Schuetzenberger star-free expression for the pair-cut block.

    Delegates to `schutzenberger_size_probe.star_free_expression`, which
    implements the local divisor induction of Diekert-Kufleitner; nothing about
    the construction is re-implemented here.
    """
    budget = SZ.Budget(seconds, 200_000_000)
    started = time.time()
    expr, builder, md, facts = SZ.star_free_expression(SZ.block_dfa(eps_g), budget)
    return expr, builder, md, facts, time.time() - started


def lift_block(expr, builder: Build, y):
    """Substitute each class letter by the union of the 21 letters mapping to it."""
    cmap = class_map(y)
    members = defaultdict(list)
    for g in SIGMA:
        members[cmap[g]].append(name(g))
    leaves = {c: builder.union([builder.lit(n) for n in sorted(members[c])])
              for c in CLASS_ALPHABET}
    return rewrite(expr, builder, lambda v: leaves[v])


def lifted_block_reference(eps_g: int, y):
    """The 21-letter block language, straight from the class automaton."""
    md = SZ.block_dfa(eps_g)
    cmap = class_map(y)
    return build_reference(
        ALL_NAMES, md.start,
        lambda s, g: md.step(s, cmap[g]),
        lambda s: s in md.accept)


def pair_cut_reference(y, q: int, r: int):
    """{ w : #(arrivals at phase q that are NOT a skipped one) = r mod 7 }.

    A skipped arrival is one whose letter is `y` and whose immediately preceding
    letter exists and differs from `y`; so the skipped arrivals at phase q are
    exactly the run-starts of `y` arriving at phase q, apart from a run starting
    at position 0.  The base cut `Z_q` is already available, so counting the
    complement is the same information.
    """
    def step(s, g):
        phase, prev, k = s
        nxt = (phase + EPS[g]) % PH
        skipped = (g == y and prev is not None and prev != y)
        if nxt == q and not skipped:
            k = (k + 1) % MOD
        return (nxt, g, k)

    return build_reference(ALL_NAMES, (0, None, 0), step,
                           lambda s: s[2] == r % MOD)


def run_end_reference(y, p: int, r: int, phase_zero: bool):
    """{ w : total phase 0 and RE'[y,p] = r mod 7 }, RE' excluding the last run.

    RE'[y,p] counts the positions i <= n-2 with w_i = y, w_{i+1} != y and
    P_i = p -- the run ENDS of `y` that are followed by another letter.
    """
    def step(s, g):
        phase, prev, k = s
        if prev == y and g != y and phase == p:
            k = (k + 1) % MOD
        return ((phase + EPS[g]) % PH, g, k)

    return build_reference(
        ALL_NAMES, (0, None, 0), step,
        lambda s: s[2] == r % MOD and (s[0] == 0 or not phase_zero))


def pair_cut_feature(blocks, builder: Build, y, block, q: int, r: int) -> GRegex:
    """Height-one expression for the pair cut at phase q, count = r mod 7.

    Exactly the shape of `cut_feature` in `c7c3_expression_equivalence.py`
    section 3 -- opener, then blocks, then a tail with no further cut -- with the
    star-free `skip^* . cutting` block replaced by the Schuetzenberger block,
    which is what section 3 could not supply.  The only new step is deciding
    whether the FIRST arrival at phase q is itself skipped, which is a star-free
    condition on the last two letters of the opener.
    """
    TOP = builder.top()
    lit_y = builder.lit(name(y))
    others = builder.union([builder.lit(name(g)) for g in SIGMA if g != y])
    opener = rewrite(blocks.opener(q), builder, builder.lit)
    no_cut = rewrite(blocks.no_cut(q), builder, builder.lit)
    skipped_shape = builder.concat([TOP, others, lit_y])
    opener_skipped = builder.inter([opener, skipped_shape])
    opener_counted = builder.inter([opener, builder.compl(skipped_shape)])
    tail = builder.compl(builder.concat([block, TOP]))
    first = builder.union([opener_counted,
                           builder.concat([opener_skipped, block])])
    nothing = builder.union([no_cut, builder.concat([opener_skipped, tail])])
    body = builder.concat([first,
                           builder.power(block, (r - 1) % MOD),
                           builder.star(builder.power(block, MOD)),
                           tail])
    return builder.union([nothing, body]) if r % MOD == 0 else body


def section2(builder: Build, blocks, y, memo, budget: Budget, verbose=True):
    """Build and DECIDE the pair-cut feature for one mover letter `y`."""
    eps_g = EPS[y]
    expr, sbuilder, md, facts, build_time = block_expression(eps_g, 900.0)
    if verbose:
        print(f"    block language for eps(g)={eps_g}: minimal DFA "
              f"{facts['min_states']} states, syntactic monoid {facts['monoid']}, "
              f"aperiodic={facts['aperiodic']}, built in {build_time:.2f}s")
        print(f"    class-level expression: {dag_nodes(expr):,} shared DAG nodes, "
              f"star height {star_height(expr)}")
    lifted = lift_block(expr, builder, y)
    t0 = time.time()
    compiled = compile_isolated(lifted, ALL_NAMES, memo, budget,
                                f"block lift for {name(y)}").minimized()
    memo[id(lifted)] = compiled
    compile_isolated(reverse_expr(lifted, builder), ALL_NAMES, memo, budget,
                     f"reversed block lift for {name(y)}")
    lift_time = time.time() - t0
    reference = lifted_block_reference(eps_g, y)
    equal, witness, visited = decide(compiled, reference)
    note("PASS" if equal else "FAIL",
         f"lifted block over 21 letters equals the class automaton's inverse "
         f"image: equal={equal}, product states visited {visited}, compiled "
         f"{len(compiled.states)} states, {lift_time:.1f}s "
         f"({dag_nodes(lifted):,} DAG nodes)")
    if not equal:
        print(f"        distinguishing word {witness!r}")
        return None
    return lifted


def check_feature(builder: Build, blocks, y, block, q, r, memo, budget,
                  label=""):
    expr = pair_cut_feature(blocks, builder, y, block, q, r)
    height = star_height(expr)
    t0 = time.time()
    compiled = compile_dag(expr, ALL_NAMES, memo, budget,
                           f"pair cut {label}").minimized()
    elapsed = time.time() - t0
    reference = pair_cut_reference(y, q, r)
    equal, witness, visited = decide(compiled, reference)
    ok = equal and height <= 1
    note("PASS" if ok else "FAIL",
         f"pair cut y={name(y)} phase {q} count={r} mod 7: star height {height}, "
         f"equal={equal}, product states visited {visited}, compiled "
         f"{len(compiled.states)} states vs reference {len(reference.states)}, "
         f"{elapsed:.1f}s")
    if not equal:
        print(f"        shortest distinguishing word {witness!r}")
    return expr, compiled, ok


# --------------------------------------------------------------------------
# section 4: GF(7) assembly
# --------------------------------------------------------------------------


def assemble(builder: Build, families, memo, budget: Budget, alphabet,
             verbose=True):
    """Expression for `sum_k coef_k f_k = 0 mod 7`, compiled as it is built.

    `families[k] = (coef, [L_0 .. L_6])` with `L_j` denoting `f_k = j mod 7`.
    Compiling after each feature is what makes the cost visible: a silent build
    followed by one compile would report nothing until it either finished or
    died.
    """
    partial = None
    for index, (coef, family, label) in enumerate(families):
        t0 = time.time()
        inv = pow(coef, -1, MOD)
        if partial is None:
            partial = [family[(r * inv) % MOD] for r in range(MOD)]
        else:
            partial = [
                builder.union([
                    builder.inter([partial[s], family[((r - s) * inv) % MOD]])
                    for s in range(MOD)
                ])
                for r in range(MOD)
            ]
        sizes = []
        for r in range(MOD):
            sizes.append(len(compile_dag(partial[r], alphabet, memo, budget,
                                         f"assembly step {index + 1}").states))
        if verbose:
            print(f"      feature {index + 1}/{len(families)} ({label}): "
                  f"partial DFAs {max(sizes)} states max, "
                  f"{time.time() - t0:.1f}s, RSS {peak_rss_mb():.0f} MB",
                  flush=True)
    return partial[0]


def nonmover_terms(letters):
    """beta_functional of `c7c3_expression_equivalence.py`, as (coef, q, skip)."""
    nonmovers = [g for g in letters if EPS[g] == 0]
    terms = []
    for q in range(PH):
        weight = INV[q]
        terms.append(((MOD - 1) * weight % MOD, q, frozenset()))
        for j in range(1, MOD):
            skip = frozenset(h for h in nonmovers if h[1] >= j)
            terms.append(((-weight) % MOD, q, skip))
    return [t for t in terms if t[0] % MOD]


def correction_value(AB, first, last) -> int:
    """A(eps(first)) b_first + B(0) b_last, the two boundary runs.

    `RS'` misses a run that starts at position 0 and `RE'` misses the run that
    ends at the last position; on words of total phase 0 the last position sits
    at phase 0, so both corrections are functions of the first and the last
    letter alone.  A one-letter word is both, and gets both terms.
    """
    out = 0
    if first is not None and EPS[first] != 0:
        out = (out + first[1] * AB[EPS[first]][0][EPS[first]]) % MOD
    if last is not None and EPS[last] != 0:
        out = (out + last[1] * AB[EPS[last]][1][0]) % MOD
    return out


def correction_family(builder: Build, AB):
    """Star-free classes of the boundary correction, by first and last letter."""
    TOP = builder.top()
    buckets = defaultdict(list)
    for f in SIGMA:
        buckets[correction_value(AB, f, f)].append(builder.lit(name(f)))
        for l in SIGMA:
            buckets[correction_value(AB, f, l)].append(
                builder.concat([builder.lit(name(f)), TOP, builder.lit(name(l))]))
    buckets[0].append(builder.EPS)
    return [builder.union(list(buckets.get(value, ()))) for value in range(MOD)]


def correction_reference(AB, value: int) -> DFA:
    return build_reference(
        ALL_NAMES, (None, None),
        lambda s, g: (s[0] if s[0] is not None else g, g),
        lambda s: correction_value(AB, s[0], s[1]) == value % MOD)


# --------------------------------------------------------------------------
# stages
# --------------------------------------------------------------------------


def stage_compiler_control(budget: Budget):
    """Does the DAG compiler agree with `tools/regex_cert.py`'s tree recursion?

    Everything below rests on `compile_dag` and on this file's `star_height`,
    neither of which is the repository's checker: `compile_regex` recurses on
    the syntax tree and cannot be run on the block expression at all.  If the
    two disagreed, every decision in this script would be about a language the
    checker does not recognise.  So they are compared, on expressions small
    enough for the tree recursion and containing STARS, since the star is the
    operator the DAG walk adds.
    """
    from tools.regex_cert import compile_regex  # noqa: PLC0415

    banner("0. CONTROL: the DAG compiler against the repository's tree compiler")
    letters = [(0, 0), (0, 1), (1, 0)]
    names = tuple(name(g) for g in letters)
    builder = Build()
    blocks = EQ.Blocks(letters)
    memo: dict = {}
    cases = {
        "cut at phase 1, count 2 mod 7":
            rewrite(EQ.cut_feature(blocks, 1, frozenset(), 2), builder,
                    builder.lit),
        "cut at phase 0, count 0 mod 7":
            rewrite(EQ.cut_feature(blocks, 0, frozenset(), 0), builder,
                    builder.lit),
        "letter count mod 3":
            rewrite(EQ.letter_count_feature(blocks, frozenset([(1, 0)]), 1, 3),
                    builder, builder.lit),
        "total phase 0":
            rewrite(EQ.phase_zero(blocks, letters), builder, builder.lit),
        "a bare star":
            builder.star(builder.lit(name((0, 1)))),
        "a star inside a concatenation":
            builder.concat([builder.star(builder.union(
                [builder.lit(name((0, 0))), builder.lit(name((1, 0)))])),
                builder.top()]),
    }
    ok = True
    for label, expr in cases.items():
        mine = compile_dag(expr, names, memo, budget, "compiler control").minimized()
        theirs = compile_regex(expr, names).minimized()
        witness = equivalence_witness(mine, theirs)
        heights = (star_height(expr), expr.star_height())
        good = witness is None and heights[0] == heights[1]
        note("PASS" if good else "FAIL",
             f"{label}: DAG compile {len(mine.states)} states, tree compile "
             f"{len(theirs.states)} states, agree={witness is None}, star "
             f"height {heights[0]} vs {heights[1]}")
        ok = ok and good
    return ok


def stage_positive_control(budget: Budget):
    """The 9-letter assembly of section 4 of the obstruction script, again.

    If this script's own combinator cannot reproduce a result that is already
    established, nothing else it prints means anything.
    """
    banner("4a. POSITIVE CONTROL: the 9-letter sub-alphabet, with this "
           "script's combinator")
    letters = [(0, b) for b in range(MOD)] + [(1, 0), (2, 0)]
    names = tuple(name(g) for g in letters)
    builder = Build()
    blocks = EQ.Blocks(letters)
    memo: dict = {}
    families = []
    for coef, q, skip in nonmover_terms(letters):
        family = [rewrite(EQ.cut_feature(blocks, q, skip, r), builder,
                          builder.lit) for r in range(MOD)]
        families.append((coef, family, f"cut q={q} |skip|={len(skip)}"))
    expr = assemble(builder, families, memo, budget, names, verbose=False)
    phase = rewrite(EQ.phase_zero(blocks, letters), builder, builder.lit)
    whole = builder.inter([phase, expr])
    height = star_height(whole)
    compiled = compile_dag(whole, names, memo, budget, "9-letter").minimized()
    target = EQ.word_problem_dfa(names)
    equal, witness, visited = decide(compiled, target)
    note("PASS" if (equal and height == 1) else "FAIL",
         f"9-letter identity fibre: star height {height}, equal={equal}, "
         f"product states visited {visited}, compiled {len(compiled.states)} "
         f"states vs target {len(target.states)}")
    if not equal:
        print(f"        distinguishing word {witness!r}")
    return equal and height == 1


def stage_features(budget: Budget, movers=None, verbose=True):
    """Stages 1-2: build and decide the pair-cut features over 21 letters."""
    banner("2. STAGE 1-2: the phase-resolved pair cut over all 21 letters")
    builder = Build()
    blocks = EQ.Blocks(list(SIGMA))
    memo: dict = {}
    if movers is None:
        movers = [(1, 1), (2, 1)]
    blocks_by_letter = {}
    for y in movers:
        lifted = section2(builder, blocks, y, memo, budget)
        if lifted is None:
            return None
        blocks_by_letter[y] = lifted
        for q in range(PH):
            for r in (0, 1, 3):
                _, _, ok = check_feature(builder, blocks, y, lifted, q, r,
                                         memo, budget, label=f"{name(y)}")
                if not ok:
                    return None
    return builder, blocks, memo, blocks_by_letter


def stage_negative_control(builder: Build, blocks, y, block, memo,
                           budget: Budget):
    banner("2b. NEGATIVE CONTROL: break the feature and watch the decision fail")
    q, r = 1, 1
    reference = pair_cut_reference(y, q, r)
    TOP = builder.top()
    lit_y = builder.lit(name(y))
    others = builder.union([builder.lit(name(g)) for g in SIGMA if g != y])
    opener = rewrite(blocks.opener(q), builder, builder.lit)
    no_cut = rewrite(blocks.no_cut(q), builder, builder.lit)
    skipped_shape = builder.concat([TOP, others, lit_y])
    opener_skipped = builder.inter([opener, skipped_shape])
    opener_counted = builder.inter([opener, builder.compl(skipped_shape)])
    tail = builder.compl(builder.concat([block, TOP]))

    mutants = {}
    # (a) forget that the first arrival may itself be skipped
    mutants["first arrival never skipped"] = builder.concat(
        [opener, builder.power(block, (r - 1) % MOD),
         builder.star(builder.power(block, MOD)), tail])
    # (b) count blocks modulo 6 instead of modulo 7
    mutants["blocks counted mod 6"] = builder.concat(
        [builder.union([opener_counted,
                        builder.concat([opener_skipped, block])]),
         builder.power(block, (r - 1) % MOD),
         builder.star(builder.power(block, MOD - 1)), tail])
    # (c) drop the tail condition
    mutants["tail condition dropped"] = builder.concat(
        [builder.union([opener_counted,
                        builder.concat([opener_skipped, block])]),
         builder.power(block, (r - 1) % MOD),
         builder.star(builder.power(block, MOD)), TOP])
    # (d) reverse the two factors of the opener shape
    mutants["skip shape reversed"] = builder.concat(
        [builder.union([
            builder.inter([opener, builder.compl(
                builder.concat([TOP, lit_y, others]))]),
            builder.concat([builder.inter([
                opener, builder.concat([TOP, lit_y, others])]), block])]),
         builder.power(block, (r - 1) % MOD),
         builder.star(builder.power(block, MOD)), tail])

    fired = 0
    for label, mutant in mutants.items():
        compiled = compile_dag(mutant, ALL_NAMES, memo, budget,
                               "negative control").minimized()
        equal, witness, visited = decide(compiled, reference)
        if equal:
            note("FAIL", f"mutation '{label}' was NOT detected")
        else:
            fired += 1
            note("PASS", f"mutation '{label}' detected: product states visited "
                         f"{visited}, shortest distinguishing word "
                         f"{''.join(witness)!r}")
    return fired == len(mutants)


def reverse_dfa(machine: DFA) -> DFA:
    """The DFA of the reversed language, by the subset construction."""
    backward: dict = defaultdict(set)
    for (s, c), t in machine.transition.items():
        backward[(t, c)].add(s)
    start = frozenset(machine.accept)
    states = {start}
    queue = deque([start])
    transition = {}
    while queue:
        S = queue.popleft()
        for c in machine.alphabet:
            T = frozenset().union(*[backward[(s, c)] for s in S]) if S \
                else frozenset()
            transition[(S, c)] = T
            if T not in states:
                states.add(T)
                queue.append(T)
    return DFA(machine.alphabet, frozenset(states), start,
               frozenset(S for S in states if machine.start in S),
               transition).minimized()


def phase_zero_dfa():
    return build_reference(ALL_NAMES, 0, lambda s, g: (s + EPS[g]) % PH,
                           lambda s: s == 0)


def run_end_forward_reference(y, p: int, q: int, r: int) -> DFA:
    """{ w : total phase 0 and (reversed base cut at q) - RE'[y,p] = r mod 7 }.

    Built FORWARD, from the semantic definition, with no reversal anywhere: the
    reversed arrival phase of position i is `eps(w_i) - P_i` on words of total
    phase 0, which a left-to-right automaton can evaluate as it goes, and
    `RE'[y,p]` counts the positions i <= n-2 with w_i = y, w_{i+1} != y and
    P_i = p.  Deciding this against the reversal of the pair-cut reference is
    what turns "a run end is a run start of the reversed word" from an argument
    into a decision.
    """
    def step(s, g):
        phase, prev, k = s
        if prev == y and g != y and phase == p:
            k = (k - 1) % MOD
        nxt = (phase + EPS[g]) % PH
        if (EPS[g] - nxt) % PH == q:
            k = (k + 1) % MOD
        return (nxt, g, k)

    return build_reference(ALL_NAMES, (0, None, 0), step,
                           lambda s: s[0] == 0 and s[2] == r % MOD)


def stage_reversal(builder: Build, blocks, y, block, memo, budget: Budget):
    banner("3. STAGE 1b: the run-END feature, as the reversal of the run-start "
           "feature")
    print("    On words of total phase 0 the arrival phase of position i in the")
    print("    reversed word is eps(w_i) - P_i, so a run END of `y` at phase p in")
    print("    `w` is a run START of `y` at phase eps(y) - p in `w` reversed.")
    print("    (i) is that claim true, and (ii) does `reverse_expr` implement the")
    print("    reversal?  Both are decided, separately, below.")
    phase_dfa = phase_zero_dfa()
    phase_expr = rewrite(EQ.phase_zero(blocks, list(SIGMA)), builder,
                         builder.lit)
    ok = True
    for p in range(PH):
        q = (EPS[y] - p) % PH
        for r in (0, 2):
            forward_ref = pair_cut_reference(y, q, r)
            reversed_ref = _product(reverse_dfa(forward_ref), phase_dfa,
                                    lambda a, b: a and b)
            semantic = run_end_forward_reference(y, p, q, r)
            equal, witness, visited = decide(reversed_ref, semantic)
            note("PASS" if equal else "FAIL",
                 f"(i) reversing the phase-{q} pair-cut automaton for "
                 f"{name(y)} counts the run ends at phase {p}: equal={equal}, "
                 f"product states visited {visited}")
            if not equal:
                print(f"        shortest distinguishing word {witness!r}")
                ok = False
                continue
            expr = pair_cut_feature(blocks, builder, y, block, q, r)
            whole = builder.inter([reverse_expr(expr, builder), phase_expr])
            height = star_height(whole)
            t0 = time.time()
            compiled = compile_dag(whole, ALL_NAMES, memo, budget,
                                   "reversal").minimized()
            equal, witness, visited = decide(compiled, semantic)
            note("PASS" if (equal and height <= 1) else "FAIL",
                 f"(ii) the reversed EXPRESSION denotes it: star height "
                 f"{height}, equal={equal}, product states visited {visited}, "
                 f"{len(compiled.states)} states, {time.time() - t0:.1f}s")
            if not equal:
                print(f"        shortest distinguishing word {witness!r}")
                ok = False
    return ok


def build_families(builder: Build, blocks, AB, blocks_by_letter):
    """Every GF(7) term of the identity, with the reference that defines it.

    Each entry is `(coefficient, [L_0..L_6], [reference_0..reference_6], label)`.
    The references are automaton constructions from the semantic definition and
    share no code with the expressions.

    Terms that name the SAME feature are folded into one entry with the summed
    coefficient before anything is compiled.  This matters: the run terms are
    stated as `RS'[y,p] = Z_p - C_y[p]`, so a naive listing repeats the base cut
    at phase p once per mover, and the assembly cost is linear in the number of
    entries.
    """
    coefficients: dict = {}
    payload: dict = {}
    order: list = []
    # The reversed features are conjoined with "total phase 0" as they are
    # built.  The assembled expression is intersected with that condition
    # anyway, so on the words that decide the answer nothing changes; what
    # changes is the size, because a reversed pair cut needs 686 states on its
    # own and 28 once the total phase is pinned.
    phase_expr = rewrite(EQ.phase_zero(blocks, list(SIGMA)), builder,
                         builder.lit)
    phase_dfa = phase_zero_dfa()

    def pinned(expr):
        return builder.inter([expr, phase_expr])

    def pinned_dfa(machine):
        return _product(machine, phase_dfa, lambda a, b: a and b)

    def add(key, coef, make_family, make_refs, label):
        coef %= MOD
        if key not in coefficients:
            coefficients[key] = 0
            payload[key] = (make_family, make_refs, label)
            order.append(key)
        coefficients[key] = (coefficients[key] + coef) % MOD

    for coef, q, skip in nonmover_terms(list(SIGMA)):
        add(("cut", q, skip), coef,
            lambda q=q, skip=skip: [rewrite(EQ.cut_feature(blocks, q, skip, r),
                                            builder, builder.lit)
                                    for r in range(MOD)],
            lambda q=q, skip=skip: [EQ.cut_count_reference(ALL_NAMES, q, skip, r)
                                    for r in range(MOD)],
            f"cut q={q} |skip|={len(skip)}")

    movers = [y for y in SIGMA if EPS[y] != 0 and y[1] != 0]
    # RS'[y,p] = Z_p - C_y[p] and RE'[y,p] = Z_q(reversed) - C_y[q](reversed)
    # with q = eps(y) - p, so each run term contributes a pair-cut feature with
    # the negated coefficient and a base cut with the original one.
    for y in movers:
        block = blocks_by_letter[y]
        A, B = AB[EPS[y]]
        for p in range(PH):
            if A[p] % MOD:
                weight = (y[1] * A[p]) % MOD
                add(("pair", y, p), -weight,
                    lambda y=y, p=p, block=block:
                    [pair_cut_feature(blocks, builder, y, block, p, r)
                     for r in range(MOD)],
                    lambda y=y, p=p: [pair_cut_reference(y, p, r)
                                      for r in range(MOD)],
                    f"pair cut {name(y)} phase {p}")
                add(("cut", p, frozenset()), weight,
                    lambda p=p: [rewrite(EQ.cut_feature(blocks, p, frozenset(), r),
                                         builder, builder.lit)
                                 for r in range(MOD)],
                    lambda p=p: [EQ.cut_count_reference(ALL_NAMES, p,
                                                        frozenset(), r)
                                 for r in range(MOD)],
                    f"cut q={p} |skip|=0")
        for p in range(PH):
            if B[p] % MOD:
                q = (EPS[y] - p) % PH
                weight = (y[1] * B[p]) % MOD
                add(("rpair", y, q), -weight,
                    lambda y=y, q=q, block=block:
                    [pinned(reverse_expr(
                        pair_cut_feature(blocks, builder, y, block, q, r),
                        builder)) for r in range(MOD)],
                    lambda y=y, q=q: [pinned_dfa(
                        reverse_dfa(pair_cut_reference(y, q, r)))
                        for r in range(MOD)],
                    f"reversed pair cut {name(y)} phase {q}")
                add(("rcut", q), weight,
                    lambda q=q: [pinned(reverse_expr(
                        rewrite(EQ.cut_feature(blocks, q, frozenset(), r),
                                builder, builder.lit), builder))
                        for r in range(MOD)],
                    lambda q=q: [pinned_dfa(reverse_dfa(EQ.cut_count_reference(
                        ALL_NAMES, q, frozenset(), r))) for r in range(MOD)],
                    f"reversed cut q={q}")
    add(("corr",), 1,
        lambda: correction_family(builder, AB),
        lambda: [correction_reference(AB, r) for r in range(MOD)],
        "boundary correction")

    families = []
    for key in order:
        coef = coefficients[key]
        if coef % MOD == 0:
            continue
        make_family, make_refs, label = payload[key]
        families.append((coef, make_family(), make_refs(), label))
    return families


def verify_families(families, memo, budget: Budget) -> bool:
    """Decide EVERY member of EVERY family against its semantic reference."""
    ok = True
    checked = 0
    t0 = time.time()
    for coef, family, refs, label in families:
        worst = 0
        for r in range(MOD):
            height = star_height(family[r])
            compiled = compile_dag(family[r], ALL_NAMES, memo, budget,
                                   f"verify {label}").minimized()
            equal, witness, visited = decide(compiled, refs[r])
            checked += 1
            worst = max(worst, visited)
            if not equal or height > 1:
                note("FAIL", f"{label}, residue {r}: height {height}, "
                             f"equal={equal}, witness {witness!r}")
                ok = False
        print(f"      verified {label:<52} coefficient {coef}, "
              f"<= {worst} product states", flush=True)
    note("PASS" if ok else "FAIL",
         f"{checked} feature languages decided against their references in "
         f"{time.time() - t0:.0f}s")
    return ok


def stage_full_assembly(builder: Build, blocks, memo, budget: Budget, AB,
                        blocks_by_letter):
    banner("4b. STAGE 3-4: the full 21-letter assembly")
    phase_expr = rewrite(EQ.phase_zero(blocks, list(SIGMA)), builder,
                         builder.lit)
    got = compile_dag(phase_expr, ALL_NAMES, memo, budget, "phase").minimized()
    equal, witness, visited = decide(got, phase_zero_dfa())
    note("PASS" if (equal and star_height(phase_expr) == 1) else "FAIL",
         f"total phase 0 over 21 letters: star height "
         f"{star_height(phase_expr)}, equal={equal}, product states visited "
         f"{visited}, {len(got.states)} states")
    t0 = time.time()
    families = build_families(builder, blocks, AB, blocks_by_letter)
    print(f"    {len(families)} GF(7) features, built in {time.time() - t0:.0f}s")
    if not verify_families(families, memo, budget):
        note("FAIL", "a feature does not denote what the identity needs; the "
                     "assembly below would be meaningless")
        return False
    families = [(coef, family, label) for coef, family, refs, label in families]
    try:
        expr = assemble(builder, families, memo, budget, ALL_NAMES)
    except (TimeoutError, MemoryError) as stop:
        note("STOP", f"assembly aborted: {stop}")
        return False
    phase = rewrite(EQ.phase_zero(blocks, list(SIGMA)), builder, builder.lit)
    whole = builder.inter([phase, expr])
    height = star_height(whole)
    try:
        compiled = compile_dag(whole, ALL_NAMES, memo, budget,
                               "final").minimized()
    except (TimeoutError, MemoryError) as stop:
        note("STOP", f"final compile aborted: {stop}")
        return False
    target = EQ.word_problem_dfa(ALL_NAMES)
    equal, witness, visited = decide(compiled, target)
    dag, tree = measure_size(whole)
    print(f"    assembled expression: {dag:,} shared DAG nodes, unfolded tree "
          f"{SZ.digits(tree)}")
    note("PASS" if (equal and height == 1) else "FAIL",
         f"21-letter identity fibre: star height {height}, equal={equal}, "
         f"product states visited {visited}, compiled {len(compiled.states)} "
         f"states vs target {len(target.states)}")
    if not equal:
        print(f"        shortest distinguishing word {witness!r}")
        return False
    if height != 1:
        return False

    # A checker that always answered "equal" would have printed the line above
    # unchanged, so the same decision procedure is now run on expressions that
    # are known to be wrong.  Each mutation is minimal: one GF(7) coefficient,
    # one dropped conjunct, one dropped feature.
    print("    negative controls on the assembled expression:", flush=True)
    fired = 0
    trials = 0
    # The perturbed coefficient is one of the LAST features: the combinator
    # folds features left to right and every node before the perturbation is
    # shared with the correct build, so a control costs one step rather than a
    # second full assembly.  Which feature is perturbed is irrelevant to what
    # the control shows -- any single wrong coefficient must be caught.
    for index, shift in ((len(families) - 1, 1), (len(families) - 2, 3)):
        broken = list(families)
        coef, family, label = broken[index]
        broken[index] = ((coef + shift) % MOD or 1, family, label)
        trials += 1
        try:
            bad = builder.inter(
                [phase, assemble(builder, broken, memo, budget, ALL_NAMES,
                                 verbose=False)])
            got = compile_dag(bad, ALL_NAMES, memo, budget, "control").minimized()
        except (TimeoutError, MemoryError) as stop:
            note("STOP", f"control (coefficient shifted by {shift}) aborted: "
                         f"{stop}")
            continue
        ok, w, seen = decide(got, target)
        fired += not ok
        note("PASS" if not ok else "FAIL",
             f"control: coefficient of feature {index} ({label}) shifted by "
             f"{shift} -> "
             f"{'detected, shortest witness ' + repr(''.join(w)) if not ok else 'NOT DETECTED'}"
             f" ({seen} product states)")
    trials += 1
    got = compile_dag(phase, ALL_NAMES, memo, budget, "control").minimized()
    ok, w, seen = decide(got, target)
    fired += not ok
    note("PASS" if not ok else "FAIL",
         f"control: the beta' conjunct dropped, total phase 0 alone -> "
         f"{'detected, shortest witness ' + repr(''.join(w)) if not ok else 'NOT DETECTED'}"
         f" ({seen} product states)")

    # Dropping the OUTER total-phase conjunct is deliberately NOT offered as a
    # control: it is redundant, and redundant by construction, because every
    # reversed feature was conjoined with total phase 0 when it was built (see
    # `build_families`).  That is checked here rather than assumed, and the
    # check is a decision, so the redundancy cannot be hiding a difference.
    got = compile_dag(expr, ALL_NAMES, memo, budget, "redundancy").minimized()
    same, w, seen = decide(got, compiled)
    note("PASS" if same else "FAIL",
         f"the outer total-phase conjunct is redundant: the beta' conjunct "
         f"alone already equals the assembled language ({seen} product states) "
         f"-- because the reversed features carry it. Not counted as a control.")
    if not same:
        print(f"        distinguishing word {w!r}")

    for index in (len(families) - 1, len(families) - 2):
        dropped = [f for i, f in enumerate(families) if i != index]
        trials += 1
        try:
            bad = builder.inter(
                [phase, assemble(builder, dropped, memo, budget, ALL_NAMES,
                                 verbose=False)])
            got = compile_dag(bad, ALL_NAMES, memo, budget,
                              "control").minimized()
            ok, w, seen = decide(got, target)
            fired += not ok
            note("PASS" if not ok else "FAIL",
                 f"control: feature {index} ({families[index][2]}) removed "
                 f"entirely -> "
                 f"{'detected, shortest witness ' + repr(''.join(w)) if not ok else 'NOT DETECTED'}"
                 f" ({seen} product states)")
        except (TimeoutError, MemoryError) as stop:
            note("STOP", f"control (feature {index} removed) aborted: {stop}")
    return fired == trials


def main() -> int:
    parser = argparse.ArgumentParser()
    # The full run is 1,722 s and CI kills a research script at 300 s in
    # EITHER tier, so the no-argument run -- which is the run
    # scripts/ci/run_research.py makes -- is the cheap prefix: the DAG
    # compiler control against tools/regex_cert.py, the beta' run-decomposition
    # identity decided over all 9,262 accumulator states, and the rank test
    # that says why the old feature family could not work. 20 s, and it is the
    # part that guards correctness. `--stages all` runs the 21-letter assembly.
    parser.add_argument("--stages", default="0,1,1b",
                        help="comma-separated, or 'all' for "
                             "0,1,1b,2,2b,3,4a,4b (about 29 minutes, 4 GB)")
    parser.add_argument("--budget", type=float, default=36000.0)
    parser.add_argument("--movers", default="")
    args = parser.parse_args()
    stages = ({"0", "1", "1b", "2", "2b", "3", "4a", "4b"}
              if args.stages == "all" else set(args.stages.split(",")))
    budget = Budget(args.budget)
    started = time.time()

    coefficients = {e: solve_run_coefficients(e) for e in (1, 2)}
    AB = {e: (coefficients[e][0], coefficients[e][1]) for e in (1, 2)}
    if "0" in stages:
        stage_compiler_control(budget)
    if "1" in stages:
        section1(coefficients)
    if "1b" in stages:
        section1b()

    state = None
    if {"2", "2b", "3", "4b"} & stages:
        movers = None
        if args.movers:
            movers = [EQ.BY_NAME[m] for m in args.movers.split(",")]
        elif "4b" in stages:
            movers = [y for y in SIGMA if EPS[y] != 0 and y[1] != 0]
        state = stage_features(budget, movers=movers)
        if state is None:
            note("FAIL", "the pair-cut feature did not verify; later stages "
                         "are not attempted")
    if state is not None and "2b" in stages:
        builder, blocks, memo, by_letter = state
        y = next(iter(by_letter))
        stage_negative_control(builder, blocks, y, by_letter[y], memo, budget)
    if state is not None and "3" in stages:
        builder, blocks, memo, by_letter = state
        y = next(iter(by_letter))
        stage_reversal(builder, blocks, y, by_letter[y], memo, budget)
    if "4a" in stages:
        stage_positive_control(budget)
    if state is not None and "4b" in stages:
        builder, blocks, memo, by_letter = state
        stage_full_assembly(builder, blocks, memo, budget, AB, by_letter)

    banner("verdict")
    if FAILURES:
        for failure in FAILURES:
            print(f"    [FAILURE] {failure}")
    else:
        print("    all checks that ran passed.")
    print(f"    runtime {time.time() - started:.1f}s, peak RSS "
          f"{peak_rss_mb():.0f} MB")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    raise SystemExit(main())
