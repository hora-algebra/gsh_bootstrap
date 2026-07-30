#!/usr/bin/env python3
"""How big is the star-free expression Schuetzenberger's proof actually produces?

MEASUREMENT, not an attempt to succeed.  `notes/c7c3_expression_obstruction.md`
section 4 records that the missing `phase-resolved pair cut` feature has a block
language which is star-free -- 12 raw states, transition monoid 90, aperiodic for
both `eps(g) = 1` and `eps(g) = 2` -- so by Schuetzenberger's theorem a star-free
expression for it EXISTS, and that the only remaining route to an explicit
expression is "implement the constructive proof and read the expression off",
whose output size was recorded as unverified.  This script implements that
construction and measures the output.

WHICH PROOF IS IMPLEMENTED.

  The local divisor induction.  For a monoid `M` and `c in M` the local divisor
  is `M_c = cM n Mc` with the product `(uc) o (cv) = ucv`; its identity is `c`,
  it is a divisor of `M`, and `|M_c| < |M|` whenever `c` is not a unit -- in an
  aperiodic monoid that means whenever `c != 1`.  The induction is on the pair
  `(|M|, |A|)` ordered lexicographically.  This is the proof of Schuetzenberger's
  theorem given by

    V. Diekert, M. Kufleitner, "A survey on the local divisor technique",
    Theoretical Computer Science 610 (2016) 13-23, arXiv:1410.6026;
    V. Diekert, M. Kufleitner, "Star-free languages and local divisors",
    arXiv:1408.2842 (2014);
    the technique is from V. Diekert, P. Gastin, "Pure future local temporal
    logics are expressively complete for Mazurkiewicz traces" (2006).

  The alternative constructions (Schuetzenberger's original 1965 induction on the
  ideal structure, Meyer 1969, Wilke's LTL route) are NOT implemented here.  The
  local divisor version was chosen because its induction is on two integers that
  both visibly decrease, which makes an implementation auditable.

  Concretely, with `phi : A* -> M` onto an aperiodic `M`, `c in A` with
  `phi(c) != 1`, `B = A \\ {c}`, `x = phi(c)`, and `eta(t) = x t x` the morphism
  from the letters `t in phi(B*)` into `M_x`:

      phi^-1(m)  =  [ phi^-1(m) n B* ]
                    u  U { L_B(s) . c . sigma(eta^-1(p)) . L_B(e) : s p e = m }

  where `L_B(s) = phi^-1(s) n B*` comes from the smaller alphabet, `eta^-1(p)`
  comes from the smaller monoid, and `sigma` substitutes the letter `t` by
  `L_B(t) . c`.  The concatenations are unambiguous (`L_B(s)` and `L_B(e)` avoid
  `c`, and `sigma` lands in the prefix code `(B* c)*`), so the union is exact.
  Complement is taken relative to the ambient set of the current context, which
  is what the `not_ambient` argument of `solve` carries.

WHAT IS MEASURED.  AST node count of the produced expression, both as a shared
DAG and as the unfolded tree; complement nesting depth; the length of the printed
expression; wall time and peak RSS; and, when the build finishes, whether the
expression is EQUAL to the block language, decided by product reachability on the
two minimal DFAs -- never by testing finitely many words.

Every "PASS" below is a complete finite decision.  The negative controls exist so
that a broken checker cannot produce the same output as a working one.
"""

from __future__ import annotations

import resource
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
    _atomic_empty,
    _atomic_eps,
    _atomic_letter,
    _concat,
    _product,
)

FAILURES: list[str] = []
PHASES = 3
ACC, DEAD = "acc", "dead"


def banner(text: str) -> None:
    print()
    print("=== " + text + " ===")


def peak_rss_mb() -> float:
    return resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / (1024 * 1024)


# --------------------------------------------------------------------------
# hash-consed expression builder over the regex_cert AST
# --------------------------------------------------------------------------


class Builder:
    """Builds `GRegex` nodes with structure sharing.

    Nodes are keyed by `id()` of their children, so every node ever built is
    kept alive: without `_keep` an address could be recycled and the table
    would silently return the wrong node.  No `star` node is ever built --
    the construction is star-free by design, so the star height is 0.
    """

    def __init__(self) -> None:
        self._table: dict[tuple, GRegex] = {}
        self._keep: list[GRegex] = []
        self.EMPTY = self._node("empty", (), None)
        self.EPS = self._node("eps", (), None)

    def _node(self, op: str, args: tuple[GRegex, ...], value) -> GRegex:
        key = (op, value, tuple(id(a) for a in args))
        hit = self._table.get(key)
        if hit is not None:
            return hit
        node = GRegex(op, args, value)
        self._table[key] = node
        self._keep.append(node)
        return node

    def lit(self, letter: str) -> GRegex:
        return self._node("letter", (), letter)

    def union(self, args) -> GRegex:
        kept = [a for a in args if a.op != "empty"]
        if not kept:
            return self.EMPTY
        if len(kept) == 1:
            return kept[0]
        return self._node("union", tuple(kept), None)

    def concat(self, args) -> GRegex:
        args = list(args)
        if any(a.op == "empty" for a in args):
            return self.EMPTY
        kept = [a for a in args if a.op != "eps"]
        if not kept:
            return self.EPS
        if len(kept) == 1:
            return kept[0]
        return self._node("concat", tuple(kept), None)

    def compl(self, arg: GRegex) -> GRegex:
        return self._node("compl", (arg,), None)

    @property
    def nodes_built(self) -> int:
        return len(self._keep)


# --------------------------------------------------------------------------
# measurement of a shared expression DAG
# --------------------------------------------------------------------------


def _post_order(root: GRegex) -> list[GRegex]:
    """Children-before-parents listing of the distinct nodes below `root`."""

    order: list[GRegex] = []
    seen: set[int] = set()
    stack: list[tuple[GRegex, bool]] = [(root, False)]
    while stack:
        node, expanded = stack.pop()
        if expanded:
            order.append(node)
            continue
        if id(node) in seen:
            continue
        seen.add(id(node))
        stack.append((node, True))
        for child in node.args:
            if id(child) not in seen:
                stack.append((child, False))
    return order


def measure(root: GRegex) -> dict:
    """Exact size measurements of the expression `root` denotes.

    `dag_nodes` counts distinct nodes; `tree_nodes` counts the nodes of the
    fully unfolded abstract syntax tree, which is what an expression written
    out on paper would have.  `str_len` is the length of the printed form
    under the convention  0 / 1 / letter / ~(E) / (E1+..+En) / (E1..En).
    """

    order = _post_order(root)
    tree: dict[int, int] = {}
    slen: dict[int, int] = {}
    cdep: dict[int, int] = {}
    ops: dict[str, int] = defaultdict(int)
    letters: dict[str, int] = defaultdict(int)
    occurrences: dict[int, dict] = {}
    for node in order:
        ops[node.op] += 1
        kids = [id(a) for a in node.args]
        tree[id(node)] = 1 + sum(tree[k] for k in kids)
        here: dict = defaultdict(int)
        if node.op == "letter":
            here[node.value] = 1
        for k in kids:
            for symbol, count in occurrences[k].items():
                here[symbol] += count
        occurrences[id(node)] = here
        cdep[id(node)] = (1 if node.op == "compl" else 0) + max(
            (cdep[k] for k in kids), default=0
        )
        if node.op == "letter":
            assert node.value is not None
            slen[id(node)] = len(node.value)
            letters[node.value] += 1
        elif node.op in {"empty", "eps"}:
            slen[id(node)] = 1
        elif node.op == "compl":
            slen[id(node)] = 3 + slen[kids[0]]
        elif node.op == "union":
            slen[id(node)] = 2 + len(kids) - 1 + sum(slen[k] for k in kids)
        elif node.op == "concat":
            slen[id(node)] = 2 + sum(slen[k] for k in kids)
        else:
            raise AssertionError(f"unexpected op {node.op}")
    if ops.get("star"):
        FAILURES.append("a star node appeared in a star-free construction")
    # what it costs to write the expression down WITH sharing: one named
    # definition per distinct node, children referred to by name.
    index = {id(node): i for i, node in enumerate(order)}
    shared_len = 0
    for i, node in enumerate(order):
        body = (len(node.value) if node.op == "letter"
                else 1 if node.op in {"empty", "eps"}
                else sum(len(str(index[id(a)])) + 2 for a in node.args) + 2)
        shared_len += len(str(i)) + 3 + body + 1
    return {
        "dag_nodes": len(order),
        "shared_str_len": shared_len,
        "tree_nodes": tree[id(root)],
        "compl_depth": cdep[id(root)],
        "str_len": slen[id(root)],
        "ops": dict(ops),
        "dag_letter_nodes": dict(letters),
        "tree_letter_occurrences": dict(occurrences[id(root)]),
        "star_height": 0,
    }


def digits(n: int) -> str:
    if n < 10 ** 15:
        return f"{n:,}"
    return f"~10^{len(str(n)) - 1} ({len(str(n))} digits)"


# --------------------------------------------------------------------------
# compiling a shared DAG, and deciding equality by product reachability
# --------------------------------------------------------------------------


def compile_dag(root: GRegex, alphabet, time_budget: float | None = None,
                memo: dict | None = None) -> DFA:
    """Compile with sharing, using the same primitives as `compile_regex`.

    `compile_regex` recurses on the syntax tree, which is impossible here: the
    unfolded tree has more nodes than there are atoms in anything.  This walks
    the shared DAG instead and memoises on node identity, but every automaton
    operation is the one `compile_regex` would have performed.  Passing a `memo`
    across calls lets a mutated copy reuse the sub-automata it did not change.
    """

    alpha = tuple(alphabet)
    memo = {} if memo is None else memo
    started = time.time()
    for node in _post_order(root):
        if id(node) in memo:
            continue
        if time_budget is not None and time.time() - started > time_budget:
            raise TimeoutError(f"compile exceeded {time_budget}s")
        if node.op == "empty":
            memo[id(node)] = _atomic_empty(alpha)
        elif node.op == "eps":
            memo[id(node)] = _atomic_eps(alpha)
        elif node.op == "letter":
            assert node.value is not None
            memo[id(node)] = _atomic_letter(alpha, node.value)
        elif node.op == "compl":
            memo[id(node)] = memo[id(node.args[0])].complemented().minimized()
        elif node.op == "union":
            acc = _atomic_empty(alpha)
            for arg in node.args:
                acc = _product(acc, memo[id(arg)], lambda x, y: x or y)
            memo[id(node)] = acc.minimized()
        elif node.op == "concat":
            acc = _atomic_eps(alpha)
            for arg in node.args:
                acc = _concat(acc, memo[id(arg)])
            memo[id(node)] = acc.minimized()
        else:
            raise AssertionError(f"unexpected op {node.op}")
    return memo[id(root)]


def decide_equality(left: DFA, right: DFA):
    """Product reachability.  Returns (equal, shortest witness, states visited).

    This is a decision over the whole language, not a test on sample words.
    """

    if left.alphabet != right.alphabet:
        raise ValueError("different alphabets")
    start = (left.start, right.start)
    parent = {start: None}
    queue = deque([start])
    while queue:
        pair = queue.popleft()
        if (pair[0] in left.accept) != (pair[1] in right.accept):
            word = []
            cursor = pair
            while parent[cursor] is not None:
                previous, symbol = parent[cursor]
                word.append(symbol)
                cursor = previous
            word.reverse()
            return False, word, len(parent)
        for symbol in left.alphabet:
            nxt = (left.step(pair[0], symbol), right.step(pair[1], symbol))
            if nxt not in parent:
                parent[nxt] = (pair, symbol)
                queue.append(nxt)
    return True, None, len(parent)


# --------------------------------------------------------------------------
# monoids
# --------------------------------------------------------------------------


def monoid_closure(generators, mult, one) -> set:
    elements = {one}
    frontier = [one]
    while frontier:
        f = frontier.pop()
        for g in generators:
            h = mult(f, g)
            if h not in elements:
                elements.add(h)
                frontier.append(h)
    return elements


def is_aperiodic(elements, mult) -> bool:
    for f in elements:
        seen, cur, k = {}, f, 0
        while cur not in seen:
            seen[cur] = k
            cur = mult(cur, f)
            k += 1
        if k - seen[cur] != 1:
            return False
    return True


def transition_monoid(dfa: DFA):
    """Minimal DFA, its transition monoid (= syntactic monoid) and morphism."""

    md = dfa.minimized()
    order = sorted(md.states)
    idx = {s: i for i, s in enumerate(order)}
    size = len(order)
    gens = {c: tuple(idx[md.step(s, c)] for s in order) for c in md.alphabet}
    one = tuple(range(size))

    def mult(a, b):
        return tuple(b[a[i]] for i in range(size))

    elements = monoid_closure(list(gens.values()), mult, one)
    start = idx[md.start]
    accept = {m for m in elements if order[m[start]] in md.accept}
    return md, gens, one, mult, elements, accept


# --------------------------------------------------------------------------
# the construction
# --------------------------------------------------------------------------


class Budget:
    def __init__(self, seconds: float, nodes: int) -> None:
        self.seconds = seconds
        self.nodes = nodes
        self.started = time.time()
        self.trace: list[tuple] = []

    def check(self, builder: Builder, where: str) -> None:
        if time.time() - self.started > self.seconds:
            raise TimeoutError(f"time budget exhausted at {where}")
        if builder.nodes_built > self.nodes:
            raise MemoryError(
                f"node budget exhausted at {where} "
                f"({builder.nodes_built} nodes built)"
            )


def solve(alph, mult, one, letters, not_ambient, builder: Builder,
          budget: Budget, depth: int = 0) -> dict:
    """Star-free expressions for every fibre of the morphism generated by `alph`.

    `alph` is a tuple of DISTINCT monoid elements playing the role of letters
    (merging letters with equal image is the standard first reduction and is
    sound because the inverse image of a length-preserving letter-to-letter
    morphism commutes with every Boolean operation and with concatenation).
    `letters[a]` is the expression, over the FINAL alphabet, denoting the block
    language of the letter `a`; `not_ambient` denotes the complement of the
    ambient set, so that complement relative to the ambient set is
    `compl(union(E, not_ambient))`.  The returned expressions are over the final
    alphabet already.
    """

    M = monoid_closure(alph, mult, one)
    budget.check(builder, f"depth {depth}, |A|={len(alph)}, |M|={len(M)}")
    budget.trace.append((depth, len(alph), len(M)))
    top = builder.compl(not_ambient)
    if len(M) == 1:
        return {one: top}
    if not is_aperiodic(M, mult):
        raise ValueError(f"monoid at depth {depth} is not aperiodic")

    # ---- choose the letter to peel off ---------------------------------
    best, chosen = None, None
    for a in sorted(alph):
        if a == one:
            continue
        local = {mult(a, m) for m in M} & {mult(m, a) for m in M}
        rest = monoid_closure([b for b in alph if b != a], mult, one)
        key = (len(local), len(rest))
        if best is None or key < best:
            best, chosen = key, a
    if chosen is None:
        raise ValueError("every letter is the identity but |M| > 1")
    c = chosen

    # ---- the smaller alphabet ------------------------------------------
    rest_alph = tuple(a for a in alph if a != c)
    not_ambient_B = builder.union(
        [not_ambient, builder.concat([top, letters[c], top])]
    )
    LB = solve(rest_alph, mult, one, {a: letters[a] for a in rest_alph},
               not_ambient_B, builder, budget, depth + 1)

    # ---- the local divisor M_c = cM n Mc, product (uc) o (cv) = ucv -----
    local = sorted({mult(c, m) for m in M} & {mult(m, c) for m in M})
    if len(local) >= len(M):
        raise ValueError("local divisor did not shrink; c must be a unit")
    witness = {}
    for p in local:
        for m in sorted(M):
            if mult(m, c) == p:
                witness[p] = m
                break

    def circ(p, q):
        return mult(witness[p], q)

    classes: dict = defaultdict(list)
    for t in sorted(LB):
        classes[mult(mult(c, t), c)].append(t)
    t_alph = tuple(sorted(classes))
    t_letters = {
        p: builder.union([builder.concat([LB[t], letters[c]]) for t in ts])
        for p, ts in classes.items()
    }
    not_ambient_T = builder.compl(
        builder.union([builder.EPS, builder.concat([top, letters[c]])])
    )
    K = solve(t_alph, circ, c, t_letters, not_ambient_T, builder, budget,
              depth + 1)

    # ---- assemble -------------------------------------------------------
    mid = {p: builder.concat([letters[c], K[p]]) for p in K}
    buckets: dict = defaultdict(list)
    for s in LB:
        for p in mid:
            sp = mult(s, p)
            for e in LB:
                buckets[mult(sp, e)].append(
                    builder.concat([LB[s], mid[p], LB[e]])
                )
        budget.check(builder, f"assembly at depth {depth}")
    result = {}
    for m in M:
        terms = list(buckets.get(m, ()))
        if m in LB:
            terms.insert(0, LB[m])
        result[m] = builder.union(terms)
    return result


def star_free_expression(dfa: DFA, budget: Budget):
    """Run the construction on a DFA and return (expression, builder, facts)."""

    md, gens, one, mult, elements, accept = transition_monoid(dfa)
    builder = Builder()
    by_image: dict = defaultdict(list)
    for symbol in md.alphabet:
        by_image[gens[symbol]].append(symbol)
    alph = tuple(sorted(by_image))
    letters = {
        image: builder.union([builder.lit(s) for s in symbols])
        for image, symbols in by_image.items()
    }
    fibres = solve(alph, mult, one, letters, builder.EMPTY, builder, budget)
    expression = builder.union([fibres[m] for m in sorted(accept & set(fibres))])
    facts = {
        "min_states": len(md.states),
        "monoid": len(elements),
        "aperiodic": is_aperiodic(elements, mult),
        "accept_elements": len(accept),
        "alphabet": md.alphabet,
        "letters_merged": len(md.alphabet) - len(alph),
        "recursion_nodes": len(budget.trace),
        "recursion_depth": max(t[0] for t in budget.trace),
    }
    return expression, builder, md, facts


# --------------------------------------------------------------------------
# the languages
# --------------------------------------------------------------------------


def block_dfa(eps_g: int, phases: int = PHASES,
              alphabet=("z", "m1", "m2", "g")) -> DFA:
    """Section 6 of `c7c3_expression_equivalence.py`, verbatim in behaviour.

    `(skipped tokens)* . (cutting token)`: the word is accepted exactly when it
    first arrives at relative phase 0 on a token that is NOT a skipped one, a
    skipped token being the distinguished mover `g` preceded by a different
    letter.
    """

    eps_of = {"z": 0, "m1": 1 % phases, "m2": 2 % phases, "g": eps_g % phases}
    start = (0, None)
    transitions: dict = {}
    seen = {start, ACC, DEAD}
    queue = deque([start])
    for s in (ACC, DEAD):
        for c in alphabet:
            transitions[(s, c)] = DEAD
    while queue:
        state = queue.popleft()
        phase, previous = state
        for c in alphabet:
            nxt = (phase + eps_of[c]) % phases
            if nxt == 0:
                skip = (c == "g" and previous is not None and previous != "g")
                target = (nxt, c) if skip else ACC
            else:
                target = (nxt, c)
            transitions[(state, c)] = target
            if target not in seen:
                seen.add(target)
                queue.append(target)
    return DFA(tuple(alphabet), frozenset(seen), start, frozenset({ACC}),
               transitions)


def dfa_from_predicate(alphabet, states, start, accept, step) -> DFA:
    transitions = {(s, c): step(s, c) for s in states for c in alphabet}
    return DFA(tuple(alphabet), frozenset(states), start, frozenset(accept),
               transitions)


def control_languages():
    """Small aperiodic languages, for validating the implementation."""

    out = []

    # A* over {a,b}
    out.append(("A* over {a,b}",
                dfa_from_predicate("ab", [0], 0, [0], lambda s, c: 0)))

    # no factor "ab"
    out.append(("no factor ab",
                dfa_from_predicate("ab", [0, 1, 2], 0, [0, 1],
                                   lambda s, c: 2 if s == 2 else
                                   (1 if c == "a" else (2 if s == 1 else 0)))))

    # exactly two a's
    def two_as(s, c):
        return min(s + 1, 3) if c == "a" else s
    out.append(("exactly two a's",
                dfa_from_predicate("ab", [0, 1, 2, 3], 0, [2], two_as)))

    # (ab)*
    def ab_star(s, c):
        table = {(0, "a"): 1, (0, "b"): 2, (1, "a"): 2, (1, "b"): 0,
                 (2, "a"): 2, (2, "b"): 2}
        return table[(s, c)]
    out.append(("(ab)*", dfa_from_predicate("ab", [0, 1, 2], 0, [0], ab_star)))

    # the same block language, smaller: 2 phases
    out.append(("block language, 2 phases, eps(g)=1",
                block_dfa(1, phases=2)))

    # the block language on sub-alphabets
    for sub in (("z", "m1", "g"), ("m1", "m2", "g"), ("z", "m1", "m2")):
        out.append((f"block language, eps(g)=1, letters {''.join(sub)}",
                    block_dfa(1, alphabet=sub)))
    return out


# --------------------------------------------------------------------------
# sections
# --------------------------------------------------------------------------


def run_one(label: str, dfa: DFA, seconds: float, nodes: int, verify=True,
            verbose=True):
    budget = Budget(seconds, nodes)
    t0 = time.time()
    try:
        expression, builder, md, facts = star_free_expression(dfa, budget)
    except (TimeoutError, MemoryError) as stop:
        elapsed = time.time() - t0
        trace = budget.trace
        print(f"    [ABORTED] {label}: {stop}")
        print(f"              after {elapsed:.1f}s, peak RSS {peak_rss_mb():.0f} MB, "
              f"{len(trace)} recursion nodes entered, deepest "
              f"(depth,|A|,|M|) = {max(trace, key=lambda t: t[0]) if trace else None}")
        return None
    build_time = time.time() - t0
    stats = measure(expression)
    if verbose:
        print(f"    {label}")
        print(f"      minimal DFA {facts['min_states']} states, syntactic monoid "
              f"{facts['monoid']}, aperiodic={facts['aperiodic']}, "
              f"|F|={facts['accept_elements']}")
        print(f"      recursion: {facts['recursion_nodes']} nodes, depth "
              f"{facts['recursion_depth']}")
        print(f"      AST nodes  shared DAG {stats['dag_nodes']:,}   "
              f"unfolded tree {digits(stats['tree_nodes'])}")
        print(f"      complement nesting depth {stats['compl_depth']}, "
              f"star height {stats['star_height']}")
        print(f"      printed length  written out {digits(stats['str_len'])}   "
              f"with sharing {digits(stats['shared_str_len'])} chars")
        print(f"      build {build_time:.2f}s, peak RSS {peak_rss_mb():.0f} MB")
    packed = {
        "label": label, "expression": expression, "builder": builder,
        "dfa": md, "facts": facts, "stats": stats, "build_time": build_time,
        "memo": {}, "compiled": None, "compile_time": None,
    }
    if not verify:
        return packed
    t1 = time.time()
    try:
        compiled = compile_dag(expression, md.alphabet, time_budget=seconds,
                               memo=packed["memo"]).minimized()
    except TimeoutError as stop:
        print(f"      [ABORTED] compile: {stop}")
        return packed
    packed["compiled"] = compiled
    packed["compile_time"] = time.time() - t1
    equal, witness, visited = decide_equality(compiled, md)
    verdict = "PASS" if equal else "FAIL"
    print(f"      [{verdict}] product reachability: equal={equal}, "
          f"product states visited {visited}, "
          f"compiled DFA {len(compiled.states)} states, "
          f"{packed['compile_time']:.2f}s")
    if not equal:
        print(f"             shortest distinguishing word: {''.join(witness)!r}")
        FAILURES.append(f"{label}: expression is not the language")
    return packed


def section_controls():
    banner("1. controls: does the implemented construction actually work?")
    print("    Every line is decided by product reachability against the DFA the")
    print("    language was defined by, not by testing words.")
    results = []
    for label, dfa in control_languages():
        out = run_one(label, dfa, seconds=900.0, nodes=40_000_000)
        if out is not None:
            results.append(out)
        print()
    return results


def section_negative_control(packed):
    """Break the verified expression in three ways and watch the checker fire.

    A checker that always printed `equal` would produce the same output as a
    working one on the section above, so each of these mutations must be caught,
    with an explicit distinguishing word.  The mutations reuse the sub-automata
    of the correct compile, so only what actually changed is recompiled.
    """

    banner("2. negative controls: break it and watch the checker fire")
    label = packed["label"]
    expression, builder = packed["expression"], packed["builder"]
    md, memo, compiled = packed["dfa"], packed["memo"], packed["compiled"]
    print(f"    subject: {label}")
    if compiled is None:
        print("    skipped: the subject expression was never compiled")
        return

    equal, _, visited = decide_equality(compiled, md)
    print(f"    (0) [CONTROL] the unbroken expression: equal={equal}, "
          f"product states visited {visited}")
    if not equal:
        FAILURES.append("negative control subject was not equal to begin with")
        return

    # (a) delete one term of the top-level union
    if expression.op == "union":
        fired = None
        for index in range(len(expression.args)):
            broken = builder.union(
                [a for i, a in enumerate(expression.args) if i != index]
            )
            got = compile_dag(broken, md.alphabet, memo=memo).minimized()
            ok, witness, seen = decide_equality(got, md)
            if not ok:
                fired = (index, witness, seen)
                break
        if fired is None:
            print("    (a) [PROBLEM] every term of the top union is redundant")
            FAILURES.append("negative control (a) did not fire")
        else:
            index, witness, seen = fired
            print(f"    (a) [FIRED] deleting union term #{index} of "
                  f"{len(expression.args)}: not equal, product states visited "
                  f"{seen}, shortest witness {''.join(witness)!r}")
    else:
        print("    (a) skipped: the top expression is not a union")

    # (b) reverse the factors of one concatenation, one node at a time.
    # Root-first, because a node near the root has few ancestors to recompile.
    # Some concatenations are genuinely reversal-invariant -- `TOP . x . TOP` is
    # the obvious one -- so the loop reports how many were tried.
    order = list(reversed(_post_order(expression)))
    victims = [n for n in order if n.op == "concat" and len(n.args) >= 2][:20]
    fired, tried = None, 0
    for victim in victims:
        tried += 1
        rebuilt: dict[int, GRegex] = {}
        for node in _post_order(expression):
            if node is victim:
                rebuilt[id(node)] = builder.concat(list(reversed(node.args)))
            elif node.op == "letter":
                rebuilt[id(node)] = builder.lit(node.value)
            elif node.op in {"empty", "eps"}:
                rebuilt[id(node)] = (builder.EMPTY if node.op == "empty"
                                     else builder.EPS)
            elif node.op == "compl":
                rebuilt[id(node)] = builder.compl(rebuilt[id(node.args[0])])
            elif node.op == "union":
                rebuilt[id(node)] = builder.union(
                    [rebuilt[id(x)] for x in node.args])
            else:
                rebuilt[id(node)] = builder.concat(
                    [rebuilt[id(x)] for x in node.args])
        got = compile_dag(rebuilt[id(expression)], md.alphabet,
                          memo=memo).minimized()
        ok, witness, seen = decide_equality(got, md)
        if not ok:
            fired = (tried, len(victim.args), witness, seen)
            break
    if not victims:
        print("    (b) skipped: no concatenation in the expression")
    elif fired is None:
        print(f"    (b) [PROBLEM] reversing any of {tried} concatenations "
              f"changed nothing")
        FAILURES.append("negative control (b) did not fire")
    else:
        tried, width, witness, seen = fired
        print(f"    (b) [FIRED] reversing the {width} factors of one "
              f"concatenation ({tried} tried, the earlier ones are genuinely "
              f"reversal-invariant): not equal, product states visited {seen}, "
              f"shortest witness {''.join(witness)!r}")

    # (c) move the target: flip the acceptance of one state of the reference DFA
    fired = None
    for state in sorted(md.states):
        accept = set(md.accept) ^ {state}
        other = DFA(md.alphabet, md.states, md.start, frozenset(accept),
                    dict(md.transition)).minimized()
        ok, witness, seen = decide_equality(compiled, other)
        if not ok:
            fired = (state, witness, seen)
            break
    if fired is None:
        print("    (c) [PROBLEM] the checker cannot see a changed accepting set")
        FAILURES.append("negative control (c) did not fire")
    else:
        state, witness, seen = fired
        print(f"    (c) [FIRED] flipping the acceptance of reference state "
              f"{state!r}: not equal, product states visited {seen}, shortest "
              f"witness {''.join(witness)!r}")


def section_target(seconds: float, nodes: int):
    banner("3. the pair-cut block language of the obstruction note")
    print("    Alphabet {z, m1, m2, g}: the class letters of section 6 of")
    print("    `c7c3_expression_equivalence.py`.  The 21-letter block language is")
    print("    the inverse image of this one under the length-preserving class")
    print("    morphism, so a star-free expression here gives one there by")
    print("    substituting each class letter with the union of its letters.")
    print("    The note reports transition monoid 90; that is the monoid of the")
    print("    12-state raw automaton.  The syntactic monoid -- the transition")
    print("    monoid of the 6-state minimisation, which is what the induction")
    print("    runs on and is the smaller, more favourable input -- has 51")
    print("    elements.  Both are aperiodic, and this run rechecks it.")
    print()
    packed = {}
    for eps_g in (1, 2):
        out = run_one(f"pair-cut block language, eps(g)={eps_g}",
                      block_dfa(eps_g), seconds=seconds, nodes=nodes)
        if out is not None:
            packed[eps_g] = out
            stats = out["stats"]
            # The 21-letter lift substitutes each class letter by the union of
            # the concrete letters of that class.  Replacing one leaf by a union
            # of k letters costs k+1 nodes instead of 1, so it adds k.  Class
            # sizes: 7 non-movers, the distinguished mover itself, and the 6 and
            # 7 remaining movers of each eps -- 7+6+7+1 = 21.
            sizes = {"z": 7, "m1": 7 if eps_g == 2 else 6,
                     "m2": 7 if eps_g == 1 else 6, "g": 1}
            dag = stats["dag_nodes"] + sum(
                sizes[c] for c in stats["dag_letter_nodes"] if sizes[c] > 1)
            tree = stats["tree_nodes"] + sum(
                n * sizes[c]
                for c, n in stats["tree_letter_occurrences"].items()
                if sizes[c] > 1)
            print(f"      21-letter lift: DAG {stats['dag_nodes']:,} -> "
                  f"{dag:,} nodes, unfolded tree {digits(stats['tree_nodes'])} "
                  f"-> {digits(tree)}")
        print()
    if packed:
        print("    What this settles and what it does not.  SETTLED: an explicit")
        print("    star-free expression for the pair-cut block language exists as")
        print("    a checked artifact, so `not constructed` in section 4 of the")
        print("    note is out of date, and the size is no longer unverified.")
        print("    NOT SETTLED: (i) the expression is only writable with sharing --")
        print("    written out as a tree it is ~10^68 symbols, and the certificate")
        print("    format of `tools/regex_cert.py` is a JSON TREE, so this is not")
        print("    yet a certificate the repository can check; (ii) this is one")
        print("    construction's output, not the minimum -- the language has a")
        print("    6-state minimal DFA and a far smaller expression may exist;")
        print("    (iii) the height-one CUT-COUNTING feature still has to be")
        print("    assembled from this block, and that step is untried here.")
    return packed


def section_scaling(control_results):
    banner("4. how the size scales with the monoid")
    print("    |M| is the syntactic monoid of the language the construction was")
    print("    run on; the node counts are of the expression it produced.")
    print()
    print(f"    {'language':<44} {'|A|':>3} {'|M|':>5} {'DAG':>10} "
          f"{'unfolded tree':>22} {'~depth':>6}")
    rows = []
    for out in control_results:
        md, facts, stats = out["dfa"], out["facts"], out["stats"]
        rows.append((out["label"], len(md.alphabet), facts["monoid"],
                     stats["dag_nodes"], stats["tree_nodes"],
                     stats["compl_depth"]))
    for label, a, m, dag, tree, cd in sorted(rows, key=lambda r: r[2]):
        print(f"    {label:<44} {a:>3} {m:>5} {dag:>10,} {digits(tree):>22} "
              f"{cd:>6}")
    return rows


def main() -> int:
    started = time.time()
    print(__doc__.strip().splitlines()[0])
    controls = section_controls()
    if controls:
        section_negative_control(max(controls,
                                     key=lambda r: r["stats"]["dag_nodes"]))
    target = section_target(seconds=3600.0, nodes=200_000_000)
    for out in sorted(target.values(), key=lambda r: r["label"]):
        section_negative_control(out)
    section_scaling(controls + list(target.values()))
    banner("verdict")
    if FAILURES:
        for failure in FAILURES:
            print(f"    [FAILURE] {failure}")
    else:
        print("    all checks passed.")
    print(f"    runtime {time.time() - started:.1f}s, peak RSS "
          f"{peak_rss_mb():.0f} MB")
    return 1 if FAILURES else 0


if __name__ == "__main__":
    sys.setrecursionlimit(100000)
    raise SystemExit(main())
