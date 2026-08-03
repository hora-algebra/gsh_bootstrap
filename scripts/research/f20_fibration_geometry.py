#!/usr/bin/env python3
"""The fibration view of F_20: base Z/4, fibre Z/5, and what the geometry buys.

F_20 = C_5 |x| C_4 is the total space of a split extension, so a word is a path,
its image is the holonomy of a flat affine Z/5-bundle over a wedge of |Sigma|
circles, and the coordinate formula beta(w) = sum_i beta_i 2^{E_i} is a 1-cocycle
(crossed homomorphism) for the pulled-back Z/4-action.  This script makes the
analogy exact, tests what cohomology can and cannot see, identifies the hard
irreducible representation, and extracts the single closure question the picture
reduces the problem to.  Output is deterministic; evidence level COMPUTED.
"""

from __future__ import annotations

import itertools
import random
import sys
from collections import deque
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import f20_full_alphabet as base  # noqa: E402
import small_group_pst_coverage as sg  # noqa: E402


MODULUS = base.MODULUS          # 5, the fibre
PHASES = base.PHASES            # 4, the base
POW2 = base.POWERS_OF_TWO       # (1, 2, 4, 3) = 2^p mod 5
IDENTITY = base.IDENTITY
FULL_SIGMA = tuple(base.SIGMA)
EPSILON = dict(base.EPSILON)

# The two-generator instance of F20-STD-01: a = (x -> x+1), b = (x -> 2x).
GEN_A = (1, 1)
GEN_B = (2, 0)
TWO_GEN = (GEN_A, GEN_B)

failures: list[str] = []


def fail(section: str, message: str) -> None:
    failures.append(f"[{section}] {message}")
    print(f"  FAIL [{section}] {message}")


def name(g) -> str:
    return base.letter_name(g)


def mu(word):
    """Ground truth: the direct group product, never the coordinate formula."""
    return base.evaluate(tuple(word))


def eps_of(word) -> int:
    return sum(EPSILON[g] for g in word) % PHASES


def words_upto(sigma, length):
    for n in range(length + 1):
        yield from itertools.product(sigma, repeat=n)


# ---------------------------------------------------------------------------
# exact linear algebra over F_5
# ---------------------------------------------------------------------------

def rank_f5(rows, ncols: int) -> int:
    """Exact rank over F_5 of the given list of rows."""
    matrix = [[v % MODULUS for v in row] for row in rows]
    rank = 0
    for col in range(ncols):
        pivot = None
        for i in range(rank, len(matrix)):
            if matrix[i][col]:
                pivot = i
                break
        if pivot is None:
            continue
        matrix[rank], matrix[pivot] = matrix[pivot], matrix[rank]
        inverse = pow(matrix[rank][col], MODULUS - 2, MODULUS)
        matrix[rank] = [(v * inverse) % MODULUS for v in matrix[rank]]
        for i in range(len(matrix)):
            if i != rank and matrix[i][col]:
                factor = matrix[i][col]
                matrix[i] = [(matrix[i][j] - factor * matrix[rank][j]) % MODULUS
                             for j in range(ncols)]
        rank += 1
    return rank


# ---------------------------------------------------------------------------
# generic DFA utilities (aperiodicity = star-freeness by Schuetzenberger 1965)
# ---------------------------------------------------------------------------

def build_dfa(sigma, start, step, accept):
    """Reachable DFA from a start state, a transition function and a predicate."""
    states = [start]
    index = {start: 0}
    transitions: list[list[int]] = []
    queue = deque([start])
    while queue:
        state = queue.popleft()
        row = []
        for letter in sigma:
            target = step(state, letter)
            if target not in index:
                index[target] = len(states)
                states.append(target)
                queue.append(target)
            row.append(index[target])
        transitions.append(row)
    accepting = frozenset(i for i, s in enumerate(states) if accept(s))
    return states, transitions, accepting


def minimize(transitions, accepting):
    """Hopcroft-free partition refinement; the automaton is already reachable."""
    n = len(transitions)
    width = len(transitions[0]) if n else 0
    block = [1 if i in accepting else 0 for i in range(n)]
    while True:
        signature = {}
        fresh = []
        for i in range(n):
            key = (block[i], tuple(block[transitions[i][a]] for a in range(width)))
            if key not in signature:
                signature[key] = len(signature)
            fresh.append(signature[key])
        if fresh == block:
            break
        block = fresh
    size = max(block) + 1
    new_transitions = [[0] * width for _ in range(size)]
    for i in range(n):
        for a in range(width):
            new_transitions[block[i]][a] = block[transitions[i][a]]
    new_accepting = frozenset(block[i] for i in accepting)
    return new_transitions, new_accepting, block


def transition_monoid_period(transitions, limit=400000):
    """Largest period of an element of the transition monoid, or None if too big.

    A monoid is aperiodic iff every element x satisfies x^n = x^{n+1} for some n.
    Minimizing the DFA first is required: a period in a non-minimal automaton can
    die in the quotient.
    """
    n = len(transitions)
    width = len(transitions[0]) if n else 0
    identity = tuple(range(n))
    generators = [tuple(transitions[s][a] for s in range(n)) for a in range(width)]
    seen = {identity}
    queue = deque([identity])
    while queue:
        element = queue.popleft()
        for generator in generators:
            product = tuple(generator[s] for s in element)
            if product not in seen:
                if len(seen) >= limit:
                    return None
                seen.add(product)
                queue.append(product)
    worst = 1
    for element in seen:
        power = element
        history = {element: 1}
        step = 1
        while True:
            power = tuple(power[s] for s in element)
            step += 1
            if power in history:
                worst = max(worst, step - history[power])
                break
            history[power] = step
    return worst


def single_letter_period(transitions, letter_index):
    """Period of one generator: O(states), enough to refute aperiodicity."""
    n = len(transitions)
    element = tuple(transitions[s][letter_index] for s in range(n))
    power = element
    history = {element: 1}
    step = 1
    while True:
        power = tuple(power[s] for s in element)
        step += 1
        if power in history:
            return step - history[power]
        history[power] = step


# ---------------------------------------------------------------------------
# [1] beta is a 1-cocycle, and over a free monoid there is no obstruction
# ---------------------------------------------------------------------------

def section_1() -> None:
    print("[1] the coordinate formula is a 1-cocycle (crossed homomorphism)")

    checked = 0
    for u in words_upto(FULL_SIGMA, 2):
        beta_u = mu(u)[1]
        for v in words_upto(FULL_SIGMA, 2):
            alpha_v, beta_v = mu(v)
            expected = (alpha_v * beta_u + beta_v) % MODULUS
            actual = mu(u + v)[1]
            if actual != expected:
                fail("1", f"cocycle identity fails at u={u} v={v}")
                return
            checked += 1
    print(f"  beta(uv) = alpha(v).beta(u) + beta(v) on all {checked} pairs of words "
          f"of length <= 2 over the full 20-letter alphabet")

    rng = random.Random(20250725)
    long_checks = 0
    for _ in range(4000):
        u = tuple(rng.choice(FULL_SIGMA) for _ in range(rng.randrange(0, 12)))
        v = tuple(rng.choice(FULL_SIGMA) for _ in range(rng.randrange(0, 12)))
        if mu(u + v)[1] != (mu(v)[0] * mu(u)[1] + mu(v)[1]) % MODULUS:
            fail("1", f"cocycle identity fails on the long pair {u} {v}")
            return
        long_checks += 1
    print(f"  and on {long_checks} random pairs of words of length <= 11 each")

    # Freeness: over a free monoid a derivation is determined by, and exists for,
    # *any* assignment of values to the generators.  Z^1(Sigma*, M) = M^Sigma.
    trials = 0
    for _ in range(200):
        values = {g: rng.randrange(MODULUS) for g in FULL_SIGMA}

        def cocycle(word):
            total = 0
            phase = 0
            for letter in reversed(word):
                total = (total + values[letter] * POW2[phase]) % MODULUS
                phase = (phase + EPSILON[letter]) % PHASES
            return total

        for _ in range(20):
            u = tuple(rng.choice(FULL_SIGMA) for _ in range(rng.randrange(0, 6)))
            v = tuple(rng.choice(FULL_SIGMA) for _ in range(rng.randrange(0, 6)))
            if cocycle(u + v) != (POW2[eps_of(v)] * cocycle(u) + cocycle(v)) % MODULUS:
                fail("1", "an arbitrary generator assignment failed to extend")
                return
            trials += 1
    print(f"  every one of 200 random assignments of fibre values to the 20 letters "
          f"extends to a cocycle ({trials} identity checks): Z^1(Sigma*, Z/5) = (Z/5)^Sigma,")
    print("  so the free monoid carries no cocycle obstruction at all -- the difficulty "
          "is not the existence of beta but its definability")


# ---------------------------------------------------------------------------
# [2] the cohomology of the extension vanishes identically
# ---------------------------------------------------------------------------

def cyclic_group_cohomology(order: int, action: int, top: int):
    """H^n(C_order, F_5) for the module where the generator acts by `action`.

    Computed from the bar resolution, not from the periodic-resolution formula:
    C^n = Maps(G^n, F_5), (d f)(g_1..g_{n+1}) = g_1.f(g_2..g_{n+1})
        + sum_i (-1)^i f(.., g_i g_{i+1}, ..) + (-1)^{n+1} f(g_1..g_n).
    """
    def act(j, value):
        return (pow(action, j, MODULUS) * value) % MODULUS

    def differential(n):
        """Matrix of d^n : C^n -> C^{n+1}, as rows indexed by C^{n+1} basis."""
        source = list(itertools.product(range(order), repeat=n))
        target = list(itertools.product(range(order), repeat=n + 1))
        position = {tup: i for i, tup in enumerate(source)}
        rows = []
        for tup in target:
            row = [0] * len(source)
            row[position[tup[1:]]] = (row[position[tup[1:]]] + act(tup[0], 1)) % MODULUS
            for i in range(1, n + 1):
                merged = tup[:i - 1] + ((tup[i - 1] + tup[i]) % order,) + tup[i + 1:]
                sign = -1 if i % 2 else 1
                row[position[merged]] = (row[position[merged]] + sign) % MODULUS
            sign = -1 if (n + 1) % 2 else 1
            row[position[tup[:n]]] = (row[position[tup[:n]]] + sign) % MODULUS
            rows.append(row)
        return rows, len(source)

    ranks = {}
    dims = {}
    for n in range(top + 1):
        rows, dim = differential(n)
        ranks[n] = rank_f5(rows, dim)
        dims[n] = dim
    cohomology = {}
    for n in range(top):
        kernel = dims[n] - ranks[n]
        image = ranks[n - 1] if n >= 1 else 0
        cohomology[n] = kernel - image
    return cohomology


def section_2() -> None:
    print("\n[2] the cohomology of the extension vanishes for the whole order-20 family")

    labels = {1: "trivial action  (C_20)",
              4: "inversion       (Dic_5)",
              2: "faithful        (F_20)"}
    table = {}
    for action in (1, 4, 2):
        cohomology = cyclic_group_cohomology(PHASES, action, 5)
        table[action] = cohomology
        shape = ", ".join(f"H^{n}={cohomology[n]}" for n in sorted(cohomology))
        print(f"  C_4 on Z/5 by x -> {action}x  [{labels[action]}]:  {shape}   "
              f"(dimensions over F_5)")
        for n in range(1, 5):
            if cohomology[n] != 0:
                fail("2", f"H^{n} should vanish for action {action}")

    if table[1][0] != 1 or table[4][0] != 0 or table[2][0] != 0:
        fail("2", "H^0 = M^G is wrong for some action")

    print("  H^n = 0 for every n >= 1 and every one of the three actions "
          "(orders 4 and 5 are coprime).")
    print("  H^2 = 0: all three extensions split.  H^1 = 0: the splitting is unique "
          "up to conjugacy.")
    print("  So the *classifying data of the extension* is literally identical -- and "
          "zero -- for C_20,")
    print("  Dic_5 and F_20.  No functor of that data can separate the settled cases "
          "from the open one.")


# ---------------------------------------------------------------------------
# [3] the order-20 family: one parameter, and the frontier sits inside it
# ---------------------------------------------------------------------------

def monodromy_order(action: int) -> int:
    order = 1
    power = action % MODULUS
    while power != 1:
        power = (power * action) % MODULUS
        order += 1
    return order


def section_3() -> None:
    print("\n[3] the order-20 family C_5 |x|_r C_4: the frontier is the monodromy order")

    groups = {r: sg.metacyclic(MODULUS, PHASES, r, name=f"C5:{r}C4") for r in (1, 4, 2)}
    for r, group in groups.items():
        if group.order != 20:
            fail("3", f"C5:{r}C4 has order {group.order}")
    for r, s in itertools.combinations((1, 4, 2), 2):
        if sg.isomorphic(groups[r], groups[s]):
            fail("3", f"C5:{r}C4 and C5:{s}C4 should not be isomorphic")

    if not sg.isomorphic(groups[1], sg.cyclic(20)):
        fail("3", "C5:1C4 should be C_20")
    if not sg.isomorphic(groups[4], sg.dicyclic(5)):
        fail("3", "C5:4C4 should be Dic_5")
    print("  the three members are pairwise non-isomorphic; r=1 is C_20 and r=4 is "
          "Dic_5 (machine-verified)")

    rows = []
    for r in (1, 4, 2):
        group = groups[r]
        witness = sg.pst_necessary_criterion(group)
        rows.append((r, monodromy_order(r), group.is_abelian(), witness is not None))
    print("   r | monodromy order | abelian | inside the PST 'abelian by elem. ab. 2' "
          "class")
    for r, order, is_abelian, inside in rows:
        print(f"   {r} |        {order}        |  {str(is_abelian):5s}  |  {inside}")

    expected = [(1, 1, True, True), (4, 2, False, True), (2, 4, False, False)]
    if rows != expected:
        fail("3", f"the family table changed: {rows}")

    print("  C_20 is covered by PST-GRP-01, Dic_5 by PST-GRP-03 (and by DICM-EMB-01), "
          "and F_20 by neither.")
    print("  The three differ in exactly one parameter -- the order of the monodromy "
          "1, 2, 4 -- while by [2]")
    print("  their extension cohomology is identical.  The frontier of the known "
          "results is the point where")
    print("  the local system stops being an involution.")


# ---------------------------------------------------------------------------
# [4] representation theory: one induced irrep carries the whole difficulty
# ---------------------------------------------------------------------------

# Z[zeta_5] in the basis 1, z, z^2, z^3 with z^4 = -(1 + z + z^2 + z^3).
def cyc(exponent: int):
    exponent %= MODULUS
    if exponent == 4:
        return (-1, -1, -1, -1)
    vector = [0, 0, 0, 0]
    vector[exponent] = 1
    return tuple(vector)


def cyc_add(x, y):
    return tuple(a + b for a, b in zip(x, y))


def cyc_scale(x, k):
    return tuple(a * k for a in x)


def cyc_mul(x, y):
    raw = [0] * 8
    for i, a in enumerate(x):
        if a:
            for j, b in enumerate(y):
                raw[i + j] += a * b
    total = (0, 0, 0, 0)
    for degree, coefficient in enumerate(raw):
        if coefficient:
            total = cyc_add(total, cyc_scale(cyc(degree), coefficient))
    return total


def cyc_conj(x):
    total = (0, 0, 0, 0)
    for degree, coefficient in enumerate(x):
        if coefficient:
            total = cyc_add(total, cyc_scale(cyc(-degree), coefficient))
    return total


def induced_character(action: int):
    """Character of Ind_{C_5}^{C_5|x|_r C_4} of the character a -> zeta_5^a.

    On the semidirect product the induced character is supported on C_5, where
    chi(a) = sum over the C_4-orbit of the character, i.e. sum_j zeta^{r^j a}.
    Computed here from the honest coset formula, not from that description.
    """
    elements = [(a, j) for a in range(MODULUS) for j in range(PHASES)]

    def multiply(p, q):
        return ((p[0] + pow(action, p[1], MODULUS) * q[0]) % MODULUS,
                (p[1] + q[1]) % PHASES)

    def inverse(p):
        for q in elements:
            if multiply(p, q) == (0, 0):
                return q
        raise AssertionError

    cosets = [(0, j) for j in range(PHASES)]        # transversal of C_5
    character = {}
    for g in elements:
        total = (0, 0, 0, 0)
        for t in cosets:
            conjugate = multiply(multiply(inverse(t), g), t)
            if conjugate[1] == 0:                    # lands in C_5
                total = cyc_add(total, cyc(conjugate[0]))
        character[g] = total
    return elements, multiply, character


def induced_matrices(action: int):
    """Ind_{C_5}^{C_5|x|_r C_4} of a -> zeta^a as explicit 4x4 monomial matrices.

    Basis indexed by the cosets C_5 t_j, t_j = (0, j).  With t_j g in C_5 t_k one
    has t_j g t_k^{-1} = (r^j b, 0) for g = (b, m) and k = j + m, so the entry is
    zeta^{r^j b}.  Transposing turns the resulting anti-homomorphism into one.
    """
    elements = [(b, m) for b in range(MODULUS) for m in range(PHASES)]

    def multiply(p, q):
        return ((p[0] + pow(action, p[1], MODULUS) * q[0]) % MODULUS,
                (p[1] + q[1]) % PHASES)

    def matrix(g):
        b, m = g
        rows = [[(0, 0, 0, 0)] * PHASES for _ in range(PHASES)]
        for j in range(PHASES):
            k = (j + m) % PHASES
            rows[j][k] = cyc(pow(action, j, MODULUS) * b)   # already transposed
        return tuple(tuple(row) for row in rows)

    return elements, multiply, matrix


def matrix_mul(x, y):
    size = len(x)
    return tuple(tuple(
        _cyc_sum(cyc_mul(x[i][t], y[t][j]) for t in range(size))
        for j in range(size)) for i in range(size))


def _cyc_sum(terms):
    total = (0, 0, 0, 0)
    for term in terms:
        total = cyc_add(total, term)
    return total


def section_4() -> None:
    print("\n[4] representation theory: the hard irrep is induced, and its dimension "
          "is the monodromy order")

    for action, expected_dimension in ((1, 1), (4, 2), (2, 4)):
        elements, _, character = induced_character(action)
        norm = (0, 0, 0, 0)
        for g in elements:
            norm = cyc_add(norm, cyc_mul(character[g], cyc_conj(character[g])))
        if any(c % len(elements) for c in norm):
            fail("4", f"<Ind chi, Ind chi> is not an integer for r={action}")
            continue
        multiplicity_sum = tuple(c // len(elements) for c in norm)
        if multiplicity_sum[1:] != (0, 0, 0):
            fail("4", f"<Ind chi, Ind chi> is not rational for r={action}")
            continue
        pieces = multiplicity_sum[0]
        # Clifford theory: with T the stabilizer of chi, Ind = sum of |T/C_5|
        # *distinct* irreps, each of dimension the orbit length [G:T].  Hence
        # <Ind, Ind> = |T/C_5| = 4 / orbit, and orbit = 4 / <Ind, Ind>.
        dimension = PHASES // pieces
        if dimension != expected_dimension or pieces * dimension != PHASES:
            fail("4", f"r={action}: induced-irrep dimension {dimension} != "
                      f"{expected_dimension}")
        print(f"  r={action}: <Ind chi, Ind chi> = {pieces}, so Ind chi is a sum of "
              f"{pieces} distinct irreps of dimension {dimension}; "
              f"{pieces} x {dimension} = 4 = the index,")
        print(f"        and {dimension} = the monodromy order")

    # The identity-fibre indicator of F_20 in terms of characters.
    _, _, chi = induced_character(2)
    ok = True
    for a in range(MODULUS):
        for j in range(PHASES):
            g = (a, j)
            base_part = 1 if j == 0 else 0
            total = cyc_add(cyc_scale(cyc(0), base_part), chi[g])
            indicator = 5 if g == (0, 0) else 0
            if total != cyc_scale(cyc(0), indicator):
                ok = False
    if ok:
        print("  orthogonality specialises to  5 . 1_{g=e}  =  1_{eps(g)=0} + chi_rho(g)  "
              "on all 20 elements:")
        print("  the four linear characters give the base language (count mod 4) and a "
              "single 4-dimensional")
        print("  induced character carries the entire remaining difficulty")
    else:
        fail("4", "the character identity for the identity fibre failed")

    # Explicit monomial model of the 4-dimensional irrep of F_20, checked to be a
    # homomorphism on all 400 products, with the right character and shape.
    elements, multiply, matrix = induced_matrices(2)
    homomorphism = all(matrix_mul(matrix(g), matrix(h)) == matrix(multiply(g, h))
                       for g in elements for h in elements)
    if not homomorphism:
        fail("4", "the explicit induced matrices are not a homomorphism")
    shape_ok = True
    permutations = {}
    for g in elements:
        rows = matrix(g)
        for i in range(PHASES):
            if sum(1 for j in range(PHASES) if rows[i][j] != (0, 0, 0, 0)) != 1:
                shape_ok = False
            if sum(1 for j in range(PHASES) if rows[j][i] != (0, 0, 0, 0)) != 1:
                shape_ok = False
        permutations[g] = tuple(next(j for j in range(PHASES)
                                     if rows[i][j] != (0, 0, 0, 0))
                                for i in range(PHASES))
    _, _, coset_character = induced_character(2)
    trace_ok = all(_cyc_sum(matrix(g)[i][i] for i in range(PHASES)) == coset_character[g]
                   for g in elements)
    if not (shape_ok and trace_ok):
        fail("4", "the induced matrices are not monomial with the expected character")
    else:
        print("  explicit 4x4 model of the hard irrep: a homomorphism on all "
              f"{len(elements) ** 2} products, trace equal to the")
        print("  coset character, and monomial -- exactly one nonzero entry per row and "
              "per column")
    if len({permutations[g] for g in elements}) != PHASES or \
            any(permutations[g] != permutations[(0, g[1])] for g in elements):
        fail("4", "the permutation part is not a function of the base coordinate alone")
    else:
        print("  rho(g) = P(eps(g)) . D(g): the permutation part depends only on the "
              "base coordinate eps(g) and")
        print("  takes exactly 4 values, the diagonal part only on the fibre -- the "
              "fibration, in matrix form")


# ---------------------------------------------------------------------------
# [5] the wreath embedding and the transducer decomposition
# ---------------------------------------------------------------------------

def wreath_mul(left, right):
    """(f, q).(f', q') = (shift_{q'} f + f', q + q') with (shift_t f)(i) = f(i+t)."""
    f, q = left
    g, r = right
    shifted = tuple((f[(i + r) % PHASES] + g[i]) % MODULUS for i in range(PHASES))
    return (shifted, (q + r) % PHASES)


def wreath_embed(element):
    alpha, beta = element
    e = EPSILON[element] if element in EPSILON else POW2.index(alpha)
    return (tuple((POW2[i] * beta) % MODULUS for i in range(PHASES)), e)


def transduce(word):
    """Right-to-left sequential marking: each letter tagged with its suffix phase."""
    marks = []
    phase = 0
    for letter in reversed(word):
        marks.append((phase, letter))
        phase = (phase + EPSILON[letter]) % PHASES
    return tuple(reversed(marks))


def in_fibre_language(marked) -> bool:
    """K over Gamma = Z/4 x Sigma: a pure counting-mod-5 (commutative) condition."""
    total = 0
    for phase, letter in marked:
        total = (total + letter[1] * POW2[phase]) % MODULUS
    return total == 0


def section_5() -> None:
    print("\n[5] the wreath embedding, and the decomposition it induces on languages")

    ok = True
    for x in FULL_SIGMA:
        for y in FULL_SIGMA:
            if wreath_mul(wreath_embed(x), wreath_embed(y)) != wreath_embed(mu((x, y))):
                ok = False
    images = {wreath_embed(g) for g in FULL_SIGMA}
    if not ok or len(images) != 20:
        fail("5", "the wreath embedding is not an injective homomorphism")
    else:
        print("  F_20 -> C_5 wr C_4 = (Z/5)^4 |x| C_4 (order 2500), "
              "g = (alpha, beta) |-> ((2^i beta)_i, eps(g)):")
        print("  verified a homomorphism on all 400 products and injective on all 20 "
              "elements")

    rng = random.Random(5202507)
    associative = 0
    for _ in range(20000):
        triple = [(tuple(rng.randrange(MODULUS) for _ in range(PHASES)),
                   rng.randrange(PHASES)) for _ in range(3)]
        x, y, z = triple
        if wreath_mul(wreath_mul(x, y), z) != wreath_mul(x, wreath_mul(y, z)):
            fail("5", "the wreath product is not associative")
            break
        associative += 1
    print(f"  the ambient wreath product is associative on {associative} random triples")

    # the transducer is genuinely sequential with the monodromy group as its states
    for _ in range(2000):
        word = tuple(rng.choice(FULL_SIGMA) for _ in range(rng.randrange(0, 10)))
        marks = []
        state = 0
        for letter in reversed(word):
            marks.append((state, letter))
            state = (state + EPSILON[letter]) % PHASES
        if tuple(reversed(marks)) != transduce(word):
            fail("5", "the transducer is not the claimed sequential machine")
            break
    print("  sigma : Sigma* -> (Z/4 x Sigma)* is right-sequential with state set Z/4 -- "
          "the monodromy group itself")

    for label, sigma, length in (("full 20-letter alphabet", FULL_SIGMA, 4),
                                 ("2-generator alphabet", TWO_GEN, 12)):
        checked = 0
        for word in words_upto(sigma, length):
            predicted = (eps_of(word) == 0) and in_fibre_language(transduce(word))
            if predicted != (mu(word) == IDENTITY):
                fail("5", f"decomposition fails on {word}")
                break
            checked += 1
        print(f"  {label}: mu^-1(e) = {{eps = 0 mod 4}} cap sigma^-1(K) on all {checked} "
              f"words of length <= {length}")

    # Negative control.  NOTE: a cyclic shift of the weights is *not* a
    # perturbation -- it multiplies the whole sum by a unit of F_5 and decides the
    # same predicate.  Genuine perturbations are ones that change the weight
    # vector projectively.
    controls = {
        "constant weights (phase ignored)": (1, 1, 1, 1),
        "two weights transposed": (POW2[1], POW2[0], POW2[2], POW2[3]),
        "one weight zeroed": (POW2[0], 0, POW2[2], POW2[3]),
    }
    for label, weights in controls.items():
        broken = 0
        for word in words_upto(TWO_GEN, 10):
            total = sum(letter[1] * weights[p]
                        for p, letter in transduce(word)) % MODULUS
            predicted = (eps_of(word) == 0) and total == 0
            if predicted != (mu(word) == IDENTITY):
                broken += 1
        if broken == 0:
            fail("5", f"the control '{label}' also decided the fibre: check is vacuous")
        else:
            print(f"  negative control, {label}: wrong on {broken} words of length "
                  f"<= 10 -- the identity")
            print("    above is a property of the phase weights 2^p, not of its shape")
    shifted = 0
    for word in words_upto(TWO_GEN, 10):
        total = sum(letter[1] * POW2[(p + 1) % PHASES]
                    for p, letter in transduce(word)) % MODULUS
        if ((eps_of(word) == 0) and total == 0) != (mu(word) == IDENTITY):
            shifted += 1
    if shifted != 0:
        fail("5", "a cyclic weight shift should be an equivalent condition")
    print("  (a cyclic shift of the weights is deliberately NOT used as a control: it "
          "scales the sum by a unit)")

    print("  K is recognized by C_5 acting on Gamma = Z/4 x Sigma by the weight "
          "morphism, hence commutative,")
    print("  hence gsh <= 1 by PST-GRP-01; {eps = 0} is recognized by C_4, likewise "
          "gsh <= 1.  So:")
    print("  HeightOneForGroup F_20 follows if sigma^-1 preserves gsh <= 1 for this "
          "single transducer.")


# ---------------------------------------------------------------------------
# [6] calibration: the mechanism must work where height one is already proved
# ---------------------------------------------------------------------------

def section_6() -> None:
    print("\n[6] calibration on the 2-generator instance, where gsh = 1 is proved "
          "(F20-STD-01)")

    # F20-STD-01: number of b's = 0 mod 4, and N_0 + 3N_1 + 4N_2 + 2N_3 = 0 mod 5,
    # where N_p counts the a's occurring at phase p.  Which phase convention?
    coefficients = (1, 3, 4, 2)
    for convention in ("prefix", "suffix"):
        agree = 0
        mismatch = 0
        for word in words_upto(TWO_GEN, 12):
            counts = [0, 0, 0, 0]
            if convention == "prefix":
                phase = 0
                for letter in word:
                    if letter == GEN_A:
                        counts[phase] += 1
                    phase = (phase + EPSILON[letter]) % PHASES
            else:
                phase = 0
                for letter in reversed(word):
                    if letter == GEN_A:
                        counts[phase] += 1
                    phase = (phase + EPSILON[letter]) % PHASES
            arithmetic = (eps_of(word) == 0 and
                          sum(c * n for c, n in zip(coefficients, counts)) % MODULUS == 0)
            if arithmetic == (mu(word) == IDENTITY):
                agree += 1
            else:
                mismatch += 1
        status = ("matches the group on all "
                  f"{agree} words" if mismatch == 0
                  else f"is wrong on {mismatch} of {agree + mismatch} words")
        print(f"  published coefficients (1,3,4,2) = 2^-p read with the {convention} "
              f"phase: {status} of length <= 12")

    # The two trivialisations differ by the holonomy of the whole loop:
    #   P_i + eps_i + E_i = eps(w),  so  beta_suffix = 2^{eps(w)} . sum beta_i 2^{-eps_i-P_i}.
    # On the identity fibre eps(w) = 0 and the twist disappears, which is why the
    # published prefix form and the suffix form of the transducer agree there.
    twist_checked = 0
    for word in words_upto(FULL_SIGMA, 3):
        prefix_phase = 0
        total = 0
        for letter in word:
            exponent = (-EPSILON[letter] - prefix_phase) % PHASES
            total = (total + letter[1] * POW2[exponent]) % MODULUS
            prefix_phase = (prefix_phase + EPSILON[letter]) % PHASES
        if (POW2[eps_of(word)] * total) % MODULUS != mu(word)[1]:
            fail("6", f"the prefix/suffix twist relation fails on {word}")
            break
        twist_checked += 1
    print(f"  the prefix and suffix trivialisations differ exactly by the holonomy "
          f"2^eps(w) of the whole loop")
    print(f"  ({twist_checked} words of length <= 3 over the full alphabet), so on the "
          f"identity fibre they agree")

    # the transducer form specialised to two letters is exactly the counting form
    matched = 0
    for word in words_upto(TWO_GEN, 14):
        counts = [0, 0, 0, 0]
        for phase, letter in transduce(word):
            if letter[1]:
                counts[phase] += 1
        transducer_value = sum(POW2[p] * counts[p] for p in range(PHASES)) % MODULUS
        if transducer_value != mu(word)[1]:
            fail("6", f"the transducer form disagrees with the group on {word}")
            break
        matched += 1
    print(f"  sigma^-1(K) specialised to {{a, b}} IS the published arithmetic condition: "
          f"agrees with the group on")
    print(f"  all {matched} words of length <= 14, the same instance verified in "
          f"F20-STD-01")
    print("  CALIBRATION PASSED: this mechanism reproduces a case where height one is "
          "already established.")
    print("  Routes (ii) and (iii) both failed exactly this test.  The transducer route "
          "is the first that does not.")


# ---------------------------------------------------------------------------
# [7] what cohomology does see: the period of the local system
# ---------------------------------------------------------------------------

def section_7() -> None:
    print("\n[7] what the homology of the fibration does see")

    print("  H^{2k}(C_5, Z) = Z/5 for k > 0, and C_4 acts on it by multiplication by "
          "r^k.")
    print("  In the Lyndon-Hochschild-Serre sequence E_2^{p,q} = H^p(C_4, H^q(C_5, Z)) "
          "the rows q > 0 are")
    print("  5-torsion, killed by [2] for p >= 1, so E_2 is the union of the q = 0 row "
          "and the p = 0 column;")
    print("  every differential leaves that shape, so the sequence collapses.")
    for r in (1, 4, 2):
        surviving = [k for k in range(1, 25) if pow(r, k, MODULUS) == 1]
        period = 2 * surviving[0]
        if period != 2 * monodromy_order(r):
            fail("7", f"period mismatch for r={r}")
        degrees = ", ".join(str(2 * k) for k in surviving[:3])
        print(f"  r={r}: (H^{{2k}})^{{C_4}} != 0 exactly when {monodromy_order(r)} | k, "
              f"so 5-torsion sits in degrees {degrees}, ...")
        print(f"        the 5-primary cohomological period is {period} "
              f"= 2 x (monodromy order)")
    print("  So homology DOES separate C_20, Dic_5 and F_20 -- but the only thing it "
          "reports is the monodromy")
    print("  order, re-encoded as a period.  It supplies no invariant beyond the "
          "parameter of [3], which is why")
    print("  COH-01 stays REFUTED: the gain of the fibration picture is the reduction "
          "of [5], not an invariant.")


# ---------------------------------------------------------------------------
# [8] the sharp form of the missing closure property
# ---------------------------------------------------------------------------

def section_8() -> None:
    print("\n[8] sigma^-1 does not preserve star-freeness, so the missing step is "
          "genuinely a height-1 step")

    # K_0 = A . Gamma*, A = the marked letters with phase 1.  Star-free over Gamma.
    # sigma^-1(K_0) = { w : the suffix phase at position 1 is 1 } over Sigma.
    for label, sigma in (("2-generator alphabet", TWO_GEN),
                         ("full 20-letter alphabet", FULL_SIGMA)):
        start = ("start", 0)

        def step(state, letter, sigma=sigma):
            tag, total = state
            if tag == "start":
                return (EPSILON[letter], EPSILON[letter])
            return (tag, (total + EPSILON[letter]) % PHASES)

        def accept(state):
            tag, total = state
            return tag != "start" and (total - tag) % PHASES == 1

        states, transitions, accepting = build_dfa(sigma, start, step, accept)
        minimal, min_accepting, _ = minimize(transitions, accepting)
        period = transition_monoid_period(minimal)
        verdict = "aperiodic (star-free)" if period == 1 else \
                  f"NOT aperiodic (max period {period}) -- not star-free"
        print(f"  {label}: sigma^-1(A.Gamma*) has a {len(minimal)}-state minimal DFA, "
              f"{verdict}")
        if period == 1:
            fail("8", f"expected sigma^-1 to break star-freeness on {label}")

    print("  A.Gamma* is star-free over Gamma (no star at all), yet its sigma-preimage "
          "is not.  Hence the")
    print("  closure property needed in [5] cannot be obtained from any star-free "
          "closure theorem;")
    print("  the transducer's state monoid is the group C_4, and PST-CL-01 covers only "
          "the one-state case")
    print("  (inverse alphabetic morphisms).  The gap between what is proved and what "
          "F_20 needs is exactly")
    print("  'one state' versus 'monodromy many states'.")


# ---------------------------------------------------------------------------
# [9] how much each hypothesis on the state monoid buys
# ---------------------------------------------------------------------------

def section_9() -> None:
    print("\n[9] the ladder: what the hypothesis on the transducer's state monoid is "
          "worth")

    # With NO hypothesis, every regular language is the sigma-preimage of a
    # star-free language: mark each letter with the DFA state in front of it, and
    # ask that the last marked letter lands in an accepting state.  "Last letter in
    # a set" is Gamma* . S, which uses no star.
    for label, sigma, length in (("2-generator alphabet", TWO_GEN, 12),
                                 ("full 20-letter alphabet", FULL_SIGMA, 4)):
        checked = 0
        for word in words_upto(sigma, length):
            state = IDENTITY
            marks = []
            for letter in word:
                marks.append((state, letter))
                state = base.compose(state, letter)
            if marks:
                last_state, last_letter = marks[-1]
                accepted = base.compose(last_state, last_letter) == IDENTITY
            else:
                accepted = True
            if accepted != (mu(word) == IDENTITY):
                fail("9", f"the state-marking transducer fails on {word}")
                break
            checked += 1
        print(f"  {label}: marking each letter with the group element in front of it "
              f"makes mu^-1(e) the")
        print(f"    preimage of the STAR-FREE language Gamma*.S -- exact on all "
              f"{checked} words of length <= {length}")

    print("  mu^-1(e) is not star-free (its syntactic monoid is the group F_20, "
          "Schuetzenberger 1965), so:")
    print("  with no hypothesis on the state monoid, sigma^-1 does not preserve gsh 0; "
          "and 'sigma^-1 preserves")
    print("  gsh <= 1 for every finite state monoid' is EQUIVALENT to the full "
          "generalized star-height")
    print("  conjecture, since the same marking works for every regular language.  "
          "The hypothesis is the whole")
    print("  content.  Known rungs: aperiodic state monoid (PST 1992 Thm 7.8), "
          "elementary abelian 2 (PST-GRP-03).")
    print("  The first open rung is a cyclic state monoid of order 4 -- which is "
          "exactly F_20.")


# ---------------------------------------------------------------------------
# [10] the abelian rung would settle every solvable group
# ---------------------------------------------------------------------------

def derived_subgroup(group):
    return group.closure([group.commutator(x, y)
                          for x in group.els for y in group.els])


def krasner_kaloujnine(group, normal):
    """Verify G -> N wr (G/N),  g |-> (q |-> t_q g t_{q.pi(g)}^{-1}, pi(g)).

    Multiplication in N wr Q is (f, p)(f', p') = (q |-> f(q) f'(q p), p p').
    """
    factor = sg.quotient(group, normal)
    coset_of = {}
    for coset in factor.els:
        for element in coset:
            coset_of[element] = coset
    transversal = {coset: next(iter(coset)) for coset in factor.els}

    def embed(g):
        table = {}
        for coset in factor.els:
            t = transversal[coset]
            target = transversal[factor.mul(coset, coset_of[g])]
            value = group.mul(group.mul(t, g), group.inv(target))
            if value not in normal:
                return None
            table[coset] = value
        return (tuple(table[c] for c in factor.els), coset_of[g])

    images = {}
    for g in group.els:
        image = embed(g)
        if image is None:
            return False, factor, "the coordinate function left N"
        images[g] = image

    order = list(factor.els)
    position = {c: i for i, c in enumerate(order)}

    def wreath(left, right):
        f, p = left
        h, q = right
        combined = tuple(group.mul(f[position[c]], h[position[factor.mul(c, p)]])
                         for c in order)
        return (combined, factor.mul(p, q))

    for x in group.els:
        for y in group.els:
            if wreath(images[x], images[y]) != images[group.mul(x, y)]:
                return False, factor, "not a homomorphism"
    if len(set(images.values())) != group.order:
        return False, factor, "not injective"
    return True, factor, "ok"


def section_10() -> None:
    print("\n[10] the abelian rung would settle every solvable group")

    wanted = {"A_4", "F_20", "C7:C3", "SL(2,3)", "S_4", "C_2xA_4"}
    catalogue = [(label, group) for _, label, group in sg.catalogue()
                 if group.name in wanted]
    if len(catalogue) != len(wanted):
        fail("10", f"catalogue lookup found {len(catalogue)} of {len(wanted)} groups")
    for label, group in catalogue:
        series = []
        current = group
        broken = False
        for _ in range(8):
            if current.order == 1:
                break
            derived = derived_subgroup(current)
            if len(derived) == current.order:
                fail("10", f"{label}: perfect subgroup of order {current.order}, "
                           f"not solvable")
                broken = True
                break
            ok, factor, why = krasner_kaloujnine(current, derived)
            if not ok:
                fail("10", f"{label}: Krasner-Kaloujnine step failed ({why})")
                broken = True
                break
            if not factor.is_abelian():
                fail("10", f"{label}: the quotient G/G' is not abelian")
                broken = True
                break
            series.append((current.order, len(derived), factor.order))
            current = sg.Grp(f"{current.name}'", sorted(derived, key=repr),
                             current.mul)
        if broken:
            continue
        if current.order != 1:
            fail("10", f"{label}: derived series did not reach the trivial group "
                       f"(stopped at order {current.order})")
            continue
        chain = " -> ".join(f"{a}" for a, _, _ in series) + " -> 1"
        # orders only: an abelian quotient of order 4 may be C_4 or C_2 x C_2, and
        # naming it would be a guess the computation does not make.
        quotients = ", ".join(str(q) for _, _, q in series)
        print(f"  {label:9s}: derived series {chain};  abelian quotients of orders "
              f"{quotients};")
        print(f"             every step verified an injective homomorphism "
              f"G -> G' wr (G/G')")

    print("  All six groups outside the PST class (SMALL-NONAB-31-01) are solvable, "
          "so iterating the")
    print("  Krasner-Kaloujnine embedding along the derived series presents each of "
          "them by transducers")
    print("  whose state monoids are the ABELIAN quotients G^(i)/G^(i+1).  Hence "
          "TRANSD-ABEL-01 would settle")
    print("  gsh <= 1 for every finite solvable group at once -- all six, not just "
          "F_20.  That is a strong")
    print("  conjecture, and the reason to attack the minimal open rung (state monoid "
          "C_4) rather than it.")


def main() -> int:
    print(__doc__.strip().splitlines()[0])
    print()
    section_1()
    section_2()
    section_3()
    section_4()
    section_5()
    section_6()
    section_7()
    section_8()
    section_9()
    section_10()
    print()
    if failures:
        print(f"FAILURES: {len(failures)}")
        for message in failures:
            print(f"  {message}")
        return 1
    print("All checks passed.")
    print()
    print("Verdict: the fibration analogy is exact.  beta is a 1-cocycle for the "
          "pulled-back Z/4-action,")
    print("F_20 embeds in C_5 wr C_4, and the identity fibre is {eps = 0} cap "
          "sigma^-1(K) with both factors")
    print("of gsh <= 1.  The extension cohomology vanishes identically across the whole "
          "order-20 family, so it")
    print("cannot see the frontier; the one parameter that does is the monodromy order "
          "1, 2, 4, which is also")
    print("the dimension of the hard induced irrep and half the 5-primary cohomological "
          "period.  The problem")
    print("reduces to a single closure question: does sigma^-1 preserve gsh <= 1 for a "
          "transducer whose state")
    print("monoid is a cyclic group of order 4?  Unlike routes (ii) and (iii), this "
          "mechanism passes the")
    print("2-generator calibration.  The hypothesis on the state monoid carries all "
          "the content: aperiodic is")
    print("PST 1992 Thm 7.8, elementary abelian 2 is PST-GRP-03, C_4 is F_20 itself, "
          "arbitrary abelian would")
    print("settle every finite solvable group, and no hypothesis at all is equivalent "
          "to the whole generalized")
    print("star-height conjecture.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
