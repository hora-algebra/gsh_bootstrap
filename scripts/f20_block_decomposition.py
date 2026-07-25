#!/usr/bin/env python3
"""Route (iii) of N-F20-001 -- finite-code block decomposition -- is BLOCKED.

Route (iii) proposed to import key 1 of RESULTS.md 5.9 (`weis_l2_family.py`): replace an
infinite code by a *finite* prefix code, whose star-freeness is then trivial, and recover
the staged counts from an exact integer identity between token counts and letter counts.

The obstruction found here is not a failure of any particular code.  It is a theorem about
every finite code, and it holds for every finite group, not only `F_20`:

  Delay theorem.  Let `G` be a finite group, `Sigma = G` the full alphabet (so the identity
  element is a letter), and let `X` be a *finite* set of nonempty words with bounded delay,
  i.e. `Sigma* = X* F` for some finite `F` -- equivalently, every long enough word has a
  prefix in `X`.  Then `mu(X) = G`.

  Proof.  Fix `z in G`.  The word `z e^D` (the letter `z`, then `D` copies of the identity
  letter) has a prefix in `X` of length at most `D`.  Every nonempty prefix of `z e^D` is
  `z e^j`, whose image is `z`.  Hence `z in mu(X)`.  QED

So the token alphabet of any finite-code block decomposition is, as a set of group elements,
the full alphabet again: the block decomposition is a self-reduction with no gain.  In
particular some token carries `eps = 2`, so the token-level cut DFA has the very period-2
element of `F20-FULL-OBS-01`, and nothing certifies at the token level either.

The theorem is sharp in the alphabet: on the 2-generator alphabet of `F20-STD-01` finite
bounded-delay codes with `mu(X)` a *proper* subset of `F_20` do exist (section [7]).  The
identity letter is what kills the full alphabet, and section [6] shows one cannot simply
delete it: deleting it is legitimate (that is a new reduction, `FULL-ALPH-RED-02`), but the
resulting 19-letter alphabet still forces `|mu(X)| >= 19`.

Claim registered as `F20-BLOCK-OBS-01` (negative, PROVED).

Sections
  [1] codes, greedy parse, exact decision of bounded delay
  [2] the block-reduction identity: the token level is the same coordinate formula
  [3] the delay criterion: which token images `A` are realizable at all
  [4] the delay theorem for the full alphabet, and route (iii) blocked
  [5] no finite phase-neutral code has bounded delay (the naive form of route (iii))
  [6] identity-letter erasure is legitimate but does not help
  [7] positive controls: proper token images DO exist on smaller alphabets

Python standard library only.
"""

from __future__ import annotations

import itertools
import sys
from contextlib import contextmanager

sys.path.insert(0, __file__.rsplit("/", 1)[0])

import f20_full_alphabet as base

PHASES = base.PHASES
MODULUS = base.MODULUS
EPSILON = base.EPSILON
FULL_SIGMA = base.SIGMA
IDENTITY = base.IDENTITY
GROUP = frozenset(FULL_SIGMA)  # Sigma = G for the full alphabet: letters *are* elements

NO_IDENTITY = tuple(g for g in FULL_SIGMA if g != IDENTITY)  # 19 letters
TWO_GEN = ((1, 1), (2, 0))  # a, b of RESULTS.md 5.11 (F20-STD-01)

failures: list[str] = []


def fail(section: str, message: str) -> None:
    failures.append(f"[{section}] {message}")
    print(f"  FAIL [{section}] {message}")


def name(g) -> str:
    return base.letter_name(g)


def show(word) -> str:
    return " ".join(name(g) for g in word) if word else "(empty)"


def mu(word):
    """Ground truth: the direct group product, never the coordinate formula."""
    return base.evaluate(tuple(word))


@contextmanager
def alphabet(sigma):
    """Restrict the imported module's alphabet.  Its functions read module globals."""
    saved = (base.SIGMA, base.NONMOVERS, base.MOVERS, base.CONTRIBUTING)
    base.SIGMA = tuple(sigma)
    base.NONMOVERS = tuple(g for g in base.SIGMA if EPSILON[g] == 0)
    base.MOVERS = tuple(g for g in base.SIGMA if EPSILON[g] != 0)
    base.CONTRIBUTING = tuple(g for g in base.SIGMA if g[1] != 0)
    try:
        yield base.SIGMA
    finally:
        base.SIGMA, base.NONMOVERS, base.MOVERS, base.CONTRIBUTING = saved


# ------------------------------------------------------------------ [1] codes and delay


def is_prefix_code(code) -> bool:
    """No token is a proper prefix of another."""
    tokens = set(code)
    for token in tokens:
        for cut in range(1, len(token)):
            if token[:cut] in tokens:
                return False
    return True


def greedy_parse(word, code):
    """Factor `word` left to right into tokens of the prefix code `code`.

    Returns `(tokens, residue)`; `residue` is the X-free tail that no token covers.
    """
    tokens = []
    index = 0
    lengths = sorted({len(token) for token in code})
    while index < len(word):
        for length in lengths:  # shortest first: for a prefix code this is *the* parse
            candidate = tuple(word[index : index + length])
            if len(candidate) == length and candidate in code:
                tokens.append(candidate)
                index += length
                break
        else:
            return tuple(tokens), tuple(word[index:])
    return tuple(tokens), ()


def free_words(code, sigma, cutoff):
    """All `code`-free words of length <= cutoff (no nonempty prefix is a token)."""
    frontier = [()]
    collected = [()]
    for _ in range(cutoff):
        nxt = []
        for prefix in frontier:
            for letter in sigma:
                extended = prefix + (letter,)
                if extended not in code:
                    nxt.append(extended)
        collected.extend(nxt)
        frontier = nxt
        if not frontier:
            break
    return collected


def delay_is_bounded(code, sigma):
    """Exact decision.  Returns `(bounded, certificate)`.

    A word is code-free when no nonempty prefix of it is a token.  Let `L` be the longest
    token.  If some code-free word has length exactly `L`, every extension of it is
    code-free too -- all of its prefixes of length <= L were already checked and longer
    prefixes are too long to be tokens -- so the code-free set is infinite.  Conversely an
    infinite code-free set contains a word of length >= L whose length-`L` prefix is
    code-free.  So: bounded delay iff no code-free word has length exactly `L`.
    """
    if not code:
        return False, ()
    longest = max(len(token) for token in code)
    words = free_words(code, sigma, longest)
    witnesses = [word for word in words if len(word) == longest]
    if witnesses:
        return False, witnesses[0]
    return True, ()


def token_image(code):
    return frozenset(mu(token) for token in code)


def section_1() -> None:
    print("[1] codes, greedy parse, exact decision of bounded delay")
    singles = frozenset((g,) for g in FULL_SIGMA)
    pairs = frozenset(tuple(w) for w in itertools.product(FULL_SIGMA, repeat=2))
    for label, code, expect in (
        ("Sigma (all 20 letters)", singles, True),
        ("Sigma^2 (all 400 pairs)", pairs, True),
    ):
        if not is_prefix_code(code):
            fail("1", f"{label} is not a prefix code")
        bounded, witness = delay_is_bounded(code, FULL_SIGMA)
        if bounded is not expect:
            fail("1", f"{label}: delay bounded = {bounded}, expected {expect}")
        print(f"  {label}: prefix code, bounded delay = {bounded}, "
              f"|mu(X)| = {len(token_image(code))}")

    # A sparse code with unbounded delay, and the certificate that says so.
    sparse = frozenset({(IDENTITY,) * 2, (TWO_GEN[1],)})
    bounded, witness = delay_is_bounded(sparse, FULL_SIGMA)
    if bounded:
        fail("1", "the sparse two-token code was reported as bounded delay")
    print(f"  sparse code {{e e, b}}: bounded delay = {bounded}, "
          f"code-free witness of maximal length = {show(witness)}")

    # The greedy parse agrees with mu on the products it produces.
    for word in itertools.islice(base.all_words(3), 0, None):
        tokens, residue = greedy_parse(word, pairs)
        rebuilt = tuple(letter for token in tokens for letter in token) + residue
        if rebuilt != word:
            fail("1", f"greedy parse lost letters on {show(word)}")
            break
        if len(residue) >= 2:
            fail("1", f"residue {show(residue)} is not shorter than the token length")
            break
    print("  greedy parse over Sigma^2: reconstructs every word of length <= 3, "
          "residue always shorter than a token")


# ---------------------------------------------------- [2] the block-reduction identity


def section_2() -> None:
    print("\n[2] the block-reduction identity: the token level is the same instance")
    pairs = frozenset(tuple(w) for w in itertools.product(FULL_SIGMA, repeat=2))
    triples = frozenset(tuple(w) for w in itertools.product(FULL_SIGMA, repeat=3))
    checked = 0
    for code, label in ((pairs, "Sigma^2"), (triples, "Sigma^3")):
        for word in base.all_words(4):
            tokens, residue = greedy_parse(word, code)
            # The token word, read as a word over the alphabet of *group elements*.
            token_word = tuple(mu(token) for token in tokens)
            if mu(token_word) != mu(tuple(letter for t in tokens for letter in t)):
                fail("2", f"token product differs from letter product on {show(word)}")
                return
            # And the coordinate formula of RESULTS.md 5.12 applies verbatim one level up.
            if base.coordinate_formula(token_word) != mu(token_word):
                fail("2", f"coordinate formula fails at token level on {show(word)}")
                return
            checked += 1
        print(f"  {label}: token-level product and coordinate formula agree with the "
              f"letter level on all words of length <= 4")
    print(f"  {checked} words checked; the token level of a block decomposition is "
          "*again* a word problem for F_20 over an alphabet of group elements")


# ------------------------------------------------------------- [3] the delay criterion


def frontier_code(sigma, allowed):
    """The canonical code whose token image is contained in `allowed`.

    A word is free exactly when no nonempty prefix has image in `allowed`; the tokens are
    the frontier of that free set.  Returns `None` when the free set is infinite, i.e. when
    no finite bounded-delay code with token image inside `allowed` exists.
    """
    free = [()]
    seen = {()}
    code = set()
    limit = len(GROUP) + 1  # a free word this long repeats an image: cycle, so infinite
    while free:
        nxt = []
        for prefix in free:
            for letter in sigma:
                extended = prefix + (letter,)
                if mu(extended) in allowed:
                    code.add(extended)
                elif extended not in seen:
                    if len(extended) > limit:
                        return None
                    seen.add(extended)
                    nxt.append(extended)
        free = nxt
    return frozenset(code)


def image_is_realizable(sigma, allowed):
    """Graph form of the same question: is the image walk forced into `allowed`?

    Vertices are the group elements outside `allowed`; there is an edge `v -> v g` for every
    letter `g` with `v g` outside `allowed`.  The free set is infinite iff some cycle is
    reachable from the one-letter starts.
    """
    outside = [g for g in GROUP if g not in allowed]
    start = [g for g in sigma if g not in allowed]
    reachable = set()
    stack = list(start)
    while stack:
        vertex = stack.pop()
        if vertex in reachable:
            continue
        reachable.add(vertex)
        for letter in sigma:
            successor = base.compose(vertex, letter)
            if successor not in allowed:
                stack.append(successor)
    # Cycle detection by colouring on the reachable sub-digraph.
    colour = {vertex: 0 for vertex in outside}

    def has_cycle(vertex) -> bool:
        colour[vertex] = 1
        for letter in sigma:
            successor = base.compose(vertex, letter)
            if successor in allowed or successor not in reachable:
                continue
            if colour[successor] == 1:
                return True
            if colour[successor] == 0 and has_cycle(successor):
                return True
        colour[vertex] = 2
        return False

    for vertex in sorted(reachable, key=repr):
        if colour[vertex] == 0 and has_cycle(vertex):
            return False
    return True


def section_3() -> None:
    print("\n[3] the delay criterion: which token images are realizable at all")
    sys.setrecursionlimit(10000)
    trials = []
    for sigma, label in ((FULL_SIGMA, "20 letters"), (NO_IDENTITY, "19 letters"),
                         (TWO_GEN, "2 generators")):
        for missing in FULL_SIGMA:  # the maximal proper images A = G \ {v}
            trials.append((sigma, label, frozenset(GROUP - {missing})))
        trials.append((sigma, label, frozenset(GROUP)))
    disagreements = 0
    for sigma, label, allowed in trials:
        by_graph = image_is_realizable(sigma, allowed)
        by_code = frontier_code(sigma, allowed)
        if by_graph != (by_code is not None):
            disagreements += 1
            fail("3", f"{label}, missing {sorted(GROUP - allowed)}: graph says "
                      f"{by_graph}, direct enumeration says {by_code is not None}")
        if by_code is not None:
            if not is_prefix_code(by_code):
                fail("3", f"{label}: frontier code is not a prefix code")
            bounded, _ = delay_is_bounded(by_code, sigma)
            if not bounded:
                fail("3", f"{label}: frontier code does not have bounded delay")
            if not token_image(by_code) <= allowed:
                fail("3", f"{label}: frontier code leaves the allowed image")
    print(f"  {len(trials)} (alphabet, image) pairs: the graph criterion and direct "
          f"enumeration of the code-free set agree in every case ({disagreements} "
          "disagreements); every realizable case yields a genuine bounded-delay prefix "
          "code with the promised token image")

    # Monotonicity, used below to reduce "all proper images" to "all maximal proper images".
    monotone_checks = 0
    for missing_pair in itertools.combinations(sorted(GROUP, key=repr), 2):
        smaller = frozenset(GROUP - set(missing_pair))
        bigger = frozenset(GROUP - {missing_pair[0]})
        if image_is_realizable(FULL_SIGMA, smaller) and not image_is_realizable(
            FULL_SIGMA, bigger
        ):
            fail("3", "realizability is not monotone in the token image")
        monotone_checks += 1
    print(f"  monotonicity in the token image: {monotone_checks} inclusion pairs, no "
          "violation (a larger allowed image can only make the code-free set smaller)")


# ------------------------------------- [4] the delay theorem, and route (iii) blocked


def section_4() -> None:
    print("\n[4] the delay theorem for the full alphabet, and route (iii) blocked")

    # (a) The witness family of the three-line proof, checked for every element.
    for z in FULL_SIGMA:
        word = (z,)
        for pad in range(len(GROUP) + 2):
            if mu(word) != z:
                fail("4", f"padding by the identity letter changed the image of {name(z)}")
                break
            word = word + (IDENTITY,)
    print(f"  witness family: for every one of the {len(FULL_SIGMA)} elements z, all "
          f"{len(GROUP) + 2} nonempty prefixes of z e^n have image z, so a finite code "
          "missing z leaves them all code-free")

    # (a') The same conclusion when the code only has to parse the *fibre* T, not all of
    #      Sigma*.  This matters: a scheme is free to case-split first and parse only the
    #      words it cares about.  The words z e^n z^{-1} lie in T, and every nonempty proper
    #      prefix of one has image z, so a code missing z can only ever cover such a word by
    #      swallowing it whole -- impossible for all n once the code is finite.
    for z in FULL_SIGMA:
        if z == IDENTITY:
            continue
        inverse = next(g for g in FULL_SIGMA if base.compose(z, g) == IDENTITY)
        for pad in range(len(GROUP) + 2):
            word = (z,) + (IDENTITY,) * pad + (inverse,)
            if mu(word) != IDENTITY:
                fail("4", f"z e^n z^-1 left the fibre for z = {name(z)}, n = {pad}")
                break
            images = {mu(word[:cut]) for cut in range(1, len(word))}
            if images != {z}:
                fail("4", f"a proper prefix of z e^n z^-1 escaped z for {name(z)}: "
                          f"{sorted(images)}")
                break
    print(f"  fibre form: for every z != e and every n <= {len(GROUP) + 1}, the word "
          "z e^n z^-1 lies in T and all of its proper nonempty prefixes have image z -- so "
          "T is not contained in X* F either, for any finite X with z outside mu(X)")

    # (b) Hence no proper token image is realizable.  By monotonicity of section [3] it is
    #     enough to refute the maximal proper images.
    bad = []
    for missing in FULL_SIGMA:
        allowed = frozenset(GROUP - {missing})
        if image_is_realizable(FULL_SIGMA, allowed):
            bad.append(missing)
    if bad:
        fail("4", f"a proper token image was realizable on the full alphabet: {bad}")
    if not image_is_realizable(FULL_SIGMA, frozenset(GROUP)):
        fail("4", "the full token image was reported unrealizable")
    print("  every one of the 20 maximal proper token images is unrealizable on the full "
          "alphabet, and the full image is realizable: mu(X) = F_20 for every finite "
          "bounded-delay code")

    # (c) Consequence: the token level carries an eps = 2 element, so the base cut of the
    #     RESULTS.md 5.5 mechanism fails there exactly as in F20-FULL-OBS-01.
    with alphabet(FULL_SIGMA):
        certificate = base.aperiodicity_certificate(None)
    if certificate["aperiodic"]:
        fail("4", "the base cut certified on the full alphabet, contradicting 5.12")
    print(f"  token-level base cut on mu(X) = F_20: aperiodic = "
          f"{certificate['aperiodic']}, period {certificate['period']}, witness "
          f"{certificate['witness']}")

    # (d) The same statement on the true token alphabet, where distinct tokens sharing an
    #     image are distinct letters.  The period-2 element is a single eps = 2 token.
    pairs = sorted({tuple(w) for w in itertools.product(FULL_SIGMA, repeat=2)}, key=repr)
    period, state_count = token_period_of_base_cut(pairs)
    if period != 2:
        fail("4", f"the eps = 2 token gave period {period}, expected 2")
    print(f"  on the genuine token alphabet Sigma^2 ({len(pairs)} tokens, {state_count} "
          f"DFA states) the base-cut transition of an eps = 2 token has period {period}: "
          "multiplicities do not repair aperiodicity")

    # (e) Certified patterns at token level: nothing certifies, as at letter level.
    with alphabet(FULL_SIGMA):
        _, results, cache = base.certify_patterns()
    certified = sum(1 for value in results.values() if value["aperiodic"])
    print(f"  full pattern table at token level: {certified} of {len(results)} candidates "
          f"certify ({len(cache)} distinct signatures)")
    if certified:
        fail("4", "a pattern certified at token level on the full image")


def token_period_of_base_cut(tokens):
    """Period of the base-cut transition of an eps = 2 token, on the genuine token alphabet.

    The state set is the one `f20_full_alphabet.token_dfa` uses, transplanted to the token
    alphabet: `(phase, previous token)` plus accept and dead, so distinct tokens sharing a
    group image really are distinct letters here and the state count grows with the code.
    The base cut segments at every arrival at phase 0.  A token with total eps = 2 has phase
    orbit {0, 2}, so from an odd phase it bounces 1 <-> 3 and never reaches the cut.
    """
    total_eps = {token: sum(EPSILON[g] for g in token) % PHASES for token in tokens}
    marked = next((token for token in tokens if total_eps[token] == 2), None)
    if marked is None:
        raise AssertionError("the token alphabet has no eps = 2 token")
    states = [(phase, previous) for phase in range(PHASES)
              for previous in (None, *tokens)]
    states += [("accept", None), ("dead", None)]
    index = {state: position for position, state in enumerate(states)}

    def step(state, token):
        if state[0] in ("accept", "dead"):
            return ("dead", None)
        phase = (state[0] + total_eps[token]) % PHASES
        return ("accept", None) if phase == 0 else (phase, token)

    transformation = tuple(index[step(state, marked)] for state in states)
    powers = {}
    power = transformation
    exponent = 1
    while power not in powers:
        powers[power] = exponent
        power = tuple(power[transformation[position]] for position in range(len(power)))
        exponent += 1
    return exponent - powers[power], len(states)


# ---------------------------------------- [5] no finite phase-neutral code, either


def section_5() -> None:
    print("\n[5] no finite phase-neutral code has bounded delay")
    # If every token had total eps = 0 mod 4, the suffix phase at every token boundary
    # would be 0 and beta would become a plain count of token types.  That is exactly what
    # route (iii) wanted.  It is unavailable: the walk can avoid phase 0 forever.
    mover = (2, 0)        # eps = 1
    bouncer = (4, 0)      # eps = 2, phase orbit {0, 2}
    for length in range(1, 15):
        word = (mover,) + (bouncer,) * length
        phases = []
        phase = 0
        for letter in word:
            phase = (phase + EPSILON[letter]) % PHASES
            phases.append(phase)
        if 0 in phases:
            fail("5", f"the bouncing word of length {len(word)} met phase 0")
            break
    print("  u h^n (eps = 1 then n letters of eps = 2): every nonempty prefix has total "
          "phase in {1, 3} for n <= 14, so no phase-neutral word is a prefix -- a "
          "phase-neutral code has delay larger than any bound")
    # And the same for the eps = 0 padding, which is what makes section [4] work.
    for length in range(1, 15):
        word = (bouncer,) + (IDENTITY,) * length
        totals = set()
        phase = 0
        for letter in word:
            phase = (phase + EPSILON[letter]) % PHASES
            totals.add(phase)
        if totals != {2}:
            fail("5", f"h e^n had prefix phases {sorted(totals)}, expected only 2")
            break
    print("  h e^n (eps = 2 then identity letters): every nonempty prefix has total phase "
          "2, so a code all of whose tokens avoid total phase 2 also has unbounded delay")

    # The one canonical phase-neutral code is the first-return code R: the words whose phase
    # walk reaches 0 exactly at the end.  It parses the whole fibre and its tokens *are*
    # phase-neutral, so beta would become a plain count of token types.  Two facts kill it.
    returns = 0
    for length in range(2, 15):
        word = (mover,) + (bouncer,) * (length - 2)
        phase = sum(EPSILON[g] for g in word) % PHASES
        closer = next(g for g in FULL_SIGMA if (phase + EPSILON[g]) % PHASES == 0)
        candidate = word + (closer,)
        walk = []
        running = 0
        for letter in candidate:
            running = (running + EPSILON[letter]) % PHASES
            walk.append(running)
        if walk[-1] != 0 or 0 in walk[:-1]:
            fail("5", f"the first-return word of length {len(candidate)} is not a return")
            break
        returns += 1
    print(f"  and R itself is infinite: {returns} first-return words of pairwise distinct "
          f"lengths 3..15 exhibited, so R is not a finite code")
    with alphabet(FULL_SIGMA):
        r_certificate = base.aperiodicity_certificate(None)
    if r_certificate["aperiodic"]:
        fail("5", "the first-return code certified star-free, contradicting 5.12")
    print(f"  and R is not star-free: the base cut of RESULTS.md 5.5 *is* the DFA of R, and "
          f"F20-FULL-OBS-01 gives it a period-{r_certificate['period']} element "
          f"({r_certificate['witness']}).  Finite codes are blocked by section [4]; the "
          "natural infinite code is blocked by non-aperiodicity")


# --------------------------------------------- [6] identity-letter erasure is legitimate


def erase(word):
    return tuple(g for g in word if g != IDENTITY)


def in_star(word, code):
    """Membership in `code*` by dynamic programming (code is a finite set of words)."""
    lengths = {len(token) for token in code}
    reach = [False] * (len(word) + 1)
    reach[0] = True
    for position in range(len(word) + 1):
        if not reach[position]:
            continue
        for length in lengths:
            if length and word[position : position + length] in code:
                if position + length <= len(word):
                    reach[position + length] = True
    return reach[len(word)]


def in_erasure_star(word, code):
    """Membership in `(B u {e})*` where `B = pi^{-1}(code)` minus the empty word and
    minus everything ending in the identity letter.

    `B` is infinite (it absorbs identity letters freely), so this is a dynamic program over
    cut positions with a membership test rather than a lookup in a finite set.
    """
    reach = [False] * (len(word) + 1)
    reach[0] = True
    for start in range(len(word)):
        if not reach[start]:
            continue
        if word[start] == IDENTITY:
            reach[start + 1] = True
        for stop in range(start + 1, len(word) + 1):
            block = word[start:stop]
            if block[-1] == IDENTITY:
                continue  # B forbids a trailing identity letter, which fixes the cut
            if erase(block) in code:
                reach[stop] = True
    return reach[len(word)]


def section_6() -> None:
    print("\n[6] identity-letter erasure is legitimate, and does not help")
    # (a) mu factors through erasure, so the full-alphabet fibre is the preimage of the
    #     19-letter fibre.  That is the content of the erasure reduction.
    for word in base.all_words(3):
        if mu(word) != mu(erase(word)):
            fail("6", f"erasure changed the image of {show(word)}")
            break
    print("  mu(w) = mu(pi(w)) for all 8421 words of length <= 3: the full-alphabet fibre "
          "is exactly pi^{-1} of the 19-letter fibre")

    # (b) The star step of the erasure argument.  The naive guess pi^{-1}(A*) = ({e} u A)*
    #     is FALSE as soon as a word of A has length >= 2: an identity letter can sit
    #     *inside* a block, and then the block is no longer a factor.  Counterexample
    #     A = {a, k a}, w = k e a: erase(w) = k a is in A, but k and a are not adjacent in
    #     w, so w is not in ({e} u A)*.  The correct statement cuts after the last
    #     non-identity letter of each block:
    #
    #       pi^{-1}(A*) = (B u {e})*,  B = pi^{-1}(A) minus the empty word
    #                                      minus everything ending in the identity letter,
    #
    #     and `B u {e}` is star-free whenever A is: pi^{-1} of a star-free language is
    #     star-free (it is recognized by the same monoid, which is aperiodic), "does not end
    #     in e" is star-free, and {e} is finite.
    small = (IDENTITY, (2, 0), (1, 1))
    a_letter, k_letter = small[1], small[2]
    codes = (
        frozenset({(a_letter,)}),
        frozenset({(a_letter,), (k_letter, a_letter)}),
        frozenset({(a_letter, a_letter), (k_letter,)}),
        frozenset({(), (k_letter, a_letter, k_letter)}),
    )
    naive_broken = 0
    for trial, code in enumerate(codes):
        mismatches = 0
        naive_mismatches = 0
        total = 0
        for length in range(8):
            for word in itertools.product(small, repeat=length):
                total += 1
                target = in_star(erase(word), code)
                if in_erasure_star(word, code) != target:
                    mismatches += 1
                if in_star(word, frozenset(code | {(IDENTITY,)})) != target:
                    naive_mismatches += 1
        if mismatches:
            fail("6", f"corrected erasure identity fails for test code {trial} "
                      f"({mismatches} of {total} words)")
        else:
            print(f"  test code {trial}: pi^{{-1}}(A*) = (B u {{e}})* on all {total} words "
                  f"of length <= 7; the naive ({{e}} u A)* is wrong on "
                  f"{naive_mismatches} of them")
            naive_broken += 1 if naive_mismatches else 0
    if not naive_broken:
        fail("6", "the naive erasure identity was never refuted -- test codes too weak")

    # (b') The concatenation step of the same argument, which is what makes the induction go
    #      through: pi^{-1}(L1 L2) = pi^{-1}(L1) pi^{-1}(L2).  Erasure never merges or splits
    #      letters, so a factorization of pi(w) lifts to a cut of w.  (This is why erasure is
    #      an exception to the PST 1992 caution that non-alphabetic inverse morphisms do not
    #      preserve height; the step fails for morphisms that map a letter to a longer word.)
    languages = (
        frozenset({(a_letter,), (k_letter, k_letter)}),
        frozenset({(), (k_letter,)}),
        frozenset({(a_letter, k_letter)}),
    )
    concat_checks = 0
    for left_language, right_language in itertools.product(languages, repeat=2):
        product = frozenset(
            left + right for left in left_language for right in right_language
        )
        for length in range(7):
            for word in itertools.product(small, repeat=length):
                target = erase(word) in product
                split = any(
                    erase(word[:cut]) in left_language
                    and erase(word[cut:]) in right_language
                    for cut in range(len(word) + 1)
                )
                if target != split:
                    fail("6", f"pi^-1(L1 L2) != pi^-1(L1) pi^-1(L2) on {show(word)}")
                    return
                concat_checks += 1
    print(f"  concatenation step: pi^{{-1}}(L1 L2) = pi^{{-1}}(L1) pi^{{-1}}(L2) on "
          f"{concat_checks} (language pair, word) instances")

    # (c) But the 19-letter alphabet still forces an almost-full token image.
    realizable = [
        sorted(GROUP - allowed, key=repr)
        for allowed in (frozenset(GROUP - set(pair))
                        for pair in itertools.combinations(sorted(GROUP, key=repr), 2))
        if image_is_realizable(NO_IDENTITY, allowed)
    ]
    if realizable:
        fail("6", f"a token image of size 18 was realizable on 19 letters: {realizable}")
    singles = [
        missing for missing in FULL_SIGMA
        if image_is_realizable(NO_IDENTITY, frozenset(GROUP - {missing}))
    ]
    print(f"  19 letters: no token image of size 18 is realizable, and "
          f"{len(singles)} of 20 images of size 19 are -- so |mu(X)| >= 19 and the token "
          "alphabet still carries every eps class, eps = 2 included")
    if not singles:
        fail("6", "no token image of size 19 was realizable on the 19-letter alphabet")
    with alphabet(NO_IDENTITY):
        certificate = base.aperiodicity_certificate(None)
    if certificate["aperiodic"]:
        fail("6", "the base cut certified on the 19-letter alphabet")
    print(f"  base cut on the 19-letter alphabet: aperiodic = "
          f"{certificate['aperiodic']}, period {certificate['period']}, witness "
          f"{certificate['witness']}")


# ------------------------------------------------------------------ [7] positive controls


def minimal_realizable_image(sigma, ceiling=9, exclude=()):
    """Smallest token image realizable on `sigma`, by exhaustive search over sizes.

    `exclude` removes elements from consideration; excluding the letters themselves forces
    every token of the resulting code to have length at least two, i.e. a genuine block
    decomposition rather than the identity reduction.
    """
    elements = [g for g in sorted(GROUP, key=repr) if g not in set(exclude)]
    for size in range(ceiling + 1):
        for allowed in itertools.combinations(elements, size):
            if image_is_realizable(sigma, frozenset(allowed)):
                return size, frozenset(allowed)
    return None, None


def section_7() -> None:
    print("\n[7] positive controls: proper token images DO exist on smaller alphabets")
    size, allowed = minimal_realizable_image(TWO_GEN)
    if size is None:
        fail("7", "no realizable token image found on the 2-generator alphabet")
        return
    code = frontier_code(TWO_GEN, allowed)
    if code is None:
        fail("7", "the criterion accepted an image the enumeration rejects")
        return
    bounded, _ = delay_is_bounded(code, TWO_GEN)
    if not bounded:
        fail("7", "the 2-generator frontier code does not have bounded delay")
    if not is_prefix_code(code):
        fail("7", "the 2-generator frontier code is not a prefix code")
    if not token_image(code) <= allowed:
        fail("7", "the 2-generator frontier code leaves its allowed image")
    print(f"  2-generator alphabet {{a, b}} of F20-STD-01: the minimal realizable token "
          f"image has size {size} out of 20 --")
    print(f"    A = {{{', '.join(name(g) for g in sorted(allowed, key=repr))}}}")
    print(f"    frontier code: {len(code)} tokens, longest {max(len(t) for t in code)}, "
          f"prefix code, bounded delay, mu(X) of size {len(token_image(code))}")

    # That minimum is attained by the letters themselves (the identity reduction).  Forbid
    # the letters, so every token has length >= 2: a genuine block decomposition.
    block_size, block_allowed = minimal_realizable_image(TWO_GEN, exclude=TWO_GEN)
    if block_size is None:
        print("    forbidding the two letters: no image of size <= 9 is realizable")
    else:
        block_code = frontier_code(TWO_GEN, block_allowed)
        bounded_block, _ = delay_is_bounded(block_code, TWO_GEN)
        if not bounded_block or min(len(t) for t in block_code) < 2:
            fail("7", "the block code control is not a bounded-delay code of blocks")
        print(f"    forbidding the two letters (all tokens length >= 2): minimal image "
              f"size {block_size}, "
              f"A = {{{', '.join(name(g) for g in sorted(block_allowed, key=repr))}}}, "
              f"code of {len(block_code)} tokens, lengths "
              f"{min(len(t) for t in block_code)}-{max(len(t) for t in block_code)}")
    print("  so the delay theorem of section [4] is a statement about the *full* "
          "alphabet, not a vacuous one: the identity letter is what forces mu(X) = G")

    # Control the other way: a code that does have bounded delay but whose image is full
    # gives no reduction, and the criterion says the minimum on 20 letters is 20.
    size_full, _ = minimal_realizable_image(FULL_SIGMA, ceiling=3)
    if size_full is not None:
        fail("7", f"a token image of size {size_full} was realizable on 20 letters")
    print("  full alphabet: no token image of size <= 3 is realizable (the minimum is 20 "
          "by section [4])")

    # And the judge is exercised on a case it must accept: Sigma itself.
    trivial = frozenset((g,) for g in FULL_SIGMA)
    bounded, _ = delay_is_bounded(trivial, FULL_SIGMA)
    if not bounded:
        fail("7", "the trivial code Sigma was rejected as unbounded delay")
    if token_image(trivial) != GROUP:
        fail("7", "the trivial code Sigma does not have full token image")
    print("  trivial code X = Sigma: accepted, token image full -- the identity "
          "reduction, which is what route (iii) collapses to")


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
    print()
    if failures:
        print(f"FAILURES: {len(failures)}")
        for message in failures:
            print(f"  {message}")
        return 1
    print("All checks passed.")
    print()
    print("Verdict: for the full-alphabet instance every finite bounded-delay code has")
    print("mu(X) = F_20, so finite-code block decomposition reproduces the same instance")
    print("one level up and certifies nothing.  Route (iii) of N-F20-001 is BLOCKED.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
