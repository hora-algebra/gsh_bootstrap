#!/usr/bin/env python3
"""F_20 sub-alphabets: the RESULTS.md 5.5 pattern-conditioned-cut mechanism cannot
separate the group element, already on the 10-letter sub-alphabet eps in {0,1}.

This refutes route (ii) of PROOF_OBLIGATIONS.md N-F20-001, which conjectured that the
15-letter sub-alphabet eps in {0,1,3} would go through because its base cut certifies
aperiodic.  It does certify -- and the mechanism still fails, for a reason unrelated to
the eps = 2 letters of F20-FULL-OBS-01: two distinct letters carrying the same eps
cannot be ordered by any certified feature.

Claim registered as `F20-SUB10-OBS-01` (negative, PROVED: hand proof in
notes/f20_subalphabet_obstruction.md plus the exhaustive checks below).

Sections
  [1] alphabets and the certified pattern table (exact transition-monoid enumeration)
  [2] the certified feature family
  [3] exhaustive mu-collision search (minimality of the length-4 witness)
  [4] the explicit witness, with every clause of the hand proof checked mechanically
  [5] generosity check: grant every Sum-eps = 0 pattern up to length 3, uncertified
  [6] positive control: the same family DOES separate mu on the 2-generator alphabet

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

# The two sub-alphabets under test, plus the 2-generator alphabet as positive control.
SUB10 = tuple(g for g in FULL_SIGMA if EPSILON[g] in (0, 1))
SUB15 = tuple(g for g in FULL_SIGMA if EPSILON[g] in (0, 1, 3))
TWO_GEN = ((1, 1), (2, 0))  # a, b of RESULTS.md 5.11 (F20-STD-01)

failures: list[str] = []


def fail(section: str, message: str) -> None:
    failures.append(f"[{section}] {message}")
    print(f"  FAIL [{section}] {message}")


@contextmanager
def alphabet(sigma):
    """Restrict the imported module's alphabet.  Its functions read module globals."""
    saved = (base.SIGMA, base.NONMOVERS, base.MOVERS, base.CONTRIBUTING)
    base.SIGMA = tuple(sigma)
    base.NONMOVERS = tuple(g for g in base.SIGMA if EPSILON[g] == 0)
    base.MOVERS = tuple(g for g in base.SIGMA if EPSILON[g] != 0)
    base.CONTRIBUTING = tuple(g for g in base.SIGMA if g[1] != 0)
    try:
        yield base.SIGMA, base.NONMOVERS, base.MOVERS
    finally:
        base.SIGMA, base.NONMOVERS, base.MOVERS, base.CONTRIBUTING = saved


def name(g) -> str:
    return base.letter_name(g)


def show(word) -> str:
    return " ".join(name(g) for g in word) if word else "(empty)"


# ---------------------------------------------------------------- [1] certification


def certification_table(sigma):
    """Exact aperiodicity verdict per pattern signature, including same-letter pairs.

    candidate_patterns() in f20_full_alphabet omits h == g (inherited from the A_4
    scripts, where pure powers were known to fail); we include them so the certified
    family below is provably the *complete* one for this alphabet.
    """
    with alphabet(sigma) as (sig, nonmovers, movers):
        table = {("base",): base.aperiodicity_certificate(None)}
        if nonmovers:
            table[("single", 0)] = base.aperiodicity_certificate(
                ("single", nonmovers[0])
            )
        for g in movers:
            for h in sig:
                key = ("pair", EPSILON[h], EPSILON[g], h == g)
                if key in table:
                    continue
                table[key] = base.aperiodicity_certificate(("pair", h, g))
    return table


def certified_pairs(sigma, table):
    """The (h, g) pairs whose signature certified aperiodic."""
    out = []
    for g in sigma:
        if EPSILON[g] == 0:
            continue
        for h in sigma:
            key = ("pair", EPSILON[h], EPSILON[g], h == g)
            verdict = table.get(key)
            if verdict is not None and verdict["aperiodic"]:
                out.append((h, g))
    return tuple(out)


# ------------------------------------------------------------------- [2] the features


def certified_feature_vector(word, sigma, nonmovers, pairs, extra_patterns=()):
    """Everything the 5.5 mechanism may legitimately read off the word.

    base cuts (all q) + single-nonmover cuts + certified pair cuts + |w|_g mod 5
    + first letter + last letter + total phase.  `extra_patterns` is for section [5].
    """
    data = base.certified_features(word)
    vector = [data.total_phase]
    vector += [data.base_cuts[q] for q in range(PHASES)]
    vector += [
        data.nonmover_count(k, q) for k in nonmovers for q in range(PHASES)
    ]
    vector += [
        data.pair_count(h, g, q) for (h, g) in pairs for q in range(PHASES)
    ]
    vector += [
        suffix_cut(word, pattern, q)
        for pattern in extra_patterns
        for q in range(PHASES)
    ]
    vector += [data.letter_counts.get(g, 0) % MODULUS for g in sigma]
    vector.append(sigma.index(data.first) if data.first is not None else -1)
    vector.append(sigma.index(data.last) if data.last is not None else -1)
    return tuple(vector)


def suffix_cut(word, pattern, q) -> int:
    """Pattern-conditioned cut for a suffix pattern of arbitrary length."""
    residue = 0
    phase = 0
    history: list = []
    span = len(pattern)
    for letter in word:
        phase = (phase + EPSILON[letter]) % PHASES
        history.append(letter)
        if phase == q:
            if len(history) >= span and tuple(history[-span:]) == pattern:
                continue
            residue = (residue + 1) % MODULUS
            history = []
    return residue


def reverse(word):
    return tuple(reversed(word))


def both_directions(word, sigma, nonmovers, pairs, extra=()):
    """Height 1 is closed under reversal, so the backward features are free."""
    return (
        certified_feature_vector(word, sigma, nonmovers, pairs, extra),
        certified_feature_vector(reverse(word), sigma, nonmovers, pairs, extra),
    )


# ------------------------------------------------------- [3] exhaustive collision search


def collision_search(sigma, nonmovers, pairs, max_length, extra=(), limit=4):
    """Return (words_scanned, first `limit` mu-collisions) grouped by feature vector."""
    table: dict = {}
    collisions = []
    scanned = 0
    for length in range(max_length + 1):
        for word in itertools.product(sigma, repeat=length):
            scanned += 1
            key = both_directions(word, sigma, nonmovers, pairs, extra)
            image = base.evaluate(word)
            if key in table:
                other, other_image = table[key]
                if other_image != image:
                    collisions.append((other, word, other_image, image))
                    if len(collisions) >= limit:
                        return scanned, collisions
            else:
                table[key] = (word, image)
    return scanned, collisions


def shortest_collision_length(sigma, nonmovers, pairs, max_length, extra=()):
    for length in range(max_length + 1):
        _, collisions = collision_search(
            sigma, nonmovers, pairs, length, extra, limit=1
        )
        if collisions:
            return length
    return None


# ------------------------------------------------------------------- main


def main() -> int:
    print("=" * 78)
    print("F_20 sub-alphabets: the 5.5 mechanism cannot separate mu (negative result)")
    print("=" * 78)

    # ---------------------------------------------------------------- [1]
    print("\n[1] certified pattern table (exact transition-monoid enumeration)")
    tables = {}
    for label, sigma in (("eps in {0,1}", SUB10), ("eps in {0,1,3}", SUB15)):
        table = certification_table(sigma)
        tables[label] = table
        print(f"  {label}  |Sigma| = {len(sigma)}")
        for key, verdict in table.items():
            if key[0] == "pair":
                total = (key[1] + key[2]) % PHASES
                shape = f"pair eps=({key[1]},{key[2]}) same={str(key[3]):5} Sum={total}"
            else:
                shape = f"{key[0]:<4}" + (f" eps={key[1]}" if len(key) > 1 else "")
            flag = (
                "CERTIFIED"
                if verdict["aperiodic"]
                else f"not aperiodic (period {verdict['period']})"
            )
            print(f"    {shape:38} monoid={verdict['monoid']:5}  {flag}")

    pairs10 = certified_pairs(SUB10, tables["eps in {0,1}"])
    pairs15 = certified_pairs(SUB15, tables["eps in {0,1,3}"])
    print(f"\n  certified pair patterns: eps in {{0,1}} -> {len(pairs10)}, "
          f"eps in {{0,1,3}} -> {len(pairs15)}")
    if pairs10:
        fail("1", f"expected no certified pair on the 10-letter alphabet, got {len(pairs10)}")
    if len(pairs15) != 50:
        fail("1", f"expected 50 certified pairs on the 15-letter alphabet, got {len(pairs15)}")
    if not tables["eps in {0,1}"][("base",)]["aperiodic"]:
        fail("1", "base cut unexpectedly fails on the 10-letter alphabet")
    if not tables["eps in {0,1,3}"][("base",)]["aperiodic"]:
        fail("1", "base cut unexpectedly fails on the 15-letter alphabet")

    # ---------------------------------------------------------------- [3]
    print("\n[3] exhaustive mu-collision search over the certified family")
    for label, sigma, pairs, bound in (
        ("eps in {0,1}", SUB10, pairs10, 4),
        ("eps in {0,1,3}", SUB15, pairs15, 4),
    ):
        nonmovers = tuple(g for g in sigma if EPSILON[g] == 0)
        scanned, collisions = collision_search(sigma, nonmovers, pairs, bound)
        shortest = shortest_collision_length(sigma, nonmovers, pairs, bound)
        print(f"  {label}: {scanned:,} words of length <= {bound}; "
              f"collisions found = {len(collisions)}; shortest = {shortest}")
        if not collisions:
            fail("3", f"{label}: expected a mu-collision, found none")
        if shortest != 4:
            fail("3", f"{label}: expected the shortest collision at length 4, got {shortest}")
        for left, right, image_left, image_right in collisions[:1]:
            print(f"    w0 = {show(left)}   mu = {image_left}")
            print(f"    w1 = {show(right)}  mu = {image_right}")

    # ---------------------------------------------------------------- [4]
    print("\n[4] the canonical witness, one clause of the hand proof per line")
    k = (1, 0)                     # eps = 0, beta = 0   (identity)
    u0 = (2, 0)                    # eps = 1, beta = 0
    u1 = (2, 1)                    # eps = 1, beta = 1
    for letter in (k, u0, u1):
        if letter not in SUB10:
            fail("4", f"witness letter {name(letter)} outside the 10-letter alphabet")
    w0 = (k, u0, u1, k)
    w1 = (k, u1, u0, k)
    print(f"    w0 = {show(w0)}")
    print(f"    w1 = {show(w1)}")

    def phase_trajectory(word):
        out, phase = [], 0
        for letter in word:
            phase = (phase + EPSILON[letter]) % PHASES
            out.append(phase)
        return tuple(out)

    checks = [
        ("identical eps sequence",
         tuple(EPSILON[g] for g in w0) == tuple(EPSILON[g] for g in w1)),
        ("identical phase trajectory",
         phase_trajectory(w0) == phase_trajectory(w1)),
        ("identical arrivals per phase",
         base.certified_features(w0).base_cuts == base.certified_features(w1).base_cuts),
        ("identical nonmover counts per phase", all(
            base.certified_features(w0).nonmover_count(m, q)
            == base.certified_features(w1).nonmover_count(m, q)
            for m in (k,) for q in range(PHASES))),
        ("identical letter multiset", sorted(w0) == sorted(w1)),
        ("identical first and last letter", (w0[0], w0[-1]) == (w1[0], w1[-1])),
        ("identical total phase",
         base.certified_features(w0).total_phase
         == base.certified_features(w1).total_phase),
        ("no certified pair pattern exists at all", len(pairs10) == 0),
        ("full certified feature vectors agree (forward and backward)",
         both_directions(w0, SUB10, tuple(g for g in SUB10 if EPSILON[g] == 0), pairs10)
         == both_directions(w1, SUB10, tuple(g for g in SUB10 if EPSILON[g] == 0), pairs10)),
        ("mu differs", base.evaluate(w0) != base.evaluate(w1)),
    ]
    for text, holds in checks:
        print(f"    {'ok ' if holds else 'NO '} {text}")
        if not holds:
            fail("4", f"witness clause failed: {text}")
    print(f"    mu(w0) = {base.evaluate(w0)},  mu(w1) = {base.evaluate(w1)}")
    print(f"    beta(w0) = 2*beta(u0) + beta(u1) = {2 * u0[1] + u1[1]} mod 5, "
          f"beta(w1) = 2*beta(u1) + beta(u0) = {2 * u1[1] + u0[1]} mod 5")

    # The witness also lies inside the 15-letter alphabet and uses no eps = 3 letter,
    # so the pair features that alphabet does certify cannot fire on it.
    nonmovers15 = tuple(g for g in SUB15 if EPSILON[g] == 0)
    if both_directions(w0, SUB15, nonmovers15, pairs15) != both_directions(
        w1, SUB15, nonmovers15, pairs15
    ):
        fail("4", "witness separated on the 15-letter alphabet (route (ii) not blocked)")
    else:
        print("    ok  still indistinguishable on the 15-letter alphabet "
              "(refutes N-F20-001 route (ii))")

    # ---------------------------------------------------------------- [5]
    print("\n[5] generosity check: grant every Sum-eps = 0 suffix pattern up to length 3")
    print("    (their aperiodicity is NOT certified -- the mechanism is handed more")
    print("     than it has earned, and still fails)")
    for label, sigma in (("eps in {0,1}", SUB10), ("eps in {0,1,3}", SUB15)):
        extra = tuple(
            pattern
            for length in (1, 2, 3)
            for pattern in itertools.product(sigma, repeat=length)
            if (length == 1 or EPSILON[pattern[-1]] != 0)
            and sum(EPSILON[x] for x in pattern) % PHASES == 0
        )
        nonmovers = tuple(g for g in sigma if EPSILON[g] == 0)
        pairs = pairs10 if sigma is SUB10 else pairs15
        _, collisions = collision_search(
            sigma, nonmovers, pairs, 4, extra=extra, limit=1
        )
        print(f"    {label}: {len(extra)} extra patterns granted; "
              f"collision still present = {bool(collisions)}")
        if not collisions:
            fail("5", f"{label}: extra patterns removed the collision")

    # ---------------------------------------------------------------- [6]
    print("\n[6] positive control: the same family on the 2-generator alphabet")
    print("    (F20-STD-01 is height 1, so the family MUST separate mu here;")
    print("     otherwise the judge above would be vacuous)")
    table2 = certification_table(TWO_GEN)
    pairs2 = certified_pairs(TWO_GEN, table2)
    nonmovers2 = tuple(g for g in TWO_GEN if EPSILON[g] == 0)
    scanned, collisions = collision_search(TWO_GEN, nonmovers2, pairs2, 12, limit=1)
    print(f"    alphabet {show(TWO_GEN)}: {scanned:,} words of length <= 12, "
          f"certified pairs = {len(pairs2)}, mu-collisions = {len(collisions)}")
    if collisions:
        left, right, image_left, image_right = collisions[0]
        fail("6", f"positive control broke: {show(left)} vs {show(right)} "
                  f"({image_left} vs {image_right})")
    else:
        print("    ok  mu is a function of the certified features on the 2-generator "
              "alphabet -- the family is not vacuous")

    # ---------------------------------------------------------------- verdict
    print("\n" + "=" * 78)
    if failures:
        print(f"FAILED: {len(failures)} check(s)")
        for line in failures:
            print(f"  {line}")
        return 1
    print("All checks passed.")
    print("Conclusion: on the 10-letter sub-alphabet eps in {0,1} of F_20 -- which")
    print("generates F_20 -- the pattern-conditioned-cut mechanism of RESULTS.md 5.5")
    print("admits NO certified pair pattern, and its certified feature family (closed")
    print("under reversal) does not separate mu.  Minimal witness: length 4.  This is")
    print("a limitation of that mechanism, NOT a lower bound on generalized star")
    print("height: nothing here shows the language has height > 1.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
