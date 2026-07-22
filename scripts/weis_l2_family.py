#!/usr/bin/env python3
"""Staged ba*b pair-counting languages ("Weis L2" family), stage m = 2:
generalized star height <= 1, machine-verified.

DEFINITIONS
  For w in {a,b}*, the phase of a position is (# of a strictly before it)
  mod m.  Occurrences of the factor pattern b a^j b are exactly the pairs
  of consecutive b's (j >= 0 is the length of the a-run between them).
    N_{p,q}(w) = #{ consecutive b-pairs : first b at phase p,
                                          second b at phase q }   (mod m)
    T'(w)      = #{ b-terminated a-runs of odd length }
                 (initial run included; = # occurrences of the marked
                  segment pattern; Thomas-style segment count)
  The "Weis L2 family" (CANDIDATES.md Tier 4: staged segment counting of
  the unbounded pattern ba*b) at stage 2 is the Boolean closure of the
  languages { w : N_{p,q}(w) = h mod k }, p,q in Z_2, k in {2,4}, together
  with the run-residue languages { w : T' = h mod k }.

THEOREM (this file, exact product-automaton proofs; no sampling)
  Every such language has generalized star height <= 1.

METHOD ("A4 results" applied to a run-length code)
  The blocker recorded in RESULTS.md §6.3 was that tokenization by an
  infinite prefix code breaks phase tracking: any token language holding
  an unbounded even a-run, e.g. (aa)*, has the group Z/2 in its syntactic
  monoid and is not star-free.  The resolution is the flat-count trick of
  §5 applied to the FINITE prefix code
      X = { b, aa, ab }
  (all tokens of length <= 2, hence star-free; prefix-freeness checked
  below; every word parses uniquely as X* . tail, tail in {eps, a}).
  Exact integer identity, verified exhaustively below:
      #ab-tokens = |w|_a + 2|w|_b - 2*#tokens - [tail = a]
  and #ab-tokens = T', so T' mod 4 only needs |w|_a mod 4, |w|_b mod 2,
  #tokens mod 2 and the tail flag -- each a height-<=1 feature:
      |w|_a = alpha mod 4      :  ((b*a)^4)*-based, star depth 1
      |w|_b = beta  mod 2      :  ((a*b)^2)*-based, star depth 1
      #tok  = nu    mod 2, tail:  (X^2)* X^nu . tail, star depth 1
  The pair atoms N_{p,q} then reduce by the phase-walk alternation: odd
  runs alternate their start phases, so the pair matrix is determined by
  T' mod 4, the cumulative W atoms N_r^(2) mod 4 (RESULTS.md §5 type,
  re-verified here for stage 2), letter counts and boundary flags.  This
  reduction is not hand-waved: it is PROVED below by exhaustive product-
  automaton search (target value is a function of the feature state).

  Every feature's state-indicator languages have height <= 1; a target
  that is a function of the feature state is a finite union of feature
  cells, i.e. a Boolean combination of height-<=1 languages: height <= 1.

STATUS OF THE WEIS (2011) IDENTIFICATION
  The exact definition of Weis's L2 could not be audited from this
  environment (network policy; see PROOF_OBLIGATIONS.md).  This file
  proves height <= 1 for the entire stage-2 family matching the recorded
  description; the identification of Weis's L2 inside the family (and its
  stage) remains an open audit item.  The "order-48 group" note was NOT
  reproduced by any single family instance scanned (subgroup orders seen:
  2,3,4,5,6,8,16,18,24,32,64,81,192,384).

Run:  python3 scripts/weis_l2_family.py        (~1 minute, stdlib only)
      python3 scripts/weis_l2_family.py --m3   (stage-3 frontier record)
"""

import random
import re
import sys
from collections import deque
from itertools import product

ALPHA = "ab"


# ---------------------------------------------------------------- features
class LC:
    """Letter counts: |w|_a mod ma, |w|_b mod mb (commutative; height<=1)."""
    def __init__(self, ma, mb):
        self.ma, self.mb = ma, mb
        self.init = (0, 0)

    def step(self, s, ch):
        na, nb = s
        return ((na + 1) % self.ma, nb) if ch == "a" else (na, (nb + 1) % self.mb)


class Flags:
    """(seen a b yet, initial a-run length mod m).  Indicators star/height<=1:
    e.g. 'no b yet and initial run even' = (aa)*."""
    def __init__(self, m=2):
        self.m = m
        self.init = (False, 0)

    def step(self, s, ch):
        seen, ir = s
        if ch == "a":
            return s if seen else (False, (ir + 1) % self.m)
        return (True, ir)


class CodeTok:
    """Deterministic parser of a FINITE prefix code; counts ALL completed
    tokens mod M; state = (partial token, count mod M).

    Height <= 1 schema for each state indicator (part, c):
        (X^M)* X^c . part      with X = union of the (finite) tokens.
    X finite => X and X^M star-free; single star; unique factorization
    because X is a prefix code (certified in __init__)."""
    def __init__(self, tokens, M, name):
        self.tokens = tuple(tokens)
        self.M = M
        self.name = name
        for t in tokens:
            for u in tokens:
                if t != u and u.startswith(t):
                    raise ValueError(f"{name}: not a prefix code: {t} < {u}")
        self.prefixes = {t[:i] for t in tokens for i in range(len(t) + 1)}
        self.init = ("", 0)

    def step(self, s, ch):
        part, c = s
        if part == "DEAD":
            return s
        cand = part + ch
        if cand in self.tokens:
            return ("", (c + 1) % self.M)
        if cand in self.prefixes:
            return (cand, c)
        return ("DEAD", c)


class TokO:
    """RESULTS.md §5 opener/connector feature (used to re-verify the stage-2
    cumulative W atoms).  Opener 'Ba'*r reaches phase r; tokens {b, aBa}
    (B = b*); counts completed tokens mod c.  NFA-subset construction as in
    scripts/a4_attempt.py."""
    def __init__(self, opener, specs, c):
        self.opener, self.specs, self.c = opener, tuple(specs), c
        self.states, self.index, self.trans = [], {}, {}
        self.init = self._intern(self._closure({("O", 0)}))

    def _closure(self, items):
        seen, stack = set(), list(items)
        while stack:
            it = stack.pop()
            if it in seen:
                continue
            seen.add(it)
            if it[0] == "O":
                p = it[1]
                if p == len(self.opener):
                    stack.append((0, -1, 0))
                elif self.opener[p] == "B":
                    stack.append(("O", p + 1))
            else:
                r, t, p = it
                if t == -1:
                    for ti in range(len(self.specs)):
                        stack.append((r, ti, 0))
                else:
                    spec = self.specs[t]
                    if p == len(spec):
                        stack.append(((r + 1) % self.c, -1, 0))
                    elif spec[p] == "B":
                        stack.append((r, t, p + 1))
        return frozenset(seen)

    def _intern(self, st):
        i = self.index.get(st)
        if i is None:
            i = len(self.states)
            self.index[st] = i
            self.states.append(st)
        return i

    def step(self, si, ch):
        key = (si, ch)
        v = self.trans.get(key)
        if v is None:
            nxt = set()
            for it in self.states[si]:
                if it[0] == "O":
                    p = it[1]
                    if p < len(self.opener):
                        s = self.opener[p]
                        if s == ch:
                            nxt.add(("O", p + 1))
                        elif s == "B" and ch == "b":
                            nxt.add(("O", p))
                else:
                    r, t, p = it
                    if t == -1:
                        continue
                    spec = self.specs[t]
                    if p == len(spec):
                        continue
                    s = spec[p]
                    if s == ch:
                        nxt.add((r, t, p + 1))
                    elif s == "B" and ch == "b":
                        nxt.add((r, t, p))
            v = self._intern(self._closure(nxt))
            self.trans[key] = v
        return v


# ---------------------------------------------------------------- targets
class PairTarget:
    """N_{p,q} mod k at stage m."""
    def __init__(self, m, p, q, k):
        self.m, self.p, self.q, self.k = m, p, q, k
        self.name = f"N[{p},{q}] mod {k} (stage {m})"
        self.init = (0, None, 0)

    def step(self, s, ch):
        ph, lam, c = s
        if ch == "a":
            return ((ph + 1) % self.m, lam, c)
        add = 1 if (lam is not None and lam == self.p and ph == self.q) else 0
        return (ph, ph, (c + add) % self.k)

    def val(self, s):
        return s[2]


class RunResidue:
    """#{b-terminated a-runs of length = s mod d} mod k (T'-type)."""
    def __init__(self, d, s, k):
        self.d, self.s, self.k = d, s, k
        self.name = f"Runs[j={s} mod {d}] mod {k}"
        self.init = (0, 0)

    def step(self, st, ch):
        r, c = st
        if ch == "a":
            return ((r + 1) % self.d, c)
        return (0, (c + (1 if r == self.s else 0)) % self.k)

    def val(self, st):
        return st[1]


class WTarget:
    """Cumulative W atom N_r^(m) mod k (b's at phase r)."""
    def __init__(self, m, r, k):
        self.m, self.r, self.k = m, r, k
        self.name = f"W(stage{m},res{r},mod{k})"
        self.init = (0, 0)

    def step(self, s, ch):
        p, c = s
        if ch == "a":
            return ((p + 1) % self.m, c)
        return (p, (c + (1 if p == self.r else 0)) % self.k)

    def val(self, s):
        return s[1]


# --------------------------------------------------- exact product checks
def prove_function(feats, target, cap=8_000_000):
    """Exact: BFS the product of feature machines x target; the target value
    must be constant on each feature cell.  Returns (verdict, cells)."""
    start = (tuple(f.init for f in feats), target.init)
    seen = {start}
    q = deque([start])
    cell = {}
    while q:
        fss, tg = q.popleft()
        v = target.val(tg)
        prev = cell.get(fss)
        if prev is None:
            cell[fss] = v
        elif prev != v:
            return False, None
        for ch in ALPHA:
            nx = (tuple(f.step(s, ch) for f, s in zip(feats, fss)),
                  target.step(tg, ch))
            if nx not in seen:
                if len(seen) > cap:
                    return None, None
                seen.add(nx)
                q.append(nx)
    return True, cell


# ------------------------------------------------------------ identities
def parse_X(w):
    """Reference X = {b, aa, ab} parse: returns (#tokens, #ab, tail)."""
    n = nab = 0
    i = 0
    while i < len(w):
        if w[i] == "b":
            n += 1
            i += 1
        elif i + 1 < len(w):
            n += 1
            if w[i + 1] == "b":
                nab += 1
            i += 2
        else:
            return n, nab, "a"
    return n, nab, ""


def brute_counts(w, m=2):
    """Direct pair/run counts by definition."""
    phases = []
    a = 0
    runs = []
    run = 0
    for ch in w:
        if ch == "a":
            a += 1
            run += 1
        else:
            phases.append(a % m)
            runs.append(run)
            run = 0
    pairs = {}
    for p, q in product(range(m), repeat=2):
        pairs[(p, q)] = sum(
            1 for i in range(len(phases) - 1)
            if phases[i] == p and phases[i + 1] == q)
    tprime = sum(1 for j in runs if j % 2 == 1)
    return pairs, tprime, runs


def check_identity(maxlen=16):
    """#ab = |w|_a + 2|w|_b - 2#tok - [tail=a], and #ab = T' (exhaustive)."""
    for L in range(maxlen + 1):
        for x in range(2 ** L):
            w = "".join("ab"[(x >> i) & 1] for i in range(L))
            n, nab, tail = parse_X(w)
            A, B = w.count("a"), w.count("b")
            if nab != A + 2 * B - 2 * n - (1 if tail == "a" else 0):
                return False, w
            _, tprime, _ = brute_counts(w)
            if nab != tprime:
                return False, w
    return True, None


# ----------------------------------------------- independent re-based check
def re_pieces(alpha, beta, nu, tail):
    """Explicit star-height-1 pieces as Python regexes (star depth 1):
    |w|_a = alpha mod 4; |w|_b = beta mod 2; #tok = nu mod 2 with tail."""
    pa = rf"^(?:(?:b*a){{4}})*(?:b*a){{{alpha}}}b*$"
    pb = rf"^(?:(?:a*b){{2}})*(?:a*b){{{beta}}}a*$"
    x = "(?:b|aa|ab)"
    pt = rf"^(?:{x}{{2}})*{x}{{{nu}}}{'a' if tail == 'a' else ''}$"
    return pa, pb, pt


def independent_T4_check(t, maxlen=13, rand_words=20000, rand_len=200, seed=7):
    """Language {w : T' = t mod 4} as an explicit Boolean combination of
    star-height-1 pieces, evaluated with the independent `re` engine."""
    tuples = [(al, be, nu, ta)
              for al in range(4) for be in range(2) for nu in range(2)
              for ta in ("", "a")
              if (al + 2 * be - 2 * nu - (1 if ta == "a" else 0)) % 4 == t]
    compiled = [(re.compile(pa), re.compile(pb), re.compile(pt))
                for (pa, pb, pt) in (re_pieces(*tp) for tp in tuples)]

    def member(w):
        return any(ra.fullmatch(w) and rb.fullmatch(w) and rt.fullmatch(w)
                   for ra, rb, rt in compiled)

    def words():
        for L in range(maxlen + 1):
            for x in range(2 ** L):
                yield "".join("ab"[(x >> i) & 1] for i in range(L))
        rnd = random.Random(seed)
        for _ in range(rand_words):
            L = rnd.randint(0, rand_len)
            yield "".join(rnd.choice("ab") for _ in range(L))

    for w in words():
        _, tprime, _ = brute_counts(w)
        if member(w) != (tprime % 4 == t):
            return False, w
    return True, None


# ---------------------------------------------------------------- driver
def main():
    print("== Weis-L2 family, stage m = 2: height <= 1 (machine proof) ==\n")

    print("[1] prefix-code certification for X = {b, aa, ab}")
    CodeTok(["b", "aa", "ab"], 2, "X")           # raises if not a prefix code
    print("    OK: pairwise prefix-free; tokens finite (star-free).\n")

    print("[2] exact integer identity (exhaustive, all words len <= 16):")
    ok, w = check_identity(16)
    print(f"    #ab = |w|_a + 2|w|_b - 2#tok - [tail=a] = T' : "
          f"{'OK' if ok else 'FAIL at ' + repr(w)}\n")
    assert ok

    print("[3] stage-2 cumulative W atoms via Sec.5 TokO construction:")
    for r in (0, 1):
        feat = TokO("Ba" * r, ["b", "aBa"], 4)
        res, _ = prove_function([LC(8, 4), feat], WTarget(2, r, 4))
        print(f"    N_{r}^(2) mod 4 = f(LC, TokO): "
              f"{'PROVEN (exact)' if res else 'FAIL'}")
        assert res is True
    print()

    print("[4] pair atoms are functions of certified features (exact):")
    feats = [LC(8, 4), Flags(2), CodeTok(["b", "aa", "ab"], 4, "X"),
             WTargetFeature(2, 0, 4), WTargetFeature(2, 1, 4)]
    tables = {}
    targets = ([PairTarget(2, p, q, k)
                for k in (2, 4) for p in (0, 1) for q in (0, 1)]
               + [RunResidue(2, 1, 4)])
    for t in targets:
        res, cells = prove_function(feats, t)
        print(f"    {t.name}: {'PROVEN function of features' if res else 'FAIL'}")
        assert res is True
        tables[t.name] = (t, cells)
    print()

    print("[5] independent end-to-end check of the cell tables "
          "(random words, direct counting vs feature lookup):")
    rnd = random.Random(11)
    checked = 0
    for _ in range(30000):
        L = rnd.randint(0, 300)
        w = "".join(rnd.choice("ab") for _ in range(L))
        fss = tuple(f.init for f in feats)
        for ch in w:
            fss = tuple(f.step(s, ch) for f, s in zip(feats, fss))
        pairs, tprime, _ = brute_counts(w)
        for name, (t, cells) in tables.items():
            if isinstance(t, PairTarget):
                truth = pairs[(t.p, t.q)] % t.k
            else:
                truth = tprime % 4
            assert cells[fss] == truth, (name, w)
            checked += 1
    print(f"    OK: {checked} value comparisons, 30k random words "
          f"(len <= 300), zero mismatches.\n")

    print("[6] fully explicit star-height-1 expression for one atom,")
    print("    L = { w : T' = 0 mod 4 }, evaluated with the independent")
    print("    `re` engine (all words len <= 13 + 20k random, len <= 200):")
    ok, w = independent_T4_check(0)
    print(f"    {'OK: exact agreement' if ok else 'FAIL at ' + repr(w)}\n")
    assert ok

    print("CONCLUSION: every Boolean combination of stage-2 staged ba*b")
    print("pair counts N_{p,q} mod 2 or 4 and odd-run counts mod 4 has")
    print("generalized star height <= 1.")


class WTargetFeature(WTarget):
    """W atom used as a feature (its state is the feature)."""
    pass


# ------------------------------------------------------- stage-3 frontier
def main_m3():
    """Stage m = 3: what the certified feature family does and does not
    reach (exact verdicts; the negatives are the recorded obstruction for
    PROOF_OBLIGATIONS.md N-L2-M3-001).

    Integrality lock: a prefix code whose tokens cover single a-runs spends
    (j + c_r)/3 tokens on a run of length j = r mod 3 with c_r = -r mod 3
    forced, so its flat count only yields the (2*T1 + T2) mod 3 line;
    together with letter parities this pins T1 mod 2 (proved below) but
    provably nothing else in the family was reached: the (T1 + T2)-type
    combination would need the single-letter token 'a', which collides
    with the filler 'aaa' (not a prefix code), and the cascade code Z3
    (r = 1 runs stealing the next letter) de-linearizes the residues --
    the product automaton rejects it below."""
    X3 = ["b", "aaa", "ab", "aab"]
    Z3 = ["b", "aaa", "aab", "aba", "abb"]
    print("== stage m = 3 frontier ==\n")
    print("[1] prefix-code certifications: X3 = {b,aaa,ab,aab}, "
          "Z3 = {b,aaa,aab,aba,abb}")
    CodeTok(X3, 2, "X3")
    CodeTok(Z3, 2, "Z3")
    print("    OK.\n")

    print("[2] positive: T1 = #runs(j=1 mod 3) mod 2 from flat X3 counts:")
    feats = [LC(12, 4), Flags(3), CodeTok(X3, 6, "X3")]
    res, _ = prove_function(feats, RunResidue(3, 1, 2), cap=20_000_000)
    print(f"    Runs[j=1 mod 3] mod 2 = f(LC(12,4), flags, #tok_X3 mod 6): "
          f"{'PROVEN (exact)' if res else 'FAIL'}")
    assert res is True
    print()

    print("[3] negatives (exact NOT-a-function verdicts; the obstruction):")
    feats = [LC(36, 8), Flags(3), CodeTok(X3, 6, "X3"), CodeTok(Z3, 6, "Z3"),
             WTargetFeature(3, 0, 6), WTargetFeature(3, 1, 6),
             WTargetFeature(3, 2, 6)]
    targets = ([RunResidue(3, 0, 2), RunResidue(3, 2, 2), RunResidue(3, 1, 4)]
               + [PairTarget(3, p, q, 2)
                  for p, q in product(range(3), repeat=2)])
    for t in targets:
        res, _ = prove_function(feats, t, cap=20_000_000)
        verdict = {True: "function (unexpected!)", False: "NOT a function",
                   None: "cap exceeded"}[res]
        print(f"    {t.name}: {verdict}")
    print("\nRecorded: stage-3 pair atoms are outside the current certified")
    print("feature family (LC, flags, finite-code flat counts, W atoms).")


if __name__ == "__main__":
    if "--m3" in sys.argv[1:]:
        main_m3()
    else:
        main()
