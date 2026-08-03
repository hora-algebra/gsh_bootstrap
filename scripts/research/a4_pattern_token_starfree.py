#!/usr/bin/env python3
"""Diagnosis for N-A4-FULL-033: explicit star-free expressions for the
pattern-conditioned cut token languages of `a4_full12.py`.

Everything is checked by EXACT DFA equivalence (not bounded sampling) over a
reduced alphabet with two letters per relevant class, which is fully general
because the token automata only read (eps class, == h, == g) of each letter.

Reduced alphabet (e = eps of the distinguished mover g; e' = 3 - e):
    g  : mover, eps e   (the pattern mover)
    u  : mover, eps e   (other same-type mover)
    d1 : mover, eps e'
    d2 : mover, eps e'
    f1 : filler (eps 0)
    f2 : filler (eps 0)

Sections:
  1. why digrams: token language for pattern ('1', g) with a MOVER g is not
     aperiodic (so the aggregate shortcut is impossible).
  2. exact-DFA re-certification of the boundary-pair frToken formula
     (upgrades the bounded certificate of a4_first_return_token.py).
  3. DFA-level decomposition T_pat = C* . (FR \\ suffix) for all cases.
  4. explicit star-free formulas for T_pat, checked exactly:
       ('1',h) nonmover:            C* = h*
       ('2',h,g), h mover eps e':   C* = (hg)^n
       ('2',h,g), h mover eps e:    candidate below
       ('2',h,g), h filler:         candidate below
"""
import itertools
import sys
from collections import deque

# ---------------- DFA machinery ----------------
# DFA: (n, trans, start, accepts) with trans[s][ch] = state index,
# complete over ALPHA; accepts: frozenset of state indices.

def dfa_minimize(dfa, alpha):
    n, trans, start, acc = dfa
    # restrict to reachable
    reach = [start]
    seen = {start}
    for s in reach:
        for ch in alpha:
            t = trans[s][ch]
            if t not in seen:
                seen.add(t)
                reach.append(t)
    # Moore refinement
    part = {s: (s in acc) for s in reach}
    while True:
        sig = {s: (part[s],) + tuple(part[trans[s][ch]] for ch in alpha)
               for s in reach}
        classes = {}
        for s in reach:
            classes.setdefault(sig[s], len(classes))
        newpart = {s: classes[sig[s]] for s in reach}
        if len(set(newpart.values())) == len(set(part.values())):
            part = newpart
            break
        part = newpart
    m = len(set(part.values()))
    ntr = [dict() for _ in range(m)]
    for s in reach:
        for ch in alpha:
            ntr[part[s]][ch] = part[trans[s][ch]]
    nacc = frozenset(part[s] for s in reach if s in acc)
    return (m, ntr, part[start], nacc)

def dfa_product(d1, d2, op, alpha):
    n1, t1, s1, a1 = d1
    n2, t2, s2, a2 = d2
    idx = {(s1, s2): 0}
    order = [(s1, s2)]
    trans = []
    for (x, y) in order:
        row = {}
        for ch in alpha:
            nx, ny = t1[x][ch], t2[y][ch]
            if (nx, ny) not in idx:
                idx[(nx, ny)] = len(order)
                order.append((nx, ny))
            row[ch] = idx[(nx, ny)]
        trans.append(row)
    acc = frozenset(i for (x, y), i in idx.items()
                    if op(x in a1, y in a2))
    return (len(order), trans, 0, acc)

def dfa_compl(d):
    n, t, s, a = d
    return (n, t, s, frozenset(range(n)) - a)

def dfa_concat(d1, d2, alpha):
    n1, t1, s1, a1 = d1
    n2, t2, s2, a2 = d2

    def norm(x, S):
        if x in a1:
            S = S | {s2}
        return (x, frozenset(S))

    start = norm(s1, frozenset())
    idx = {start: 0}
    order = [start]
    trans = []
    for (x, S) in order:
        row = {}
        for ch in alpha:
            nx = t1[x][ch]
            nS = frozenset(t2[q][ch] for q in S)
            st = norm(nx, nS)
            if st not in idx:
                idx[st] = len(order)
                order.append(st)
            row[ch] = idx[st]
        trans.append(row)
    acc = frozenset(i for (x, S), i in idx.items() if S & a2)
    return dfa_minimize((len(order), trans, 0, acc), alpha)

def dfa_equiv(d1, d2, alpha):
    """None if equivalent, else a witness word."""
    n1, t1, s1, a1 = d1
    n2, t2, s2, a2 = d2
    startp = (s1, s2)
    parent = {startp: None}
    queue = deque([startp])
    while queue:
        (x, y) = queue.popleft()
        if (x in a1) != (y in a2):
            word = []
            cur = (x, y)
            while parent[cur] is not None:
                cur, ch = parent[cur]
                word.append(ch)
            return list(reversed(word))
        for ch in alpha:
            np_ = (t1[x][ch], t2[y][ch])
            if np_ not in parent:
                parent[np_] = ((x, y), ch)
                queue.append(np_)
    return None

def dfa_words(dfa, alpha, maxlen, limit=25):
    """Shortest accepted words (for exploration)."""
    n, t, s, a = dfa
    out = []
    layer = {s: []}
    if s in a:
        out.append([])
    for _ in range(maxlen):
        nxt = {}
        for st, w in layer.items():
            for ch in alpha:
                t2_ = t[st][ch]
                if t2_ not in nxt:
                    nxt[t2_] = w + [ch]
                    if t2_ in a:
                        out.append(w + [ch])
                        if len(out) >= limit:
                            return out
        layer = nxt
    return out

# ---------------- star-free AST ----------------
class E:
    def __init__(self, kind, *args):
        self.kind, self.args = kind, args

def atoms(S):
    return E('atoms', frozenset(S))

def cat(*es):
    r = es[0]
    for x in es[1:]:
        r = E('cat', r, x)
    return r

def uni(*es):
    r = es[0]
    for x in es[1:]:
        r = E('uni', r, x)
    return r

def inter(*es):
    r = es[0]
    for x in es[1:]:
        r = E('int', r, x)
    return r

def comp(e):
    return E('cmp', e)

EPSW = E('eps')

def to_dfa(e, alpha):
    if e.kind == 'eps':
        t = [{ch: 1 for ch in alpha}, {ch: 1 for ch in alpha}]
        return (2, t, 0, frozenset({0}))
    if e.kind == 'atoms':
        S = e.args[0]
        t = [{ch: (1 if ch in S else 2) for ch in alpha},
             {ch: 2 for ch in alpha}, {ch: 2 for ch in alpha}]
        return (3, t, 0, frozenset({1}))
    if e.kind == 'uni':
        return dfa_minimize(dfa_product(to_dfa(e.args[0], alpha),
                                        to_dfa(e.args[1], alpha),
                                        lambda a, b: a or b, alpha), alpha)
    if e.kind == 'int':
        return dfa_minimize(dfa_product(to_dfa(e.args[0], alpha),
                                        to_dfa(e.args[1], alpha),
                                        lambda a, b: a and b, alpha), alpha)
    if e.kind == 'cmp':
        return dfa_compl(to_dfa(e.args[0], alpha))
    if e.kind == 'cat':
        return dfa_concat(to_dfa(e.args[0], alpha),
                          to_dfa(e.args[1], alpha), alpha)
    if e.kind in ('bigint', 'biguni'):
        op = (lambda a, b: a and b) if e.kind == 'bigint' \
            else (lambda a, b: a or b)
        d = to_dfa(e.args[0][0], alpha)
        for x in e.args[0][1:]:
            d = dfa_minimize(dfa_product(d, to_dfa(x, alpha), op, alpha),
                             alpha)
        return d
    raise ValueError(e.kind)

def big_inter(es):
    return E('bigint', list(es))

def big_uni(es):
    return E('biguni', list(es))

# ---------------- alphabet / semantics ----------------
def make_alpha(e):
    ep = 3 - e
    return ['g', 'u', 'd1', 'd2', 'f1', 'f2'], \
           {'g': e, 'u': e, 'd1': ep, 'd2': ep, 'f1': 0, 'f2': 0}

def token_dfa(alpha, EPS, match, q=0):
    """Token language DFA: word ends at the first UNMATCHED landing on q.
    match(buf, ch) -> bool; buf is None right after a cut."""
    ACC, DEAD = ('ACC',), ('DEAD',)
    start = (0, None)
    idx = {start: 0}
    order = [start]
    trans = []
    for st in order:
        row = {}
        if st in (ACC, DEAD):
            for ch in alpha:
                row[ch] = idx.setdefault(DEAD, len(order))
                if row[ch] == len(order):
                    order.append(DEAD)
            trans.append(row)
            continue
        ph, buf = st
        for ch in alpha:
            nph = (ph + EPS[ch]) % 3
            if nph == q:
                ns = (nph, ch) if match(buf, ch) else ACC
            else:
                ns = (nph, ch)
            if ns not in idx:
                idx[ns] = len(order)
                order.append(ns)
            row[ch] = idx[ns]
        trans.append(row)
    acc = frozenset([idx[ACC]]) if ACC in idx else frozenset()
    return dfa_minimize((len(order), trans, 0, acc), alpha)

def cstar_dfa(alpha, EPS, match, q=0):
    """C* : every landing matched, word ends at a landing (or empty)."""
    DEAD = ('DEAD',)
    start = (0, None, True)          # (phase, buf, at-block-boundary)
    idx = {start: 0}
    order = [start]
    trans = []
    for st in order:
        row = {}
        if st == DEAD:
            for ch in alpha:
                row[ch] = idx[DEAD]
            trans.append(row)
            continue
        ph, buf, _ = st
        for ch in alpha:
            nph = (ph + EPS[ch]) % 3
            if nph == q:
                ns = (nph, ch, True) if match(buf, ch) else DEAD
            else:
                ns = (nph, ch, False)
            if ns not in idx:
                idx[ns] = len(order)
                order.append(ns)
            row[ch] = idx[ns]
        trans.append(row)
    acc = frozenset(i for st, i in idx.items()
                    if st != DEAD and st[2])
    return dfa_minimize((len(order), trans, 0, acc), alpha)

def first_return_dfa(alpha, EPS, q=0):
    return token_dfa(alpha, EPS, lambda buf, ch: False, q)

def is_aperiodic(dfa, alpha):
    n, t, s, a = dfa
    gens = {tuple(t[i][ch] for i in range(n)) for ch in alpha}
    monoid = set(gens)
    frontier = list(gens)
    while frontier:
        f = frontier.pop()
        for gfun in gens:
            h = tuple(gfun[f[i]] for i in range(n))
            if h not in monoid:
                monoid.add(h)
                frontier.append(h)
    for f in monoid:
        seenp, gg, k = {}, f, 0
        while gg not in seenp:
            seenp[gg] = k
            gg = tuple(f[gg[i]] for i in range(n))
            k += 1
        if k - seenp[gg] != 1:
            return False
    return True

# NOTE on explicit formulas for the two harder `C*` cases
# (`('2',u,g)` same-type, `('2',f,g)` filler): each `C*` is a 5-state
# APERIODIC automaton, hence star-free by Schützenberger's theorem
# (verified in section 3 below).  An explicit expression is available but
# large; because star-freeness is already certified via aperiodicity, we do
# not need the closed form for the mathematical soundness of `N-A4-FULL-033`.
# The Lean route uses the decomposition `T_pat = C* . (FR \ suffix)` with a
# concrete star-free `C*` (formalization engineering, not a math risk).

# ---------------- star-free building blocks ----------------
def blocks(alpha, EPS):
    movers = [c for c in alpha if EPS[c] != 0]
    fills = [c for c in alpha if EPS[c] == 0]
    m1 = [c for c in alpha if EPS[c] == 1]
    m2 = [c for c in alpha if EPS[c] == 2]
    sigma_star = comp(cat(atoms(alpha), comp(atoms([]))))  # placeholder
    # sigma* = complement of the empty language:
    sigma_star = comp(inter(EPSW, comp(EPSW)))
    sigma_plus = cat(atoms(alpha), sigma_star)
    fill_words = comp(cat(sigma_star, atoms(movers), sigma_star))
    A0, A1, A2 = atoms(fills), atoms(m1), atoms(m2)
    M = atoms(movers)
    mixed = uni(cat(A1, fill_words, A2), cat(A2, fill_words, A1))
    P = uni(cat(A1, fill_words, A1), cat(A2, fill_words, A2))
    three = cat(sigma_star, M, sigma_star, M, sigma_star, M, sigma_star)
    frLong = inter(cat(P, sigma_star), cat(sigma_star, P),
                   comp(cat(sigma_plus, P, sigma_plus)), three)
    FR = uni(A0, mixed, frLong)
    return dict(sigma_star=sigma_star, sigma_plus=sigma_plus,
                fill_words=fill_words, A0=A0, A1=A1, A2=A2, M=M,
                mixed=mixed, P=P, frLong=frLong, FR=FR)

def run_case(name, alpha, EPS, match, cstar_expr, ends_pat_expr, B):
    """Check T_pat == C* . (FR \\ Sigma* pat-suffix) with the given
    star-free C* expression; report witness on failure."""
    tok = token_dfa(alpha, EPS, match)
    F_expr = inter(B['FR'], comp(ends_pat_expr))
    T_expr = cat(cstar_expr, F_expr)
    w = dfa_equiv(tok, to_dfa(T_expr, alpha), alpha)
    # independent DFA-level decomposition check
    cs = cstar_dfa(alpha, EPS, match)
    w2 = dfa_equiv(tok, dfa_concat(cs, to_dfa(F_expr, alpha), alpha), alpha)
    print(f"  {name}:")
    print(f"    decomposition T = C*.F (DFA-level): "
          f"{'OK' if w2 is None else 'FAIL ' + repr(w2)}")
    print(f"    star-free formula: "
          f"{'OK' if w is None else 'WITNESS ' + repr(w)}")
    if w is not None:
        cs_min = dfa_minimize(cs, alpha)
        print(f"    minimal C* DFA states: {cs_min[0]}")
        print(f"    shortest C* words: {dfa_words(cs, alpha, 8, 15)}")
    return w is None and w2 is None

PATTERNS = [
    ("('1',f)   nonmover h",        lambda buf, ch: ch == 'f1'),
    ("('2',d,g) opposite mover h",  lambda buf, ch: ch == 'g' and buf == 'd1'),
    ("('2',u,g) same-type mover h", lambda buf, ch: ch == 'g' and buf == 'u'),
    ("('2',f,g) filler h",          lambda buf, ch: ch == 'g' and buf == 'f1'),
]

def main():
    ok_all = True

    print("=== 1. why digram patterns are necessary ===")
    for e in (1, 2):
        alpha, EPS = make_alpha(e)
        tok = token_dfa(alpha, EPS, lambda buf, ch: ch == 'g')
        ap = is_aperiodic(tok, alpha)
        print(f"  ('1',g) with MOVER g (eps={e}): aperiodic={ap}"
              f"  -> {'shortcut impossible; digram needed' if not ap else '??'}")

    print("\n=== 2. frToken boundary-pair formula: exact DFA equivalence ===")
    for e in (1, 2):
        alpha, EPS = make_alpha(e)
        B = blocks(alpha, EPS)
        frd = first_return_dfa(alpha, EPS)
        w = dfa_equiv(frd, to_dfa(B['FR'], alpha), alpha)
        print(f"  eps(g)={e}: {'OK (exact)' if w is None else 'FAIL ' + repr(w)}")
        ok_all &= (w is None)

    print("\n=== 3. RISK RETIREMENT: every token + C* is aperiodic (=> star-free)")
    print("        and T_pat = C* . (FR minus pat-suffix) exactly ===")
    for e in (1, 2):
        alpha, EPS = make_alpha(e)
        B = blocks(alpha, EPS)
        print(f"-- eps(g) = {e} --")
        for name, match in PATTERNS:
            tok = token_dfa(alpha, EPS, match)
            cs = cstar_dfa(alpha, EPS, match)
            ap_tok = is_aperiodic(tok, alpha)
            ap_cs = is_aperiodic(cs, alpha)
            suffix = pat_suffix(name, alpha, B)
            F = dfa_concat(cs, to_dfa(inter(B['FR'], comp(suffix)), alpha),
                           alpha)
            dec = dfa_equiv(tok, F, alpha)
            ok = ap_tok and ap_cs and dec is None
            ok_all &= ok
            print(f"  {name}: token aperiodic={ap_tok}  C* aperiodic={ap_cs}"
                  f"  T=C*.F {'OK' if dec is None else 'FAIL'+repr(dec)}"
                  f"  [{dfa_minimize(cs, alpha)[0]}-state C*]")

    print("\n=== 4. explicit star-free C* formulas (exact) for the easy cases ===")
    for e in (1, 2):
        alpha, EPS = make_alpha(e)
        B = blocks(alpha, EPS)
        ss = B['sigma_star']
        hstar = comp(cat(ss, atoms([c for c in alpha if c != 'f1']), ss))
        ok_all &= run_case("('1',f)   C* = f*", alpha, EPS,
                           lambda buf, ch: ch == 'f1',
                           hstar, cat(ss, atoms(['f1'])), B)
        only_hg = comp(cat(ss, atoms([c for c in alpha
                                      if c not in ('d1', 'g')]), ss))
        alt = uni(EPSW,
                  inter(only_hg,
                        cat(atoms(['d1']), ss), cat(ss, atoms(['g'])),
                        comp(cat(ss, atoms(['d1']), atoms(['d1']), ss)),
                        comp(cat(ss, atoms(['g']), atoms(['g']), ss))))
        ok_all &= run_case("('2',d,g) C* = (dg)*", alpha, EPS,
                           lambda buf, ch: ch == 'g' and buf == 'd1',
                           alt, cat(ss, atoms(['d1']), atoms(['g'])), B)

    print(f"\noverall: {'ALL OK - 033 mathematical risk retired' if ok_all else 'ITERATION NEEDED'}")
    return 0 if ok_all else 1

def pat_suffix(name, alpha, B):
    ss = B['sigma_star']
    if name.startswith("('1',f)"):
        return cat(ss, atoms(['f1']))
    if name.startswith("('2',d"):
        return cat(ss, atoms(['d1']), atoms(['g']))
    if name.startswith("('2',u"):
        return cat(ss, atoms(['u']), atoms(['g']))
    return cat(ss, atoms(['f1']), atoms(['g']))

if __name__ == "__main__":
    sys.exit(main())
