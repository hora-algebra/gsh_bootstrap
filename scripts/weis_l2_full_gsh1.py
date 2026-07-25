#!/usr/bin/env python3
"""Full L2 has generalized star-height 1 (WEIS-L2-GSH-01).

L2 = L((ab*a | ba*b(ab*a)*ba*b)*) over {a,b}, exactly as printed in
Weis 2011 p.115 (proposed by Pin-Straubing-Therien 1992).  Remote record
WEIS-L2-OPEN-01 states its generalized star-height was open.  This script
proves gsh(L2) <= 1 by the "diagonal anchor" method and certifies the
result with a complete finite proof:

  0. compile the PRINTED regex to a minimal DFA (ground truth; 6 states,
     the walk automaton of a = (01)(34), b = (0235) on the octahedron
     vertices, start = accept = vertex 0);
  1. build the syntactic group G = <a,b> <= S_6 (order 48 = C2 x S4),
     find the central antipodal involution z, and form the four
     "diagonals" (z-orbits of face pairs); the induced action psi on the
     diagonals sends a to a transposition and b to a 4-cycle;
  2. the two diagonals moved by BOTH letters are exactly the anchor pair
     {d3, d4}; removing an anchor leaves only a-self-loops off-anchor, so
     every first-return language R_d at an anchor d is STAR-FREE, and the
     reach languages W_d(x) = (R_d)* . S_d(x) have height <= 1;
  3. letter parities (|w|_a mod 2, |w|_b mod 2) together with psi
     separate all 48 elements of G (machine-checked injectivity), so
     every fiber phi^{-1}(g) is a Boolean combination of height-1 atoms;
  4. L2 = union of the 8 fibers over Stab(vertex 0); the assembled
     generalized expression has star-height 1 (syntactic check);
  5. compile that expression EXACTLY to a DFA (subset construction +
     Moore minimization), cross-validate the compiler against an
     independent recursive matcher, and prove language equivalence with
     the ground-truth DFA by product reachability (no sampling).

Since the syntactic monoid is a nontrivial group, L2 is not star-free
(Schutzenberger), so gsh(L2) = 1 exactly.

Three independent evaluation paths must agree: the exact DFA compiler, a
recursive interval matcher, and Python's `re` engine applied to the
printed regex.  The same compiler independently reproduces the A4 claim
of RESULTS.md section 5 (scripts/a4_std_dfa_equivalence.py).

Python 3 stdlib only.  Exit code 0 iff every check passes.
"""
import itertools, re, sys, time
from collections import deque

sys.setrecursionlimit(100000)
AL = 'ab'

# ---------------- generalized regex AST ----------------
EMPTY = ('empty',)
EPS = ('eps',)
def lit(c): return ('lit', c)
def cat(*es):
    es = [e for e in es if e != EPS]
    if not es: return EPS
    r = es[0]
    for e in es[1:]:
        r = ('cat', r, e)
    return r
def union(*es): return ('union', tuple(es))
def inter(*es): return ('inter', tuple(es))
def neg(e): return ('not', e)
def star(e): return ('star', e)
def power(e, n): return cat(*([e] * n)) if n > 0 else EPS

TOP = neg(EMPTY)
la, lb = lit('a'), lit('b')

def height(e):
    t = e[0]
    if t in ('empty', 'eps', 'lit'): return 0
    if t in ('union', 'inter'): return max(height(x) for x in e[1])
    if t == 'not': return height(e[1])
    if t == 'cat': return max(height(e[1]), height(e[2]))
    return 1 + height(e[1])

# ---------------- independent matcher (for cross-validation) ----------------
def match(expr, w, i, j, memo):
    key = (expr, i, j)
    v = memo.get(key)
    if v is not None: return v
    t = expr[0]
    if t == 'empty': r = False
    elif t == 'eps': r = (i == j)
    elif t == 'lit': r = (j == i + 1 and w[i] == expr[1])
    elif t == 'union': r = any(match(e, w, i, j, memo) for e in expr[1])
    elif t == 'inter': r = all(match(e, w, i, j, memo) for e in expr[1])
    elif t == 'not': r = not match(expr[1], w, i, j, memo)
    elif t == 'cat':
        r = any(match(expr[1], w, i, k, memo) and match(expr[2], w, k, j, memo)
                for k in range(i, j + 1))
    else:
        if i == j: r = True
        else:
            reach = [False] * (j + 1)
            reach[i] = True
            for p in range(i, j):
                if reach[p]:
                    for q in range(p + 1, j + 1):
                        if not reach[q] and match(expr[1], w, p, q, memo):
                            reach[q] = True
            r = reach[j]
    memo[key] = r
    return r

# ---------------- exact DFA compiler ----------------
def dfa(trans, start, acc):
    return {'t': trans, 's': start, 'a': set(acc)}

def d_empty(): return dfa([{c: 0 for c in AL}], 0, [])
def d_eps():
    return dfa([{c: 1 for c in AL}, {c: 1 for c in AL}], 0, [0])
def d_lit(ch):
    return dfa([{c: (1 if c == ch else 2) for c in AL},
                {c: 2 for c in AL}, {c: 2 for c in AL}], 0, [1])
def d_not(d):
    return dfa(d['t'], d['s'], set(range(len(d['t']))) - d['a'])

def d_prod(d1, d2, op):
    idx = {}
    trans = []
    acc = set()
    start = (d1['s'], d2['s'])
    idx[start] = 0
    trans.append(None)
    work = [start]
    while work:
        p = work.pop()
        i = idx[p]
        if trans[i] is not None: continue
        row = {}
        for c in AL:
            np = (d1['t'][p[0]][c], d2['t'][p[1]][c])
            if np not in idx:
                idx[np] = len(trans)
                trans.append(None)
                work.append(np)
            row[c] = idx[np]
        trans[i] = row
        if op(p[0] in d1['a'], p[1] in d2['a']):
            acc.add(i)
    return dfa(trans, 0, acc)

def eclose(S, eps):
    S = set(S)
    st = list(S)
    while st:
        s = st.pop()
        for t2 in eps.get(s, ()):
            if t2 not in S:
                S.add(t2)
                st.append(t2)
    return frozenset(S)

def nfa_from_dfa(d, off):
    tr = {}
    for i, row in enumerate(d['t']):
        for c, j in row.items():
            tr[(i + off, c)] = {j + off}
    return {'tr': tr, 'eps': {}, 'st': {d['s'] + off},
            'ac': {x + off for x in d['a']}, 'n': len(d['t'])}

def determinize(n):
    start = eclose(n['st'], n['eps'])
    idx = {start: 0}
    order = [start]
    trans = [None]
    i = 0
    while i < len(order):
        S = order[i]
        row = {}
        for c in AL:
            T = set()
            for s in S:
                T.update(n['tr'].get((s, c), ()))
            T = eclose(T, n['eps'])
            if T not in idx:
                idx[T] = len(order)
                order.append(T)
                trans.append(None)
            row[c] = idx[T]
        trans[i] = row
        i += 1
    acc = {j for S, j in idx.items() if S & n['ac']}
    return dfa(trans, 0, acc)

def d_cat(d1, d2):
    n1 = nfa_from_dfa(d1, 0)
    n2 = nfa_from_dfa(d2, n1['n'])
    tr = {}
    tr.update(n1['tr'])
    tr.update(n2['tr'])
    eps = {}
    for s in n1['ac']:
        eps.setdefault(s, set()).update(n2['st'])
    return determinize({'tr': tr, 'eps': eps, 'st': n1['st'],
                        'ac': n2['ac'], 'n': n1['n'] + n2['n']})

def d_star(d):
    n = nfa_from_dfa(d, 1)   # state 0: new start/accept hub
    eps = {0: set(n['st'])}
    for s in n['ac']:
        eps.setdefault(s, set()).add(0)
    return determinize({'tr': n['tr'], 'eps': eps, 'st': {0},
                        'ac': {0}, 'n': n['n'] + 1})

def d_min(d):
    reach = {d['s']}
    st = [d['s']]
    while st:
        s = st.pop()
        for c in AL:
            t2 = d['t'][s][c]
            if t2 not in reach:
                reach.add(t2)
                st.append(t2)
    order = sorted(reach)
    remap = {s: i for i, s in enumerate(order)}
    trans = [{c: remap[d['t'][s][c]] for c in AL} for s in order]
    acc = {remap[s] for s in d['a'] if s in remap}
    n = len(order)
    cls = [1 if i in acc else 0 for i in range(n)]
    while True:
        sig = {}
        new = [0] * n
        for i in range(n):
            key = (cls[i], tuple(cls[trans[i][c]] for c in AL))
            if key not in sig:
                sig[key] = len(sig)
            new[i] = sig[key]
        if new == cls:
            break
        cls = new
    k = len(set(cls))
    trans2 = [None] * k
    for i in range(n):
        trans2[cls[i]] = {c: cls[trans[i][c]] for c in AL}
    acc2 = {cls[i] for i in acc}
    return dfa(trans2, cls[remap[d['s']]], acc2)

_compile_cache = {}
def compile_dfa(e):
    if e in _compile_cache:
        return _compile_cache[e]
    t = e[0]
    if t == 'empty': d = d_empty()
    elif t == 'eps': d = d_eps()
    elif t == 'lit': d = d_lit(e[1])
    elif t == 'not': d = d_not(compile_dfa(e[1]))
    elif t == 'union':
        ds = [compile_dfa(x) for x in e[1]]
        d = ds[0]
        for x in ds[1:]:
            d = d_min(d_prod(d, x, lambda p, q: p or q))
    elif t == 'inter':
        ds = [compile_dfa(x) for x in e[1]]
        d = ds[0]
        for x in ds[1:]:
            d = d_min(d_prod(d, x, lambda p, q: p and q))
    elif t == 'cat':
        d = d_cat(compile_dfa(e[1]), compile_dfa(e[2]))
    else:
        d = d_star(compile_dfa(e[1]))
    d = d_min(d)
    _compile_cache[e] = d
    return d

def d_accepts(d, w):
    s = d['s']
    for c in w:
        s = d['t'][s][c]
    return s in d['a']

def equivalence_counterexample(d1, d2):
    """BFS the product; return a shortest distinguishing word or None."""
    start = (d1['s'], d2['s'])
    seen = {start: ''}
    dq = deque([start])
    while dq:
        p = dq.popleft()
        if (p[0] in d1['a']) != (p[1] in d2['a']):
            return seen[p]
        for c in AL:
            np = (d1['t'][p[0]][c], d2['t'][p[1]][c])
            if np not in seen:
                seen[np] = seen[p] + c
                dq.append(np)
    return None

# ---------------- step 0: ground truth from the PRINTED regex ----------------
# L2 = ( ab*a  |  ba*b (ab*a)* ba*b )*
ABA = cat(la, star(lb), la)
INNER = union(ABA, cat(lb, star(la), lb, star(ABA), lb, star(la), lb))
L2_PRINTED = star(INNER)

# the same language for Python's `re` engine (third, fully independent path)
L2_RE = re.compile(r'(?:ab*a|ba*b(?:ab*a)*ba*b)*')

# expected minimal DFA: walk automaton of a=(01)(34), b=(0235) on the six
# octahedron vertices, start = accept = 0 (WEIS-L2-AUDIT-01)
PA6 = (1, 0, 2, 4, 3, 5)
PB6 = (2, 1, 3, 5, 4, 0)

def ground_truth():
    dT = compile_dfa(L2_PRINTED)
    walk = dfa([{'a': PA6[s], 'b': PB6[s]} for s in range(6)], 0, [0])
    cex = equivalence_counterexample(dT, walk)
    assert len(dT['t']) == 6, f"minimal DFA has {len(dT['t'])} states, expected 6"
    assert cex is None, f"printed regex != walk automaton, counterexample {cex!r}"
    return walk

# ---------------- step 1: group, diagonals, anchor action ----------------
def pm(p, q):  # apply p, then q
    return tuple(q[p[i]] for i in range(6))

ID6 = tuple(range(6))

def build_group():
    """G = <PA6, PB6> with a BFS witness word per element."""
    els = {ID6: ''}
    frontier = deque([ID6])
    while frontier:
        g = frontier.popleft()
        for c, P in (('a', PA6), ('b', PB6)):
            h = pm(g, P)
            if h not in els:
                els[h] = els[g] + c
                frontier.append(h)
    return els

def diagonals(els):
    """The 4 z-orbits of octahedron faces (z = central antipodal map)."""
    G = list(els)
    zc = [g for g in G if g != ID6
          and all(pm(g, h) == pm(h, g) for h in (PA6, PB6))
          and all(g[i] != i for i in range(6)) and pm(g, g) == ID6]
    assert len(zc) == 1, "central fixed-point-free involution not unique"
    Z = zc[0]
    faces = [f for f in itertools.combinations(range(6), 3)
             if not any(Z[x] in f for x in f)]
    assert len(faces) == 8
    D, seen = [], set()
    for f in faces:
        k = frozenset(f)
        if k in seen: continue
        k2 = frozenset(Z[x] for x in f)
        seen |= {k, k2}
        D.append(frozenset({k, k2}))
    assert len(D) == 4
    return Z, D

def make_psi(D):
    def psi(g):
        out = []
        for d in D:
            f = next(iter(d))
            img = frozenset(g[x] for x in f)
            out.append(next(j for j, dd in enumerate(D) if img in dd))
        return tuple(out)
    return psi

def cyctype(p):
    seen, t = set(), []
    for i in range(len(p)):
        if i in seen: continue
        c, j = 1, p[i]
        seen.add(i)
        while j != i:
            seen.add(j)
            j = p[j]
            c += 1
        t.append(c)
    return sorted(t)

# ---------------- step 2: height-1 atoms from the anchor structure ----------------
Astar = neg(cat(TOP, lb, TOP))   # words without 'b' (= a*), star-free
Na = neg(cat(TOP, la, TOP))      # words without 'a' (= b*), star-free

def esc_words(anchor, step4):
    """S[x]: star-free expressions for anchor->x paths avoiding the anchor.

    Off-anchor, the only cycles of the 4-diagonal walk are a-self-loops,
    absorbed as Astar; hence every escape language is star-free."""
    exprs = deque()
    out = {}
    for c, l in (('a', la), ('b', lb)):
        t = step4(anchor, c)
        if t != anchor:
            exprs.append((t, l))
    while exprs:
        s, e = exprs.popleft()
        e2 = cat(e, Astar) if step4(s, 'a') == s else e
        out.setdefault(s, []).append(e2)
        for c, l in (('a', la), ('b', lb)):
            t = step4(s, c)
            if t == s or t == anchor: continue
            exprs.append((t, cat(e2, l)))
    return {s: union(*es) if len(es) > 1 else es[0] for s, es in out.items()}

def firstreturn(anchor, S, step4):
    """First-return language at the anchor: star-free."""
    terms = []
    for c, l in (('a', la), ('b', lb)):
        if step4(anchor, c) == anchor: terms.append(l)
    for s, e in S.items():
        for c, l in (('a', la), ('b', lb)):
            if step4(s, c) == anchor: terms.append(cat(e, l))
    return union(*terms)

def parlang(letter, r):
    """{ w : |w|_letter = r mod 2 }, star-height 1."""
    l = la if letter == 'a' else lb
    N = Na if letter == 'a' else Astar
    return cat(star(cat(N, l, N, l)), power(cat(N, l), r), N)

# ---------------- certificate export (tools/regex_cert.py schema) ----------
def to_cert_json(e):
    """Translate the AST into the `gsh-regex-certificate-v1` expression
    schema, which has no intersection: A & B becomes ~(~A | ~B).  Star
    height is unchanged because complement does not count."""
    t = e[0]
    if t == 'empty': return {"op": "empty"}
    if t == 'eps': return {"op": "eps"}
    if t == 'lit': return {"op": "letter", "value": e[1]}
    if t == 'not': return {"op": "compl", "arg": to_cert_json(e[1])}
    if t == 'star': return {"op": "star", "arg": to_cert_json(e[1])}
    if t == 'cat':
        return {"op": "concat", "args": [to_cert_json(e[1]), to_cert_json(e[2])]}
    if t == 'union':
        return {"op": "union", "args": [to_cert_json(x) for x in e[1]]}
    if t == 'inter':
        return {"op": "compl", "arg": {"op": "union", "args": [
            {"op": "compl", "arg": to_cert_json(x)} for x in e[1]]}}
    raise ValueError(t)


def write_certificate(path, expr):
    import json
    data = {
        "schema": "gsh-regex-certificate-v1",
        "description": (
            "Full L2 = L((ab*a | ba*b(ab*a)*ba*b)*), proposed by "
            "Pin-Straubing-Therien 1992 and left open in Weis 2011, has "
            "generalized star-height 1 (claim WEIS-L2-GSH-01, RESULTS.md "
            "5.10). The expression is the union of the eight fibres over "
            "Stab(vertex 0), each an intersection of two letter-parity "
            "languages and two anchor reach languages for the action on the "
            "four cube diagonals; a* and b* are star-free complements, so "
            "the only stars are the outer ones. Generated by "
            "scripts/weis_l2_full_gsh1.py --certificate. Target: the walk "
            "automaton of a = (01)(34), b = (0235) on the six octahedron "
            "vertices, start = accept = v0."),
        "alphabet": list(AL),
        "claimed_height": 1,
        "expression": to_cert_json(expr),
        "target_dfa": {
            "states": [f"v{s}" for s in range(6)],
            "start": "v0",
            "accept": ["v0"],
            "transitions": {
                f"v{s}": {"a": f"v{PA6[s]}", "b": f"v{PB6[s]}"}
                for s in range(6)
            },
        },
    }
    # the expression tree is machine-generated and large, so the metadata is
    # written readably and the tree compactly (42 kB instead of 310 kB)
    with open(path, 'w') as fh:
        fh.write('{\n')
        for key in ("schema", "description", "alphabet", "claimed_height"):
            fh.write(f'  {json.dumps(key)}: {json.dumps(data[key])},\n')
        fh.write('  "expression": '
                 + json.dumps(data["expression"], separators=(',', ':'))
                 + ',\n')
        fh.write('  "target_dfa": '
                 + json.dumps(data["target_dfa"], separators=(',', ':'))
                 + '\n}\n')
    return path


def main():
    t0 = time.time()
    dT = ground_truth()
    print(f"[ok] printed regex compiles to the expected 6-state walk DFA "
          f"(a=(01)(34), b=(0235), start=accept=0). ({time.time()-t0:.0f}s)")

    els = build_group()
    G = list(els)
    assert len(G) == 48, f"|<a,b>| = {len(G)}, expected 48"
    Z, D = diagonals(els)
    psi = make_psi(D)
    pa_, pb_ = psi(PA6), psi(PB6)
    assert cyctype(pa_) == [1, 1, 2], f"psi(a) not a transposition: {pa_}"
    assert cyctype(pb_) == [4], f"psi(b) not a 4-cycle: {pb_}"
    moved = lambda p: {i for i in range(4) if p[i] != i}
    both = sorted(moved(pa_) & moved(pb_))
    assert len(both) == 2, f"doubly-active diagonals: {both}"
    d3, d4 = both
    assert set(both) == moved(pa_), "anchors must be the transposition support"
    print(f"[ok] |G| = 48; psi(a) = {pa_} (transposition), psi(b) = {pb_} "
          f"(4-cycle); anchors = diagonals {both}.")

    def step4(s, c):
        return (pa_ if c == 'a' else pb_)[s]

    # parities of a group element via its BFS witness word; verify the
    # parity map is a well-defined homomorphism G -> C2 x C2
    def pars(g):
        w = els[g]
        return (w.count('a') % 2, w.count('b') % 2)
    for g in G:
        for c, P in (('a', PA6), ('b', PB6)):
            pg, ph = pars(g), pars(pm(g, P))
            e = (1, 0) if c == 'a' else (0, 1)
            assert ph == ((pg[0] + e[0]) % 2, (pg[1] + e[1]) % 2), \
                "letter-parity map not well-defined on G"
    sig = {(pars(g), psi(g)) for g in G}
    assert len(sig) == 48, "signature (parities, psi) not injective on G"
    print("[ok] (|w|_a mod 2, |w|_b mod 2, psi) is well-defined and "
          "separates all 48 elements of G.")

    # height-1 atoms
    S3 = esc_words(d3, step4)
    S4_ = esc_words(d4, step4)
    R3 = firstreturn(d3, S3, step4)
    R4 = firstreturn(d4, S4_, step4)
    assert height(R3) == 0 and height(R4) == 0, "first-return not star-free"
    K3, K4 = star(R3), star(R4)

    def W(anchor, K, S, x):
        return K if x == anchor else cat(K, S[x])

    stab = [g for g in G if g[0] == 0]
    assert len(stab) == 8
    terms = []
    for g in stab:
        pga, pgb = pars(g)
        q = psi(g)
        terms.append(inter(parlang('a', pga), parlang('b', pgb),
                           W(d3, K3, S3, q[d3]), W(d4, K4, S4_, q[d4])))
    L2EXPR = union(*terms)
    h = height(L2EXPR)
    assert h == 1, f"expression has star-height {h}, expected 1"
    print(f"[ok] assembled expression: union of {len(stab)} fibers over "
          f"Stab(vertex 0); star-height = 1.")

    # compile and cross-validate the compiler against the independent matcher
    t0 = time.time()
    dE = compile_dfa(L2EXPR)
    print(f"[ok] compiled expression to a minimized DFA with "
          f"{len(dE['t'])} states. ({time.time()-t0:.0f}s)")
    t0 = time.time()
    for n in range(8):
        for tup in itertools.product(AL, repeat=n):
            w = ''.join(tup)
            if d_accepts(dE, w) != match(L2EXPR, w, 0, len(w), {}):
                print(f"[FAIL] compiler vs matcher disagree on {w!r}")
                sys.exit(1)
    print(f"[ok] DFA compiler agrees with the independent recursive matcher "
          f"on all 255 words of length <= 7. ({time.time()-t0:.0f}s)")

    # third path: Python's own regex engine on the PRINTED expression
    t0 = time.time()
    nre = 0
    for n in range(13):
        for tup in itertools.product(AL, repeat=n):
            w = ''.join(tup)
            nre += 1
            if d_accepts(dE, w) != bool(L2_RE.fullmatch(w)):
                print(f"[FAIL] height-1 DFA vs `re` on the printed regex "
                      f"disagree on {w!r}")
                sys.exit(1)
    print(f"[ok] height-1 expression agrees with Python `re` evaluation of "
          f"the PRINTED regex on all {nre} words of length <= 12. "
          f"({time.time()-t0:.0f}s)")

    # complete finite proof: equivalence with the ground-truth DFA
    cex = equivalence_counterexample(dE, dT)
    if cex is None:
        print("[PROOF] the height-1 expression denotes EXACTLY L2 "
              "(product-automaton reachability, complete finite proof; "
              f"product size <= {len(dE['t']) * 6}).")
        print("[conclusion] gsh(L2) = 1: upper bound above; lower bound "
              "because the syntactic monoid is a nontrivial group "
              "(C2 x S4), so L2 is not star-free (Schutzenberger).")
    else:
        print(f"[FAIL] languages differ; shortest counterexample: {cex!r}")
        sys.exit(1)

    if '--certificate' in sys.argv:
        i = sys.argv.index('--certificate')
        path = (sys.argv[i + 1] if len(sys.argv) > i + 1
                else 'data/certificates/height1_weis_l2_full.json')
        write_certificate(path, L2EXPR)
        print(f"[ok] wrote certificate {path} (check it with "
              f"`python3 scripts/check_certificate.py {path}`, which "
              f"re-verifies the height bound and the equivalence with an "
              f"independent compiler).")

if __name__ == '__main__':
    main()
