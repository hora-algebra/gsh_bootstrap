#!/usr/bin/env python3
"""Independent reproduction of A4-STD-01 (RESULTS.md section 5):
the A4 word problem with generators phi(a)=(123), phi(b)=(12)(34)
has generalized star-height <= 1.

Written from the RESULTS.md prose alone (not from scripts/research/a4_final.py),
and it upgrades the evidence: a4_final.py checks end-to-end agreement on
all words of length <= 16 plus 30k random words, whereas step 4 below is
a COMPLETE finite proof of language equality by product reachability, so
no bounded-length gap remains for this two-generator case.  (A4-FULL-01,
the all-twelve-letters alphabet, is untouched by this script.)

Verification layers:
  1. brute-check the arithmetic characterization against the group (<= len 14);
  2. build an explicit height-1 generalized regex (complement allowed);
  3. compile it EXACTLY to a DFA (subset construction + Moore minimization);
  4. prove language equivalence with the 12-state A4 word-problem DFA by
     product reachability (a complete finite proof, no sampling);
  5. cross-validate the compiler against an independent recursive matcher.
"""
import itertools, random, sys, time
sys.setrecursionlimit(100000)
random.seed(20260722)
AL = 'ab'

# ---------------- A4 ground truth ----------------
def pmul(p, q):  # apply p, then q
    return tuple(q[p[i]] for i in range(4))

PID = (0, 1, 2, 3)
PA = (1, 2, 0, 3)   # (123) acting on {0,1,2}
PB = (1, 0, 3, 2)   # (12)(34)
GEN = {'a': PA, 'b': PB}

def group_order():
    els = {PID}
    st = [PID]
    while st:
        g = st.pop()
        for c in AL:
            h = pmul(g, GEN[c])
            if h not in els:
                els.add(h)
                st.append(h)
    return els

def phi(w):
    g = PID
    for c in w:
        g = pmul(g, GEN[c])
    return g

def pred(w):
    """claimed characterization: |w|_a = 0 mod 3 and N_0 = N_1 = N_2 mod 2,
    N_r = #{b's preceded by = r mod 3 a's}."""
    na = 0
    N = [0, 0, 0]
    for c in w:
        if c == 'a':
            na += 1
        else:
            N[na % 3] += 1
    return na % 3 == 0 and (N[0] % 2 == N[1] % 2 == N[2] % 2)

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
BS = neg(cat(TOP, la, TOP))                      # words without 'a' (= b*), star-free
X = union(lb, cat(la, BS, la, BS, la))           # tokens: b | a b* a b* a   (star-free)
D0 = star(cat(X, X))                             # even token count   (the only star level)
D1 = cat(X, D0)                                  # odd token count
TAIL = [EPS, cat(la, BS), cat(la, BS, la, BS)]   # 0, 1, 2 trailing a's
def OPEN(r): return power(cat(BS, la), r)        # opener: reach phase r (star-free)
def A6(q): return cat(star(power(cat(BS, la), 6)), power(cat(BS, la), q), BS)
A3_0 = cat(star(power(cat(BS, la), 3)), BS)      # |w|_a = 0 mod 3
def LOW(r):                                       # fewer than r a's (star-free)
    if r == 0: return EMPTY
    return union(*[cat(BS, *([cat(la, BS)] * i)) for i in range(r)])
def E(r):
    """{ w : N_r(w) is even }, star-height 1."""
    terms = []
    for s in range(3):
        for c in range(2):
            q = (r + s + 3 * c) % 6
            Dp = D0 if c == 0 else D1
            terms.append(inter(cat(OPEN(r), Dp, TAIL[s]), A6(q)))
    body = union(*terms)
    return union(LOW(r), body) if r > 0 else body

E0, E1, E2 = E(0), E(1), E(2)
LEXPR = inter(A3_0, union(inter(E0, E1, E2),
                          inter(neg(E0), neg(E1), neg(E2))))

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
    # prune unreachable
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

def equivalence_counterexample(d1, d2, maxlen=64):
    """BFS the product; return a shortest distinguishing word or None."""
    start = (d1['s'], d2['s'])
    from collections import deque
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

def main():
    t0 = time.time()
    els = group_order()
    assert len(els) == 12, f"<(123),(12)(34)> has order {len(els)}, expected 12 (A4)"
    print(f"[ok] <(123),(12)(34)> has order 12 (A4).")

    # 1. characterization vs group, exhaustive <= 14
    for n in range(15):
        for tup in itertools.product(AL, repeat=n):
            w = ''.join(tup)
            if (phi(w) == PID) != pred(w):
                print(f"[FAIL] characterization wrong on {w!r}")
                sys.exit(1)
    print(f"[ok] characterization (|w|_a=0 mod 3, N_0=N_1=N_2 mod 2) "
          f"matches the group on all 32767 words of length <= 14. "
          f"({time.time()-t0:.0f}s)")

    print(f"[info] star-height of the expression: {height(LEXPR)}")

    # 2. compile expression to DFA
    t0 = time.time()
    dL = compile_dfa(LEXPR)
    print(f"[ok] compiled expression to a minimized DFA with "
          f"{len(dL['t'])} states. ({time.time()-t0:.0f}s)")

    # 3. cross-validate compiler vs independent matcher (guards compiler bugs)
    t0 = time.time()
    for n in range(10):
        for tup in itertools.product(AL, repeat=n):
            w = ''.join(tup)
            if d_accepts(dL, w) != match(LEXPR, w, 0, len(w), {}):
                print(f"[FAIL] compiler vs matcher disagree on {w!r}")
                sys.exit(1)
    print(f"[ok] DFA compiler agrees with the independent recursive matcher "
          f"on all 1023 words of length <= 9. ({time.time()-t0:.0f}s)")

    # 4. exact equivalence with the A4 word-problem DFA
    elist = sorted(els)
    eidx = {g: i for i, g in enumerate(elist)}
    trans = [{c: eidx[pmul(g, GEN[c])] for c in AL} for g in elist]
    dA4 = dfa(trans, eidx[PID], [eidx[PID]])
    cex = equivalence_counterexample(dL, dA4)
    if cex is None:
        print("[PROOF] the height-1 expression denotes EXACTLY the A4 word "
              "problem language (product-automaton reachability check, "
              f"complete finite proof; product size <= {len(dL['t'])*12}).")
    else:
        print(f"[FAIL] languages differ; shortest counterexample: {cex!r} "
              f"(len {len(cex)}), group says {phi(cex) == PID}")
        sys.exit(1)

if __name__ == '__main__':
    main()
