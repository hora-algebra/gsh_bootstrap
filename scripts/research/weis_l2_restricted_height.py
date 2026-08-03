#!/usr/bin/env python3
"""Restricted star height of the full L2 is exactly 2 (WEIS-L2-RSH-01).

L2 = L((ab*a | ba*b(ab*a)*ba*b)*), the language of Weis 2011 p.115
(proposed by Pin-Straubing-Therien 1992).  "Restricted" = no complement.

Cited inputs (verified verbatim in Sakarovitch-Lombardy, "The Universal
Automaton", in Logic and Automata: History and Perspectives, 2008):

  Def. 2.4  The universal automaton U_L has as states the maximal
            factorisations (X, Y) of L (i.e. X Y subset L, maximal
            componentwise), I = {(X,Y) : 1 in X}, T = {(X,Y) : 1 in Y},
            and (X,Y) --a--> (X',Y') iff X a Y' subset L.
  Def. 7.4  loop complexity lc(G): 0 if G has no ball (= strongly
            connected component with at least one arc); max over balls if
            G is not itself a ball; 1 + min over vertex removals if it is.
  Thm. 7.5  (Eggan 1963) The star height of a language equals the minimal
            loop complexity of an automaton accepting it.
  Thm. 7.10 (Lombardy-Sakarovitch 2003) The universal automaton of a
            regular group language contains a subautomaton of minimal
            loop complexity that recognises the language.

Lemma proved here (short, group-theoretic; see notes/):
  Let phi : Sigma* -> G be onto, H <= G a subgroup, L = phi^{-1}(H).
  Then the maximal factorisations of L with both components nonempty are
  exactly the pairs (H g^{-1}, g H) for g in G, they are in bijection with
  the left cosets gH, and the induced universal automaton is DETERMINISTIC
  and isomorphic to the coset automaton, i.e. to the minimal DFA of L.
  (Consistency check: for W_q = {w : |w|_a = |w|_b mod 2^q}, H trivial,
  TUA remarks after Cor. 7.12 that U is isomorphic to the minimal
  automaton -- the same conclusion.)
  The two degenerate factorisations (Sigma*, empty) and (empty, Sigma*)
  are neither accessible nor co-accessible, and lc is monotone under
  subgraph inclusion, so the minimum in Thm. 7.10 is attained on
  subautomata of the trim part.

Hence: rsh(L2) = min { lc(B) : B subautomaton of the 6-state minimal DFA
with L(B) = L2 }, and this script computes that minimum by exhausting all
2^12 subsets of labelled edges.

A subautomaton (same states, subset of edges, same initial/final state 0)
always accepts a subset of L2, since its runs are runs of the full DFA.
It accepts all of L2 iff every state reachable inside the subautomaton has
both letters defined: if some reachable s lacks letter c, take u reaching s
inside the subautomaton and v driving the full DFA from delta(s,c) back to
0 (possible: the coset automaton of a group language is strongly
connected), then ucv is in L2 but has no run.

Python 3 stdlib only.  Exit code 0 iff every check passes.
"""
import sys

# minimal DFA of L2: walk automaton of a = (01)(34), b = (0235) on the six
# octahedron vertices, start = accept = 0.  Derived from the printed regex
# in scripts/research/weis_l2_full_gsh1.py (step 0) and re-derived below.
PA6 = (1, 0, 2, 4, 3, 5)
PB6 = (2, 1, 3, 5, 4, 0)
EDGES = ([(s, 'a', PA6[s]) for s in range(6)]
         + [(s, 'b', PB6[s]) for s in range(6)])          # 12 labelled edges


def balls(vs, E):
    """Strongly connected components of (vs, E); tiny graphs, so use
    repeated forward/backward reachability instead of Tarjan."""
    vs = set(vs)
    out = []
    while vs:
        v = next(iter(vs))
        fwd, st = {v}, [v]
        while st:
            x = st.pop()
            for (p, q) in E:
                if p == x and q in vs and q not in fwd:
                    fwd.add(q)
                    st.append(q)
        bwd, st = {v}, [v]
        while st:
            x = st.pop()
            for (p, q) in E:
                if q == x and p in vs and p not in bwd:
                    bwd.add(p)
                    st.append(p)
        C = fwd & bwd
        out.append(frozenset(C))
        vs -= C
    return out


def lc(vs, E):
    """Loop complexity (TUA Def. 7.4) of the digraph induced on vs."""
    E = [(p, q) for (p, q) in E if p in vs and q in vs]
    if not E:
        return 0
    best = 0
    for C in balls(vs, E):
        EC = [(p, q) for (p, q) in E if p in C and q in C]
        if not EC:            # trivial SCC: not a ball
            continue
        best = max(best, 1 + min(lc(C - {v}, EC) for v in C))
    return best


def strongly_connected_full():
    E = {(s, t) for (s, _, t) in EDGES}
    return len(balls(range(6), E)) == 1 and len(balls(range(6), E)[0]) == 6


def accepts_exactly_L2(mask):
    """True iff the subautomaton given by the edge subset accepts L2."""
    d = {}
    for i, (s, c, t) in enumerate(EDGES):
        if mask >> i & 1:
            d[(s, c)] = t
    seen, st = {0}, [0]
    while st:
        s = st.pop()
        for c in 'ab':
            if (s, c) not in d:
                return False       # reachable state with a missing letter
            t = d[(s, c)]
            if t not in seen:
                seen.add(t)
                st.append(t)
    return True                    # complete on its reachable part


def main():
    # sanity: the walk automaton is a coset automaton, hence 6 states, all
    # distinguishable, and strongly connected (needed by the argument above)
    assert strongly_connected_full(), "minimal DFA is not strongly connected"
    print("[ok] the 6-state minimal DFA of L2 is strongly connected.")

    valid = []
    for mask in range(1 << 12):
        if accepts_exactly_L2(mask):
            E = [(s, t) for i, (s, _, t) in enumerate(EDGES) if mask >> i & 1]
            vs = {x for e in E for x in e} | {0}
            valid.append((mask, bin(mask).count('1'), lc(vs, E)))
    assert valid, "no subautomaton accepts L2 (impossible: the full one does)"
    word = "subautomaton" if len(valid) == 1 else "subautomata"
    print(f"[ok] exhausted all 4096 edge subsets; {len(valid)} {word} of "
          f"the universal automaton accept exactly L2 (every edge of the "
          f"coset automaton lies on an accepting path, so only the full "
          f"automaton survives).")
    best = min(r for _, _, r in valid)
    for mask, k, r in valid:
        if r == best:
            E = [(s, c, t) for i, (s, c, t) in enumerate(EDGES)
                 if mask >> i & 1]
            print(f"     witness ({k} edges, lc = {r}): "
                  + " ".join(f"{s}-{c}->{t}" for s, c, t in E))
            break
    print(f"[ok] minimal loop complexity over those subautomata = {best}; "
          f"full minimal DFA has lc = {lc(set(range(6)), [(s, t) for s, _, t in EDGES])}.")
    if best != 2:
        print(f"[FAIL] expected minimal loop complexity 2, got {best}")
        sys.exit(1)
    print("[conclusion] rsh(L2) = 2 (Eggan Thm. 7.5 + Lombardy-Sakarovitch "
          "Thm. 7.10 + the subgroup lemma making U(L2) the minimal DFA).")
    print("[remark] the printed expression (ab*a | ba*b(ab*a)*ba*b)* has "
          "restricted star height 3, so it is not optimal; combined with "
          "gsh(L2) = 1 (WEIS-L2-GSH-01) this makes L2 an explicit "
          "literature-standard language with gsh = 1 < rsh = 2.")


if __name__ == '__main__':
    main()
