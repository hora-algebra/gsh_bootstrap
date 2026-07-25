"""Star-free-labelled automata and the relativized Eggan upper bound.

An **SF-automaton** is a finite automaton whose transitions are labelled by
*star-free languages* instead of by single letters.  Because a generalized
regular expression is star-free exactly when its syntactic star height is
zero, "the label is star-free" is a syntactic, decidable side condition on
the certificate, not a semantic obligation.

The module provides

* :func:`loop_complexity` — the cycle rank of the underlying digraph
  (Lombardy--Sakarovitch, *The universal automaton*, Def. 7.4);
* :meth:`SFAutomaton.to_expression` — state elimination performed along the
  cycle-rank decomposition, so that the emitted generalized expression has
  syntactic star height at most the loop complexity.  The construction
  **verifies this bound on every call** and raises otherwise, which makes the
  upper-bound theorem a runtime-checked invariant rather than prose;
* :meth:`SFAutomaton.absorb_self_loop` — the one NFA-level transformation
  that the repository's positive results all use: a self-loop whose star is
  again star-free is folded into the incoming edges, deleting an edge from
  the graph and usually lowering the rank, at no cost in star height;
* the four-diagonal automaton of the Weis ``L2`` language, which reproduces
  the first-return and escape languages printed in
  ``notes/weis_l2_full_height_one.md`` §3.

Nothing here is a star-height *lower* bound.  ``loop_complexity`` bounds
``gsh`` from above only; see ``notes/sf_labeled_automata.md`` §2 for why the
converse half of Eggan's theorem does not relativize.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any, Hashable, Iterable, Mapping, Sequence

from tools.regex_cert import DFA, GRegex


class SFAutomatonError(ValueError):
    """Raised when an SF-automaton or one of its transformations is invalid."""


# --------------------------------------------------------------------------
# Generalized-expression constructors with normalizing simplification.
#
# Simplification matters: state elimination is quadratic in the number of
# subexpressions it copies, and without absorption of the empty language the
# emitted trees become unreadable and slow to compile.
# --------------------------------------------------------------------------

EMPTY = GRegex("empty")
EPS = GRegex("eps")
TOP = GRegex("compl", (EMPTY,))  # the full language Sigma*


def letter(value: str) -> GRegex:
    return GRegex("letter", value=value)


def compl(arg: GRegex) -> GRegex:
    if arg.op == "compl":
        return arg.args[0]
    return GRegex("compl", (arg,))


def star(arg: GRegex) -> GRegex:
    if arg in (EMPTY, EPS):
        return EPS
    return GRegex("star", (arg,))


def union(*args: GRegex) -> GRegex:
    flat: dict[GRegex, None] = {}
    for arg in args:
        parts = arg.args if arg.op == "union" else (arg,)
        for part in parts:
            if part == EMPTY:
                continue
            if part == TOP:
                return TOP
            flat[part] = None
    if not flat:
        return EMPTY
    if len(flat) == 1:
        return next(iter(flat))
    return GRegex("union", tuple(flat))


def concat(*args: GRegex) -> GRegex:
    flat: list[GRegex] = []
    for arg in args:
        parts = arg.args if arg.op == "concat" else (arg,)
        for part in parts:
            if part == EMPTY:
                return EMPTY
            if part == EPS:
                continue
            flat.append(part)
    if not flat:
        return EPS
    if len(flat) == 1:
        return flat[0]
    return GRegex("concat", tuple(flat))


def words_avoiding(letters: Sequence[str], alphabet: Sequence[str]) -> GRegex:
    """``(Sigma \\ letters)*`` written star-free, as ``not(TOP . (union letters) . TOP)``.

    This is the workhorse label: over ``{a, b}`` it turns ``a*`` into the
    star-free ``not(TOP b TOP)``, which is what lets the anchor construction
    of ``notes/weis_l2_full_height_one.md`` §3 stay at star height 0.
    """

    unknown = set(letters) - set(alphabet)
    if unknown:
        raise SFAutomatonError(f"letters {sorted(unknown)!r} are not in the alphabet")
    forbidden = union(*[letter(x) for x in letters])
    if forbidden == EMPTY:
        return TOP
    return compl(concat(TOP, forbidden, TOP))


def any_of(letters: Sequence[str]) -> GRegex:
    return union(*[letter(x) for x in letters])


def pretty(expr: GRegex, aliases: Mapping[GRegex, str] | None = None) -> str:
    """Human-readable rendering, with optional names for known subexpressions."""

    table = dict(aliases or {})
    if expr in table:
        return table[expr]
    if expr.op == "empty":
        return "0"
    if expr.op == "eps":
        return "1"
    if expr.op == "letter":
        return str(expr.value)
    if expr.op == "compl":
        return f"~({pretty(expr.args[0], table)})"
    if expr.op == "star":
        return f"({pretty(expr.args[0], table)})*"
    if expr.op == "union":
        return "(" + " | ".join(pretty(arg, table) for arg in expr.args) + ")"
    if expr.op == "concat":
        return "".join(pretty(arg, table) for arg in expr.args)
    raise SFAutomatonError(f"cannot print operation {expr.op!r}")


# --------------------------------------------------------------------------
# Graph primitives.  Vertex collections are ordered tuples throughout, so that
# every construction below is deterministic and memoizable.
# --------------------------------------------------------------------------

Vertex = Hashable
Edges = Mapping[tuple[Vertex, Vertex], GRegex]


def _restrict(vertices: tuple[Vertex, ...], edges: Edges) -> dict[tuple[Vertex, Vertex], GRegex]:
    inside = set(vertices)
    return {
        pair: label
        for pair, label in edges.items()
        if pair[0] in inside and pair[1] in inside
    }


def _sccs(vertices: tuple[Vertex, ...], edges: Edges) -> list[tuple[Vertex, ...]]:
    """Strongly connected components, by Kosaraju, in ambient vertex order."""

    successors: dict[Vertex, list[Vertex]] = {v: [] for v in vertices}
    predecessors: dict[Vertex, list[Vertex]] = {v: [] for v in vertices}
    for source, target in edges:
        successors[source].append(target)
        predecessors[target].append(source)

    finished: list[Vertex] = []
    seen: set[Vertex] = set()
    for root in vertices:
        if root in seen:
            continue
        seen.add(root)
        stack = [(root, iter(successors[root]))]
        while stack:
            node, walker = stack[-1]
            for nxt in walker:
                if nxt not in seen:
                    seen.add(nxt)
                    stack.append((nxt, iter(successors[nxt])))
                    break
            else:
                finished.append(node)
                stack.pop()

    rank = {v: i for i, v in enumerate(vertices)}
    assigned: set[Vertex] = set()
    components: list[tuple[Vertex, ...]] = []
    for root in reversed(finished):
        if root in assigned:
            continue
        component = [root]
        assigned.add(root)
        stack = [root]
        while stack:
            node = stack.pop()
            for previous in predecessors[node]:
                if previous not in assigned:
                    assigned.add(previous)
                    component.append(previous)
                    stack.append(previous)
        components.append(tuple(sorted(component, key=rank.__getitem__)))
    return components


def _topological_order(
    components: Sequence[tuple[Vertex, ...]], edges: Edges
) -> list[int]:
    """Indices of ``components`` in topological order of the condensation."""

    index_of = {v: i for i, component in enumerate(components) for v in component}
    successors: dict[int, set[int]] = {i: set() for i in range(len(components))}
    indegree = [0] * len(components)
    for source, target in edges:
        i, j = index_of[source], index_of[target]
        if i != j and j not in successors[i]:
            successors[i].add(j)
            indegree[j] += 1
    ready = [i for i in range(len(components)) if indegree[i] == 0]
    order: list[int] = []
    while ready:
        i = ready.pop(0)
        order.append(i)
        for j in sorted(successors[i]):
            indegree[j] -= 1
            if indegree[j] == 0:
                ready.append(j)
    if len(order) != len(components):
        raise SFAutomatonError("condensation of an SCC decomposition is not acyclic")
    return order


def cycle_rank(
    vertices: tuple[Vertex, ...],
    edges: Edges,
    memo: dict[tuple[Vertex, ...], int] | None = None,
) -> int:
    """Cycle rank (loop complexity) of the induced subgraph on ``vertices``.

    Lombardy--Sakarovitch, *The universal automaton*, Def. 7.4:
    ``0`` for a graph without edges; the maximum over strongly connected
    components when there is more than one; and ``1 + min_v rank(G - v)``
    for a strongly connected graph that has an edge.
    """

    if memo is None:
        memo = {}
    if vertices in memo:
        return memo[vertices]

    inner = _restrict(vertices, edges)
    if not inner:
        memo[vertices] = 0
        return 0

    components = _sccs(vertices, inner)
    nontrivial = [c for c in components if any(u in c and v in c for u, v in inner)]
    if not nontrivial:
        memo[vertices] = 0
        return 0
    if len(components) > 1:
        result = max(cycle_rank(c, inner, memo) for c in nontrivial)
        memo[vertices] = result
        return result

    best = min(
        cycle_rank(tuple(v for v in vertices if v != drop), inner, memo)
        for drop in vertices
    )
    memo[vertices] = 1 + best
    return 1 + best


def _rank_witness(vertices: tuple[Vertex, ...], edges: Edges) -> Vertex:
    """A vertex whose deletion realizes ``rank(G) = 1 + rank(G - v)``."""

    memo: dict[tuple[Vertex, ...], int] = {}
    return min(
        vertices,
        key=lambda drop: (
            cycle_rank(tuple(v for v in vertices if v != drop), edges, memo),
            vertices.index(drop),
        ),
    )


# --------------------------------------------------------------------------
# State elimination along the cycle-rank decomposition.
# --------------------------------------------------------------------------


def all_pairs(
    vertices: tuple[Vertex, ...], edges: Edges
) -> dict[tuple[Vertex, Vertex], GRegex]:
    """Expressions for the path languages between every ordered pair.

    The elimination order follows the recursion that defines the cycle rank,
    so that a star is introduced only when a genuine cycle is destroyed.  The
    resulting star height is bounded by ``cycle_rank(vertices, edges)``; see
    ``notes/sf_labeled_automata.md`` §2 for the induction.
    """

    inner = _restrict(vertices, edges)
    result: dict[tuple[Vertex, Vertex], GRegex] = {
        (p, q): (EPS if p == q else EMPTY) for p in vertices for q in vertices
    }
    if not inner:
        return result

    components = _sccs(vertices, inner)
    if len(components) > 1:
        return _all_pairs_across_components(vertices, inner, components)

    anchor = _rank_witness(vertices, inner)
    rest = tuple(v for v in vertices if v != anchor)
    sub = all_pairs(rest, inner)

    returns = _first_return(anchor, rest, inner, sub)
    loop = star(returns)
    reach = {p: _to_anchor(p, anchor, rest, inner, sub) for p in vertices}
    leave = {q: _from_anchor(q, anchor, rest, inner, sub) for q in vertices}

    for p in vertices:
        for q in vertices:
            direct = sub[(p, q)] if (p != anchor and q != anchor) else EMPTY
            result[(p, q)] = union(direct, concat(reach[p], loop, leave[q]))
    return result


def _first_return(
    anchor: Vertex, rest: tuple[Vertex, ...], edges: Edges, sub: Mapping
) -> GRegex:
    """Nonempty paths ``anchor -> anchor`` with no intermediate visit to ``anchor``."""

    parts = [edges.get((anchor, anchor), EMPTY)]
    for x in rest:
        out = edges.get((anchor, x))
        if out is None:
            continue
        for y in rest:
            back = edges.get((y, anchor))
            if back is None:
                continue
            parts.append(concat(out, sub[(x, y)], back))
    return union(*parts)


def _to_anchor(
    source: Vertex, anchor: Vertex, rest: tuple[Vertex, ...], edges: Edges, sub: Mapping
) -> GRegex:
    if source == anchor:
        return EPS
    parts = []
    for x in rest:
        back = edges.get((x, anchor))
        if back is None:
            continue
        parts.append(concat(sub[(source, x)], back))
    return union(*parts)


def _from_anchor(
    target: Vertex, anchor: Vertex, rest: tuple[Vertex, ...], edges: Edges, sub: Mapping
) -> GRegex:
    if target == anchor:
        return EPS
    parts = []
    for y in rest:
        out = edges.get((anchor, y))
        if out is None:
            continue
        parts.append(concat(out, sub[(y, target)]))
    return union(*parts)


def _all_pairs_across_components(
    vertices: tuple[Vertex, ...],
    edges: Edges,
    components: Sequence[tuple[Vertex, ...]],
) -> dict[tuple[Vertex, Vertex], GRegex]:
    """Combine per-component solutions along the (acyclic) condensation.

    Crossing between components can never be repeated, so this stage adds no
    star at all and the star height stays at the maximum over components.
    """

    index_of = {v: i for i, component in enumerate(components) for v in component}
    inside = [all_pairs(component, _restrict(component, edges)) for component in components]
    crossing = [
        (source, target, label)
        for (source, target), label in edges.items()
        if index_of[source] != index_of[target]
    ]
    order = _topological_order(components, edges)

    result: dict[tuple[Vertex, Vertex], GRegex] = {}
    for goal in vertices:
        reaching: dict[Vertex, GRegex] = {}
        for component_index in reversed(order):
            component = components[component_index]
            for x in component:
                parts = []
                if index_of[goal] == component_index:
                    parts.append(inside[component_index][(x, goal)])
                for source, target, label in crossing:
                    if index_of[source] != component_index:
                        continue
                    parts.append(
                        concat(inside[component_index][(x, source)], label, reaching[target])
                    )
                reaching[x] = union(*parts)
        for x in vertices:
            result[(x, goal)] = reaching[x]
    return result


# --------------------------------------------------------------------------
# The automaton object.
# --------------------------------------------------------------------------


def _letters(expr: GRegex) -> set[str]:
    """Every letter occurring in ``expr``."""

    if expr.op == "letter":
        assert expr.value is not None
        return {expr.value}
    found: set[str] = set()
    for arg in expr.args:
        found |= _letters(arg)
    return found


@dataclass(frozen=True)
class SFAutomaton:
    """A finite automaton whose transition labels are star-free languages."""

    alphabet: tuple[str, ...]
    states: tuple[Vertex, ...]
    start: frozenset
    accept: frozenset
    edges: Mapping[tuple[Vertex, Vertex], GRegex]
    description: str = ""

    def __post_init__(self) -> None:
        known = set(self.states)
        if len(known) != len(self.states):
            raise SFAutomatonError("duplicate state")
        if not self.start <= known:
            raise SFAutomatonError("start states are not all declared")
        if not self.accept <= known:
            raise SFAutomatonError("accepting states are not all declared")
        alphabet = set(self.alphabet)
        for (source, target), label in self.edges.items():
            if source not in known or target not in known:
                raise SFAutomatonError(f"edge {(source, target)!r} leaves the state set")
            if label.star_height() != 0:
                raise SFAutomatonError(
                    f"label of edge {(source, target)!r} has star height "
                    f"{label.star_height()}, so it is not star-free"
                )
            # A label may only mention declared letters.  Without this check a
            # nominally valid automaton can emit an expression that
            # ``tools.regex_cert`` then rejects, because the certificate schema
            # validates every letter node against the declared alphabet.
            stray = sorted(_letters(label) - alphabet)
            if stray:
                raise SFAutomatonError(
                    f"label of edge {(source, target)!r} uses letters "
                    f"{stray} outside the alphabet {list(self.alphabet)}"
                )

    def loop_complexity(self) -> int:
        return cycle_rank(self.states, self.edges)

    def path_expressions(self) -> dict[tuple[Vertex, Vertex], GRegex]:
        return all_pairs(self.states, self.edges)

    def to_expression(self) -> GRegex:
        """Eliminate states; the result has star height at most the loop complexity.

        The bound is re-checked here on every call, so a regression in the
        elimination order fails loudly instead of silently producing a weaker
        certificate.
        """

        paths = self.path_expressions()
        expression = union(
            *[
                paths[(s, f)]
                for s in self.states
                if s in self.start
                for f in self.states
                if f in self.accept
            ]
        )
        rank = self.loop_complexity()
        height = expression.star_height()
        if height > rank:
            raise SFAutomatonError(
                f"state elimination produced star height {height} above the "
                f"loop complexity {rank}; the elimination order is wrong"
            )
        return expression

    def absorb_self_loop(self, state: Vertex, closure: GRegex) -> "SFAutomaton":
        """Fold the self-loop at ``state`` into its incoming edges.

        ``closure`` must be a star-free expression for ``E*``, where ``E`` is
        the current self-loop label.  Callers are responsible for supplying a
        correct ``closure``; :func:`check_closure` verifies one exactly.

        The self-loop disappears from the graph, so the cycle rank can only
        drop, while every label stays star-free.  When ``state`` is initial a
        fresh predecessor carries the closure, so runs that begin inside the
        loop are preserved.
        """

        loop = self.edges.get((state, state))
        if loop is None:
            raise SFAutomatonError(f"state {state!r} has no self-loop to absorb")
        if closure.star_height() != 0:
            raise SFAutomatonError("the closure of an absorbed self-loop must be star-free")

        edges = {
            (source, target): (concat(label, closure) if target == state else label)
            for (source, target), label in self.edges.items()
            if (source, target) != (state, state)
        }
        states = self.states
        start = self.start
        if state in self.start:
            entry = ("entry", state)
            if entry in set(states):
                raise SFAutomatonError(f"state {entry!r} already exists")
            states = states + (entry,)
            edges[(entry, state)] = closure
            start = (self.start - {state}) | {entry}
        return SFAutomaton(
            alphabet=self.alphabet,
            states=states,
            start=frozenset(start),
            accept=self.accept,
            edges=edges,
            description=self.description,
        )

    def apply_star(self, hub: Vertex = ("star", "hub")) -> "SFAutomaton":
        """Return an SF-automaton for ``L(self)*`` of rank at most ``rank + 1``.

        The construction adds **one fresh vertex**, both the unique initial and
        the unique accepting state, with `ε`-edges from it to every old initial
        vertex and from every old accepting vertex back to it.  Deleting the
        hub returns the original digraph, so
        ``r(result) <= r(self) + 1`` — using ``r(G) <= r(G - v) + 1``, which
        holds for a strongly connected ``G`` by definition and in general
        because cycle rank is monotone under subgraphs.

        The naive alternative — `ε`-edges from every accepting vertex directly
        back to every initial vertex, with no new state — does **not** satisfy
        that bound.  A rank-0 DAG with two initial and two accepting vertices
        and all four initial-to-accepting edges becomes a bidirected `K_{2,2}`
        and has rank 2; ``tests/test_sf_automaton.py`` pins that case.
        """

        if hub in set(self.states):
            raise SFAutomatonError(f"state {hub!r} already exists")
        edges = dict(self.edges)
        for source in self.start:
            edges[(hub, source)] = union(edges.get((hub, source), EMPTY), EPS)
        for target in self.accept:
            edges[(target, hub)] = union(edges.get((target, hub), EMPTY), EPS)
        return SFAutomaton(
            alphabet=self.alphabet,
            states=self.states + (hub,),
            start=frozenset({hub}),
            accept=frozenset({hub}),
            edges=edges,
            description=f"star of: {self.description}" if self.description else "",
        )

    def certificate(self, target: DFA, description: str) -> dict[str, Any]:
        """Emit a ``gsh-regex-certificate-v1`` record for ``tools.regex_cert``."""

        expression = self.to_expression()
        return {
            "schema": "gsh-regex-certificate-v1",
            "description": description,
            "alphabet": list(self.alphabet),
            "claimed_height": expression.star_height(),
            "expression": expression.to_json(),
            "target_dfa": target.to_json(),
        }


def from_dfa(machine: DFA, description: str = "") -> SFAutomaton:
    """View a DFA as an SF-automaton whose labels are unions of letters."""

    states = tuple(sorted(machine.states, key=repr))
    grouped: dict[tuple[Vertex, Vertex], list[str]] = {}
    for state in states:
        for symbol in machine.alphabet:
            grouped.setdefault((state, machine.step(state, symbol)), []).append(symbol)
    return SFAutomaton(
        alphabet=tuple(machine.alphabet),
        states=states,
        start=frozenset({machine.start}),
        accept=frozenset(machine.accept),
        edges={pair: any_of(symbols) for pair, symbols in grouped.items()},
        description=description,
    )


def first_return(machine: SFAutomaton, anchor: Vertex) -> GRegex:
    """Nonempty returns to ``anchor`` that do not visit ``anchor`` in between."""

    if anchor not in set(machine.states):
        raise SFAutomatonError(f"unknown anchor {anchor!r}")
    rest = tuple(v for v in machine.states if v != anchor)
    return _first_return(anchor, rest, machine.edges, all_pairs(rest, machine.edges))


def escapes(machine: SFAutomaton, anchor: Vertex) -> dict[Vertex, GRegex]:
    """Paths leaving ``anchor`` and stopping before returning to it."""

    if anchor not in set(machine.states):
        raise SFAutomatonError(f"unknown anchor {anchor!r}")
    rest = tuple(v for v in machine.states if v != anchor)
    sub = all_pairs(rest, machine.edges)
    return {q: _from_anchor(q, anchor, rest, machine.edges, sub) for q in rest}


def check_closure(loop: GRegex, closure: GRegex, alphabet: Sequence[str]) -> bool:
    """Exact check that ``closure`` defines the same language as ``loop*``."""

    from tools.regex_cert import compile_regex, equivalence_witness

    return (
        equivalence_witness(
            compile_regex(star(loop), alphabet).minimized(),
            compile_regex(closure, alphabet).minimized(),
        )
        is None
    )


# --------------------------------------------------------------------------
# Calibration automata.
# --------------------------------------------------------------------------

_AB = ("a", "b")
A_STAR = words_avoiding(("b",), _AB)  # a* written star-free
B_STAR = words_avoiding(("a",), _AB)  # b* written star-free

ALIASES: dict[GRegex, str] = {A_STAR: "a*", B_STAR: "b*", TOP: "T"}


def _counting_automaton(modulus: int, driver: str, filler: GRegex) -> SFAutomaton:
    """``{ w : |w|_driver = 0 mod modulus }`` as a rank-1 SF-automaton.

    One residue state per class, the filler letter absorbed into the incoming
    edges; the only cycle is the residue cycle, so the rank is 1.
    """

    states: tuple[Vertex, ...] = ("entry",) + tuple(range(modulus))
    edges = {("entry", 0): filler}
    for residue in range(modulus):
        edges[(residue, (residue + 1) % modulus)] = concat(letter(driver), filler)
    return SFAutomaton(
        alphabet=_AB,
        states=states,
        start=frozenset({"entry"}),
        accept=frozenset({0}),
        edges=edges,
        description=f"|w|_{driver} = 0 mod {modulus}, rank-1 SF-automaton",
    )


def _aa_star_automaton() -> SFAutomaton:
    return SFAutomaton(
        alphabet=_AB,
        states=(0,),
        start=frozenset({0}),
        accept=frozenset({0}),
        edges={(0, 0): concat(letter("a"), letter("a"))},
        description="(aa)* as the star of a star-free label",
    )


# The four-diagonal action of the Weis L2 syntactic group
# (notes/weis_l2_full_height_one.md §2):
#     psi(a) = (D2 D3),  psi(b) = (D0 D3 D2 D1).
WEIS_L2_DIAGONAL_ACTION: dict[str, dict[str, str]] = {
    "a": {"D0": "D0", "D1": "D1", "D2": "D3", "D3": "D2"},
    "b": {"D0": "D3", "D1": "D0", "D2": "D1", "D3": "D2"},
}

# The same walk graph after absorbing the two a-self-loops (at D0 and D1)
# into the incoming edges, using the star-free a*.  Every remaining cycle
# passes through D2, so the loop complexity is 1.
WEIS_L2_DIAGONAL_GRAPH = SFAutomaton(
    alphabet=_AB,
    states=("D0", "D1", "D2", "D3"),
    start=frozenset({"D2"}),
    accept=frozenset({"D2"}),
    edges={
        ("D0", "D3"): letter("b"),
        ("D1", "D0"): concat(letter("b"), A_STAR),
        ("D2", "D1"): concat(letter("b"), A_STAR),
        ("D2", "D3"): letter("a"),
        ("D3", "D2"): any_of(("a", "b")),
    },
    description=(
        "Weis L2, four-diagonal action, a-self-loops absorbed; "
        "anchor D2, loop complexity 1"
    ),
)


def weis_l2_diagonal_walk_dfa(source: str, target: str) -> DFA:
    """``{ w : the diagonal walk of w from `source` ends at `target` }``."""

    states = ("D0", "D1", "D2", "D3")
    transition = {
        (state, symbol): WEIS_L2_DIAGONAL_ACTION[symbol][state]
        for state in states
        for symbol in _AB
    }
    machine = DFA(_AB, frozenset(states), source, frozenset({target}), transition)
    machine.validate()
    return machine.minimized()


def weis_l2_minimal_dfa() -> DFA:
    """The six-state minimal DFA of ``L2`` (notes/weis_l2_full_height_one.md §1).

    The walk automaton of ``a = (0 1)(3 4)``, ``b = (0 2 3 5)`` on the six
    octahedron vertices, with ``start = accept = v0``.
    """

    images = {
        "a": {0: 1, 1: 0, 2: 2, 3: 4, 4: 3, 5: 5},
        "b": {0: 2, 1: 1, 2: 3, 3: 5, 4: 4, 5: 0},
    }
    states = frozenset(range(6))
    transition = {
        (state, symbol): images[symbol][state] for state in states for symbol in _AB
    }
    machine = DFA(_AB, states, 0, frozenset({0}), transition)
    machine.validate()
    return machine.minimized()


CALIBRATION: dict[str, SFAutomaton] = {
    "even_a": _counting_automaton(2, "a", B_STAR),
    "even_b": _counting_automaton(2, "b", A_STAR),
    "z3": _counting_automaton(3, "a", B_STAR),
    "aa_star": _aa_star_automaton(),
    "weis_l2_diagonals": WEIS_L2_DIAGONAL_GRAPH,
}
