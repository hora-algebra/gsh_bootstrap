"""Exact checker for generalized-regular-expression certificates.

The checker parses a finite generalized regular expression, computes its
syntactic star height, compiles it to a complete DFA using standard automata
constructions, minimizes the result, and checks language equivalence with a
supplied target DFA.

This checker is intended as a compact independently auditable boundary between
untrusted expression generation and mathematical claims.  It is not a Lean
proof.  The long-term formalization target is a Lean soundness theorem for an
equivalent certificate format.

Two schemas
-----------

``gsh-regex-certificate-v1`` carries the expression as a nested JSON tree.
``gsh-regex-certificate-v2`` carries it as a **shared DAG**: a table of nodes
addressed by id, where an operand is an id rather than an inlined subtree.  The
two denote expressions in exactly the same way; v2 exists because sharing is
sometimes the difference between a file that can be written and one that cannot.
The assembled height-one expression for the identity fibre of ``C_7 : C_3`` has
277,408 DAG nodes and about ``10^111`` tree nodes, so v1 cannot represent it at
any scale.

Why the DAG reading is sound
----------------------------

Let ``D`` be a node table with root ``r``, in which every node is reachable
from ``r`` and the reference graph is acyclic.  Write ``unfold(D, r)`` for the
tree obtained by repeatedly replacing each reference with a copy of the subtree
it names.

1. ``unfold(D, r)`` is well defined and finite.  Acyclicity gives a topological
   order on a finite node set, so the replacement terminates; it is finite
   because each node has finitely many children.  (It can be astronomically
   large, which is the point, but it is finite.)
2. ``star_height`` of a node depends only on its operator and on the star
   heights of its children -- never on the path by which the node was reached.
   So the memoized value computed once per node equals the value the tree
   computation would produce at every copy of that node, and by induction along
   the topological order, ``dag_star_height(D, r) = star_height(unfold(D, r))``.
3. The denoted language of a node depends only on its operator and on the
   languages of its children, by the same argument.  The automaton
   constructions below are pure functions of their input automata, so the
   memoized compilation of a node equals the compilation of every copy of it in
   the unfolding, and ``compile_regex_dag(D, r)`` accepts exactly
   ``L(unfold(D, r))``.

Both properties fail without acyclicity -- a cyclic table denotes no finite
expression at all -- so the cycle check is not a hygiene rule but the hypothesis
of the argument, and it is enforced before anything is evaluated.  Reachability
is required for a weaker reason: an unreachable node cannot change the verdict,
but it can hide arbitrary unchecked content inside a certificate, so the parser
refuses it rather than ignoring it.

Both passes are iterative.  A recursive implementation would be sound and would
also overflow the interpreter stack on any certificate large enough to need v2.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Hashable, Iterable, Mapping, Sequence
import json


class CertificateError(ValueError):
    """Raised when a certificate is malformed or false."""


@dataclass(frozen=True, slots=True)
class GRegex:
    """Generalized regular-expression abstract syntax tree."""

    op: str
    args: tuple["GRegex", ...] = ()
    value: str | None = None

    def star_height(self) -> int:
        if self.op in {"empty", "eps", "letter"}:
            return 0
        if self.op in {"union", "concat"}:
            return max((arg.star_height() for arg in self.args), default=0)
        if self.op == "compl":
            return self.args[0].star_height()
        if self.op == "star":
            return 1 + self.args[0].star_height()
        raise AssertionError(f"unknown op after validation: {self.op}")

    def to_json(self) -> dict[str, Any]:
        if self.op == "letter":
            return {"op": "letter", "value": self.value}
        if self.op in {"empty", "eps"}:
            return {"op": self.op}
        if self.op in {"compl", "star"}:
            return {"op": self.op, "arg": self.args[0].to_json()}
        return {"op": self.op, "args": [arg.to_json() for arg in self.args]}


def parse_regex(data: Any, alphabet: Sequence[str], *, path: str = "expression") -> GRegex:
    """Parse and validate a JSON expression."""

    if not isinstance(data, Mapping):
        raise CertificateError(f"{path}: expected an object")
    op = data.get("op")
    if not isinstance(op, str):
        raise CertificateError(f"{path}.op: expected a string")

    if op in {"empty", "eps"}:
        return GRegex(op)
    if op == "letter":
        value = data.get("value")
        if not isinstance(value, str):
            raise CertificateError(f"{path}.value: expected a string")
        if value not in alphabet:
            raise CertificateError(f"{path}: letter {value!r} is not in the alphabet")
        return GRegex(op, value=value)
    if op in {"compl", "star"}:
        if "arg" not in data:
            raise CertificateError(f"{path}.arg: missing")
        return GRegex(op, (parse_regex(data["arg"], alphabet, path=f"{path}.arg"),))
    if op in {"union", "concat"}:
        raw_args = data.get("args")
        if not isinstance(raw_args, list):
            raise CertificateError(f"{path}.args: expected a list")
        return GRegex(
            op,
            tuple(
                parse_regex(arg, alphabet, path=f"{path}.args[{index}]")
                for index, arg in enumerate(raw_args)
            ),
        )
    raise CertificateError(f"{path}.op: unsupported operation {op!r}")


@dataclass(frozen=True, slots=True)
class DagNode:
    """One node of a shared expression DAG; children are node ids."""

    op: str
    children: tuple[str, ...] = ()
    value: str | None = None


@dataclass(frozen=True)
class ExpressionDag:
    """A rooted, acyclic, fully reachable expression DAG.

    ``order`` lists every node id with all children before their parents, so a
    single left-to-right pass evaluates any structurally determined attribute.
    """

    nodes: Mapping[str, DagNode]
    root: str
    order: tuple[str, ...]


def parse_regex_dag(data: Any, alphabet: Sequence[str]) -> ExpressionDag:
    """Parse and validate a shared expression DAG.

    Rejects, in this order: a malformed table, an unknown operator, a letter
    outside the alphabet, a dangling reference, a node unreachable from the
    root, and a reference cycle.
    """

    if not isinstance(data, Mapping):
        raise CertificateError("expression_dag: expected an object")
    root = data.get("root")
    if not isinstance(root, str):
        raise CertificateError("expression_dag.root: expected a string")
    raw_nodes = data.get("nodes")
    if not isinstance(raw_nodes, Mapping):
        raise CertificateError("expression_dag.nodes: expected an object")
    if root not in raw_nodes:
        raise CertificateError(f"expression_dag.root: {root!r} is not a node")

    nodes: dict[str, DagNode] = {}
    for node_id, raw in raw_nodes.items():
        where = f"expression_dag.nodes[{node_id!r}]"
        if not isinstance(raw, Mapping):
            raise CertificateError(f"{where}: expected an object")
        op = raw.get("op")
        if not isinstance(op, str):
            raise CertificateError(f"{where}.op: expected a string")
        if op in {"empty", "eps"}:
            nodes[node_id] = DagNode(op)
        elif op == "letter":
            value = raw.get("value")
            if not isinstance(value, str):
                raise CertificateError(f"{where}.value: expected a string")
            if value not in alphabet:
                raise CertificateError(f"{where}: letter {value!r} is not in the alphabet")
            nodes[node_id] = DagNode(op, value=value)
        elif op in {"compl", "star"}:
            arg = raw.get("arg")
            if not isinstance(arg, str):
                raise CertificateError(f"{where}.arg: expected a node id")
            nodes[node_id] = DagNode(op, (arg,))
        elif op in {"union", "concat"}:
            args = raw.get("args")
            if not isinstance(args, list) or not all(isinstance(x, str) for x in args):
                raise CertificateError(f"{where}.args: expected a list of node ids")
            nodes[node_id] = DagNode(op, tuple(args))
        else:
            raise CertificateError(f"{where}.op: unsupported operation {op!r}")

    for node_id, node in nodes.items():
        for child in node.children:
            if child not in nodes:
                raise CertificateError(
                    f"expression_dag.nodes[{node_id!r}]: dangling reference {child!r}"
                )

    reachable: set[str] = set()
    stack = [root]
    while stack:
        node_id = stack.pop()
        if node_id in reachable:
            continue
        reachable.add(node_id)
        stack.extend(nodes[node_id].children)
    unreachable = set(nodes) - reachable
    if unreachable:
        raise CertificateError(
            "expression_dag.nodes: "
            f"{len(unreachable)} node(s) unreachable from the root, first {sorted(unreachable)[0]!r}"
        )

    # Kahn's algorithm over the reversed edges, so children come out first.
    pending = {node_id: len(set(nodes[node_id].children)) for node_id in nodes}
    parents: dict[str, list[str]] = {node_id: [] for node_id in nodes}
    for node_id, node in nodes.items():
        for child in set(node.children):
            parents[child].append(node_id)
    ready = deque(sorted(node_id for node_id, n in pending.items() if n == 0))
    order: list[str] = []
    while ready:
        node_id = ready.popleft()
        order.append(node_id)
        for parent in parents[node_id]:
            pending[parent] -= 1
            if pending[parent] == 0:
                ready.append(parent)
    if len(order) != len(nodes):
        stuck = sorted(node_id for node_id, n in pending.items() if n > 0)
        raise CertificateError(
            f"expression_dag.nodes: reference cycle through {len(stuck)} node(s), "
            f"first {stuck[0]!r}"
        )
    return ExpressionDag(nodes, root, tuple(order))


def dag_star_height(dag: ExpressionDag) -> int:
    """Syntactic star height of the tree the DAG unfolds to."""

    height: dict[str, int] = {}
    for node_id in dag.order:
        node = dag.nodes[node_id]
        kids = [height[child] for child in node.children]
        if node.op in {"empty", "eps", "letter"}:
            height[node_id] = 0
        elif node.op in {"union", "concat"}:
            height[node_id] = max(kids, default=0)
        elif node.op == "compl":
            height[node_id] = kids[0]
        elif node.op == "star":
            height[node_id] = 1 + kids[0]
        else:
            raise AssertionError(f"unknown op after validation: {node.op}")
    return height[dag.root]


@dataclass(frozen=True)
class DFA:
    """A complete deterministic finite automaton."""

    alphabet: tuple[str, ...]
    states: frozenset[Hashable]
    start: Hashable
    accept: frozenset[Hashable]
    transition: Mapping[tuple[Hashable, str], Hashable]

    def validate(self) -> None:
        if self.start not in self.states:
            raise CertificateError("DFA start state is not in the state set")
        if not self.accept <= self.states:
            raise CertificateError("DFA accepting states are not all declared")
        for state in self.states:
            for symbol in self.alphabet:
                key = (state, symbol)
                if key not in self.transition:
                    raise CertificateError(
                        f"DFA transition missing for state {state!r}, symbol {symbol!r}"
                    )
                target = self.transition[key]
                if target not in self.states:
                    raise CertificateError(
                        f"DFA transition target {target!r} is not a declared state"
                    )

    def step(self, state: Hashable, symbol: str) -> Hashable:
        return self.transition[(state, symbol)]

    def run(self, word: Iterable[str]) -> Hashable:
        state = self.start
        for symbol in word:
            if symbol not in self.alphabet:
                raise CertificateError(f"word symbol {symbol!r} is not in alphabet")
            state = self.step(state, symbol)
        return state

    def accepts(self, word: Iterable[str]) -> bool:
        return self.run(word) in self.accept

    def reachable(self) -> "DFA":
        queue: deque[Hashable] = deque([self.start])
        seen: set[Hashable] = {self.start}
        while queue:
            state = queue.popleft()
            for symbol in self.alphabet:
                nxt = self.step(state, symbol)
                if nxt not in seen:
                    seen.add(nxt)
                    queue.append(nxt)
        transition = {
            (state, symbol): self.step(state, symbol)
            for state in seen
            for symbol in self.alphabet
        }
        return DFA(
            self.alphabet,
            frozenset(seen),
            self.start,
            frozenset(self.accept & seen),
            transition,
        )

    def canonical(self) -> "DFA":
        """Renumber reachable states in breadth-first alphabet order."""

        source = self.reachable()
        order: dict[Hashable, int] = {source.start: 0}
        queue: deque[Hashable] = deque([source.start])
        while queue:
            state = queue.popleft()
            for symbol in source.alphabet:
                nxt = source.step(state, symbol)
                if nxt not in order:
                    order[nxt] = len(order)
                    queue.append(nxt)
        transition = {
            (order[state], symbol): order[source.step(state, symbol)]
            for state in order
            for symbol in source.alphabet
        }
        return DFA(
            source.alphabet,
            frozenset(order.values()),
            0,
            frozenset(order[state] for state in source.accept),
            transition,
        )

    def minimized(self) -> "DFA":
        """Minimize by stable partition refinement, then canonicalize."""

        source = self.reachable()
        accepting = set(source.accept)
        rejecting = set(source.states) - accepting
        blocks: list[set[Hashable]] = [block for block in (accepting, rejecting) if block]

        while True:
            block_index = {
                state: index for index, block in enumerate(blocks) for state in block
            }
            refined: list[set[Hashable]] = []
            changed = False
            for block in blocks:
                buckets: dict[tuple[int, ...], set[Hashable]] = {}
                for state in block:
                    signature = tuple(
                        block_index[source.step(state, symbol)]
                        for symbol in source.alphabet
                    )
                    buckets.setdefault(signature, set()).add(state)
                refined.extend(buckets.values())
                changed = changed or len(buckets) > 1
            blocks = refined
            if not changed:
                break

        block_index = {
            state: index for index, block in enumerate(blocks) for state in block
        }
        transition: dict[tuple[int, str], int] = {}
        for index, block in enumerate(blocks):
            representative = next(iter(block))
            for symbol in source.alphabet:
                transition[(index, symbol)] = block_index[source.step(representative, symbol)]
        quotient = DFA(
            source.alphabet,
            frozenset(range(len(blocks))),
            block_index[source.start],
            frozenset(block_index[state] for state in source.accept),
            transition,
        )
        return quotient.canonical()

    def complemented(self) -> "DFA":
        return DFA(
            self.alphabet,
            self.states,
            self.start,
            frozenset(self.states - self.accept),
            dict(self.transition),
        )

    def to_json(self) -> dict[str, Any]:
        machine = self.canonical()
        return {
            "states": [str(state) for state in sorted(machine.states)],
            "start": str(machine.start),
            "accept": [str(state) for state in sorted(machine.accept)],
            "transitions": {
                str(state): {
                    symbol: str(machine.step(state, symbol)) for symbol in machine.alphabet
                }
                for state in sorted(machine.states)
            },
        }


@dataclass(frozen=True)
class NFA:
    alphabet: tuple[str, ...]
    states: frozenset[Hashable]
    start: Hashable
    accept: frozenset[Hashable]
    transition: Mapping[tuple[Hashable, str], frozenset[Hashable]]
    epsilon: Mapping[Hashable, frozenset[Hashable]]

    def epsilon_closure(self, initial: Iterable[Hashable]) -> frozenset[Hashable]:
        stack = list(initial)
        closure = set(stack)
        while stack:
            state = stack.pop()
            for nxt in self.epsilon.get(state, frozenset()):
                if nxt not in closure:
                    closure.add(nxt)
                    stack.append(nxt)
        return frozenset(closure)

    def determinize(self) -> DFA:
        start = self.epsilon_closure([self.start])
        queue: deque[frozenset[Hashable]] = deque([start])
        seen: set[frozenset[Hashable]] = {start}
        transition: dict[tuple[frozenset[Hashable], str], frozenset[Hashable]] = {}
        while queue:
            state_set = queue.popleft()
            for symbol in self.alphabet:
                moved: set[Hashable] = set()
                for state in state_set:
                    moved.update(self.transition.get((state, symbol), frozenset()))
                target = self.epsilon_closure(moved)
                transition[(state_set, symbol)] = target
                if target not in seen:
                    seen.add(target)
                    queue.append(target)
        dfa = DFA(
            self.alphabet,
            frozenset(seen),
            start,
            frozenset(state for state in seen if state & self.accept),
            transition,
        )
        dfa.validate()
        return dfa.canonical()


def _atomic_empty(alphabet: tuple[str, ...]) -> DFA:
    transition = {(0, symbol): 0 for symbol in alphabet}
    return DFA(alphabet, frozenset({0}), 0, frozenset(), transition)


def _atomic_eps(alphabet: tuple[str, ...]) -> DFA:
    transition: dict[tuple[int, str], int] = {}
    for symbol in alphabet:
        transition[(0, symbol)] = 1
        transition[(1, symbol)] = 1
    return DFA(alphabet, frozenset({0, 1}), 0, frozenset({0}), transition).minimized()


def _atomic_letter(alphabet: tuple[str, ...], letter: str) -> DFA:
    transition: dict[tuple[int, str], int] = {}
    for symbol in alphabet:
        transition[(0, symbol)] = 1 if symbol == letter else 2
        transition[(1, symbol)] = 2
        transition[(2, symbol)] = 2
    return DFA(
        alphabet,
        frozenset({0, 1, 2}),
        0,
        frozenset({1}),
        transition,
    ).minimized()


def _product(
    left: DFA,
    right: DFA,
    accept_predicate: Callable[[bool, bool], bool],
) -> DFA:
    if left.alphabet != right.alphabet:
        raise CertificateError("cannot combine DFAs over different alphabets")
    alphabet = left.alphabet
    start = (left.start, right.start)
    queue: deque[tuple[Hashable, Hashable]] = deque([start])
    seen = {start}
    transition: dict[tuple[tuple[Hashable, Hashable], str], tuple[Hashable, Hashable]] = {}
    while queue:
        state = queue.popleft()
        for symbol in alphabet:
            nxt = (left.step(state[0], symbol), right.step(state[1], symbol))
            transition[(state, symbol)] = nxt
            if nxt not in seen:
                seen.add(nxt)
                queue.append(nxt)
    accept = frozenset(
        state
        for state in seen
        if accept_predicate(state[0] in left.accept, state[1] in right.accept)
    )
    return DFA(alphabet, frozenset(seen), start, accept, transition).minimized()


def _tagged_nfa_from_dfa(dfa: DFA, tag: Hashable) -> NFA:
    states = frozenset((tag, state) for state in dfa.states)
    transition = {
        ((tag, state), symbol): frozenset({(tag, dfa.step(state, symbol))})
        for state in dfa.states
        for symbol in dfa.alphabet
    }
    return NFA(
        dfa.alphabet,
        states,
        (tag, dfa.start),
        frozenset((tag, state) for state in dfa.accept),
        transition,
        {},
    )


def _concat(left: DFA, right: DFA) -> DFA:
    if left.alphabet != right.alphabet:
        raise CertificateError("cannot concatenate DFAs over different alphabets")
    l_nfa = _tagged_nfa_from_dfa(left, "L")
    r_nfa = _tagged_nfa_from_dfa(right, "R")
    epsilon: dict[Hashable, frozenset[Hashable]] = {}
    for state in l_nfa.accept:
        epsilon[state] = frozenset({r_nfa.start})
    nfa = NFA(
        left.alphabet,
        l_nfa.states | r_nfa.states,
        l_nfa.start,
        r_nfa.accept,
        dict(l_nfa.transition) | dict(r_nfa.transition),
        epsilon,
    )
    return nfa.determinize().minimized()


def _star(machine: DFA) -> DFA:
    core = _tagged_nfa_from_dfa(machine, "C")
    start: Hashable = ("S", 0)
    final: Hashable = ("F", 0)
    states = core.states | frozenset({start, final})
    epsilon: dict[Hashable, frozenset[Hashable]] = {
        start: frozenset({core.start, final})
    }
    for state in core.accept:
        epsilon[state] = frozenset({core.start, final})
    nfa = NFA(
        machine.alphabet,
        states,
        start,
        frozenset({final}),
        dict(core.transition),
        epsilon,
    )
    return nfa.determinize().minimized()


def compile_regex(expr: GRegex, alphabet: Sequence[str]) -> DFA:
    """Compile a validated generalized expression to a minimal complete DFA."""

    alpha = tuple(alphabet)
    if expr.op == "empty":
        return _atomic_empty(alpha)
    if expr.op == "eps":
        return _atomic_eps(alpha)
    if expr.op == "letter":
        assert expr.value is not None
        return _atomic_letter(alpha, expr.value)
    if expr.op == "compl":
        return compile_regex(expr.args[0], alpha).complemented().minimized()
    if expr.op == "star":
        return _star(compile_regex(expr.args[0], alpha))
    if expr.op == "union":
        result = _atomic_empty(alpha)
        for arg in expr.args:
            result = _product(result, compile_regex(arg, alpha), lambda x, y: x or y)
        return result.minimized()
    if expr.op == "concat":
        result = _atomic_eps(alpha)
        for arg in expr.args:
            result = _concat(result, compile_regex(arg, alpha))
        return result.minimized()
    raise AssertionError(f"unknown op after validation: {expr.op}")


def compile_regex_dag(dag: ExpressionDag, alphabet: Sequence[str]) -> DFA:
    """Compile a shared expression DAG to a minimal complete DFA.

    Each node is compiled once.  A node's automaton is released as soon as its
    last parent has consumed it, which is what keeps a certificate with
    hundreds of thousands of nodes inside a usable amount of memory; the root is
    exempt because it is the answer.
    """

    alpha = tuple(alphabet)
    remaining: dict[str, int] = {node_id: 0 for node_id in dag.nodes}
    for node in dag.nodes.values():
        for child in node.children:
            remaining[child] += 1

    built: dict[str, DFA] = {}

    def consume(node_id: str) -> DFA:
        machine = built[node_id]
        remaining[node_id] -= 1
        if remaining[node_id] == 0 and node_id != dag.root:
            del built[node_id]
        return machine

    for node_id in dag.order:
        node = dag.nodes[node_id]
        if node.op == "empty":
            built[node_id] = _atomic_empty(alpha)
        elif node.op == "eps":
            built[node_id] = _atomic_eps(alpha)
        elif node.op == "letter":
            assert node.value is not None
            built[node_id] = _atomic_letter(alpha, node.value)
        elif node.op == "compl":
            built[node_id] = consume(node.children[0]).complemented().minimized()
        elif node.op == "star":
            built[node_id] = _star(consume(node.children[0]))
        elif node.op == "union":
            result = _atomic_empty(alpha)
            for child in node.children:
                result = _product(result, consume(child), lambda x, y: x or y)
            built[node_id] = result.minimized()
        elif node.op == "concat":
            result = _atomic_eps(alpha)
            for child in node.children:
                result = _concat(result, consume(child))
            built[node_id] = result.minimized()
        else:
            raise AssertionError(f"unknown op after validation: {node.op}")
    return built[dag.root]


def parse_target_dfa(data: Any, alphabet: Sequence[str]) -> DFA:
    if not isinstance(data, Mapping):
        raise CertificateError("target_dfa: expected an object")
    raw_states = data.get("states")
    if not isinstance(raw_states, list) or not all(isinstance(x, str) for x in raw_states):
        raise CertificateError("target_dfa.states: expected a list of strings")
    if len(raw_states) != len(set(raw_states)):
        raise CertificateError("target_dfa.states: duplicate state")
    states = frozenset(raw_states)
    start = data.get("start")
    if not isinstance(start, str):
        raise CertificateError("target_dfa.start: expected a string")
    raw_accept = data.get("accept")
    if not isinstance(raw_accept, list) or not all(isinstance(x, str) for x in raw_accept):
        raise CertificateError("target_dfa.accept: expected a list of strings")
    transitions = data.get("transitions")
    if not isinstance(transitions, Mapping):
        raise CertificateError("target_dfa.transitions: expected an object")
    transition: dict[tuple[str, str], str] = {}
    for state in states:
        row = transitions.get(state)
        if not isinstance(row, Mapping):
            raise CertificateError(f"target_dfa.transitions[{state!r}]: missing row")
        unknown = set(row) - set(alphabet)
        if unknown:
            raise CertificateError(
                f"target_dfa.transitions[{state!r}]: unknown symbols {sorted(unknown)!r}"
            )
        for symbol in alphabet:
            target = row.get(symbol)
            if not isinstance(target, str):
                raise CertificateError(
                    f"target_dfa.transitions[{state!r}][{symbol!r}]: expected string"
                )
            transition[(state, symbol)] = target
    machine = DFA(
        tuple(alphabet),
        states,
        start,
        frozenset(raw_accept),
        transition,
    )
    machine.validate()
    return machine.minimized()


def equivalence_witness(left: DFA, right: DFA) -> list[str] | None:
    """Return a shortest distinguishing word, or ``None`` if equivalent."""

    if left.alphabet != right.alphabet:
        raise CertificateError("equivalence check requires identical alphabets")
    start = (left.start, right.start)
    queue: deque[tuple[Hashable, Hashable]] = deque([start])
    parent: dict[
        tuple[Hashable, Hashable],
        tuple[tuple[Hashable, Hashable], str] | None,
    ] = {start: None}
    while queue:
        pair = queue.popleft()
        if (pair[0] in left.accept) != (pair[1] in right.accept):
            word: list[str] = []
            cursor = pair
            while parent[cursor] is not None:
                previous, symbol = parent[cursor]  # type: ignore[misc]
                word.append(symbol)
                cursor = previous
            word.reverse()
            return word
        for symbol in left.alphabet:
            nxt = (left.step(pair[0], symbol), right.step(pair[1], symbol))
            if nxt not in parent:
                parent[nxt] = (pair, symbol)
                queue.append(nxt)
    return None


SCHEMA_TREE = "gsh-regex-certificate-v1"
SCHEMA_DAG = "gsh-regex-certificate-v2"


@dataclass(frozen=True)
class CheckReport:
    ok: bool
    actual_height: int
    claimed_height: int
    expression_states: int
    target_states: int
    witness: tuple[str, ...] | None = None
    #: Number of DAG nodes, for a v2 certificate; ``None`` for a v1 tree.
    expression_nodes: int | None = None

    def to_json(self) -> dict[str, Any]:
        return {
            "ok": self.ok,
            "actual_height": self.actual_height,
            "claimed_height": self.claimed_height,
            "expression_states": self.expression_states,
            "target_states": self.target_states,
            "witness": list(self.witness) if self.witness is not None else None,
            "expression_nodes": self.expression_nodes,
        }


def check_certificate(data: Any) -> CheckReport:
    if not isinstance(data, Mapping):
        raise CertificateError("certificate: expected an object")
    schema = data.get("schema")
    if schema not in {SCHEMA_TREE, SCHEMA_DAG}:
        raise CertificateError(
            f"certificate.schema must be {SCHEMA_TREE!r} (tree) or {SCHEMA_DAG!r} (shared DAG)"
        )
    alphabet = data.get("alphabet")
    if not isinstance(alphabet, list) or not all(isinstance(x, str) for x in alphabet):
        raise CertificateError("certificate.alphabet: expected a list of strings")
    if len(alphabet) != len(set(alphabet)):
        raise CertificateError("certificate.alphabet: duplicate symbol")
    claimed_height = data.get("claimed_height")
    if not isinstance(claimed_height, int) or isinstance(claimed_height, bool) or claimed_height < 0:
        raise CertificateError("certificate.claimed_height: expected a nonnegative integer")

    # The height is checked before compiling, so a certificate that overstates
    # its own height is rejected without paying for its automaton.
    if schema == SCHEMA_TREE:
        if "expression" not in data:
            raise CertificateError("certificate.expression: missing")
        expr = parse_regex(data["expression"], alphabet)
        actual_height = expr.star_height()
        node_count = None
    else:
        if "expression_dag" not in data:
            raise CertificateError("certificate.expression_dag: missing")
        dag = parse_regex_dag(data["expression_dag"], alphabet)
        actual_height = dag_star_height(dag)
        node_count = len(dag.nodes)
    if actual_height > claimed_height:
        raise CertificateError(
            f"expression has star height {actual_height}, exceeding claim {claimed_height}"
        )

    if "target_dfa" not in data:
        raise CertificateError("certificate.target_dfa: missing")
    target = parse_target_dfa(data["target_dfa"], alphabet)
    if schema == SCHEMA_TREE:
        compiled = compile_regex(expr, alphabet).minimized()
    else:
        compiled = compile_regex_dag(dag, alphabet).minimized()
    witness = equivalence_witness(compiled, target)
    return CheckReport(
        ok=witness is None,
        actual_height=actual_height,
        claimed_height=claimed_height,
        expression_states=len(compiled.states),
        target_states=len(target.states),
        witness=tuple(witness) if witness is not None else None,
        expression_nodes=node_count,
    )


def load_and_check(path: str | Path) -> CheckReport:
    certificate_path = Path(path)
    try:
        data = json.loads(certificate_path.read_text(encoding="utf-8"))
    except OSError as error:
        raise CertificateError(f"cannot read {certificate_path}: {error}") from error
    except json.JSONDecodeError as error:
        raise CertificateError(f"invalid JSON in {certificate_path}: {error}") from error
    return check_certificate(data)
