"""Machine companion for the two closure lemmas behind Proposition 3.1
(notes/conway_group_identities_and_full_alphabet.md).

Lemma Q (letter quotient). For a generalized regular expression E and a
letter x, the Brzozowski derivative d_x(E) is a generalized expression with
syntactic star height <= height(E) and language x^-1 L(E).

Lemma M (literal inverse morphism). For a letter-to-letter map
h: A -> B, substituting every letter b of E (over B) by the union of the
letters in h^-1(b) yields an expression over A of the same star height
whose language is h^-1(L(E)).

This script checks BOTH claims exactly (DFA equivalence via
tools.regex_cert, not sampling of words) on a deterministic pseudo-random
family of expressions, and additionally asserts the syntactic height
inequality on every instance.  The general statements are proved by
structural induction in the note; this is the executable companion, and a
failure here would refute the induction.

Run: python3 -m scripts.closure_lemmas_check
"""

from __future__ import annotations

import random

from tools.regex_cert import DFA, GRegex, compile_regex, equivalence_witness

EMPTY = GRegex("empty")
EPS = GRegex("eps")


def letter(x: str) -> GRegex:
    return GRegex("letter", value=x)


def union(*args: GRegex) -> GRegex:
    return GRegex("union", tuple(args)) if args else EMPTY


def concat(a: GRegex, b: GRegex) -> GRegex:
    return GRegex("concat", (a, b))


def compl(a: GRegex) -> GRegex:
    return GRegex("compl", (a,))


def star(a: GRegex) -> GRegex:
    return GRegex("star", (a,))


def nullable(e: GRegex) -> bool:
    if e.op == "empty":
        return False
    if e.op == "eps":
        return True
    if e.op == "letter":
        return False
    if e.op == "union":
        return any(nullable(a) for a in e.args)
    if e.op == "concat":
        return all(nullable(a) for a in e.args)
    if e.op == "compl":
        return not nullable(e.args[0])
    if e.op == "star":
        return True
    raise AssertionError(e.op)


def derivative(e: GRegex, x: str) -> GRegex:
    """Brzozowski derivative; every clause stays within height(e)."""
    if e.op in {"empty", "eps"}:
        return EMPTY
    if e.op == "letter":
        return EPS if e.value == x else EMPTY
    if e.op == "union":
        return union(*(derivative(a, x) for a in e.args))
    if e.op == "concat":
        a, b = e.args
        first = concat(derivative(a, x), b)
        if nullable(a):
            return union(first, derivative(b, x))
        return first
    if e.op == "compl":
        return compl(derivative(e.args[0], x))
    if e.op == "star":
        return concat(derivative(e.args[0], x), e)
    raise AssertionError(e.op)


def substitute(e: GRegex, preimages: dict[str, tuple[str, ...]]) -> GRegex:
    """Letter substitution implementing h^-1 for letter-to-letter h."""
    if e.op in {"empty", "eps"}:
        return e
    if e.op == "letter":
        return union(*(letter(a) for a in preimages.get(e.value, ())))
    if e.op in {"union", "concat"}:
        return GRegex(e.op, tuple(substitute(a, preimages) for a in e.args))
    if e.op in {"compl", "star"}:
        return GRegex(e.op, (substitute(e.args[0], preimages),))
    raise AssertionError(e.op)


def quotient_dfa(dfa: DFA, x: str) -> DFA:
    """DFA for x^-1 L(dfa): move the start state along x."""
    return DFA(
        alphabet=dfa.alphabet,
        states=dfa.states,
        start=dfa.transition[(dfa.start, x)],
        accept=dfa.accept,
        transition=dfa.transition,
    )


def inverse_morphism_dfa(dfa: DFA, h: dict[str, str], domain: tuple[str, ...]) -> DFA:
    """DFA for h^-1(L(dfa)) over the domain alphabet."""
    transition = {
        (state, a): dfa.transition[(state, h[a])]
        for state in dfa.states
        for a in domain
    }
    return DFA(
        alphabet=domain,
        states=dfa.states,
        start=dfa.start,
        accept=dfa.accept,
        transition=transition,
    )


def random_expr(rng: random.Random, alphabet: tuple[str, ...], depth: int) -> GRegex:
    if depth == 0:
        return rng.choice([EMPTY, EPS] + [letter(a) for a in alphabet])
    op = rng.choice(["union", "concat", "compl", "star", "leaf"])
    if op == "leaf":
        return random_expr(rng, alphabet, 0)
    if op in {"union", "concat"}:
        left = random_expr(rng, alphabet, depth - 1)
        right = random_expr(rng, alphabet, depth - 1)
        return GRegex(op, (left, right))
    return GRegex(op, (random_expr(rng, alphabet, depth - 1),))


def main() -> None:
    rng = random.Random(20260723)
    target = ("u", "v", "w")  # codomain alphabet B
    domain = ("a", "b", "c", "d")  # domain alphabet A
    trials = 400
    for trial in range(trials):
        expr = random_expr(rng, target, rng.randint(1, 4))
        dfa = compile_regex(expr, target)

        x = rng.choice(target)
        dexpr = derivative(expr, x)
        assert dexpr.star_height() <= expr.star_height(), (
            f"height increased by derivative at trial {trial}"
        )
        witness = equivalence_witness(compile_regex(dexpr, target), quotient_dfa(dfa, x))
        assert witness is None, f"derivative wrong at trial {trial}: {witness}"

        h = {a: rng.choice(target) for a in domain}
        preimages: dict[str, tuple[str, ...]] = {b: () for b in target}
        for a, b in h.items():
            preimages[b] = preimages[b] + (a,)
        sexpr = substitute(expr, preimages)
        assert sexpr.star_height() <= expr.star_height(), (
            f"height increased by substitution at trial {trial}"
        )
        witness = equivalence_witness(
            compile_regex(sexpr, domain), inverse_morphism_dfa(dfa, h, domain)
        )
        assert witness is None, f"substitution wrong at trial {trial}: {witness}"

    print(f"ALL CHECKS PASSED ({trials} expressions; exact DFA equivalence per case)")


if __name__ == "__main__":
    main()
