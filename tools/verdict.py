"""Machine-readable verdicts: the status label, derived from what ran.

Why this module exists
----------------------

`CLAIMS_LEDGER.md` distinguishes `COMPUTED` (the claim was reduced to a finite
object and that object was traversed exhaustively) from `EMPIRICAL` (a finite
sample, which can refute but never establish).  Until now both the label and the
evidence sentence were prose typed by whoever wrote the row, and
`scripts/lint_claims.py` was a regular expression over that prose.  The gate
therefore inspected the *description* of a computation and never the
computation.  Three failures followed, each one defeating the previous patch:

1. 2026-07-22 - `A4-FULL-01` was labelled `COMPUTED` while its last step was
   agreement on words of length <= 4 plus random words.  Fix: a sampling-marker
   regex.
2. 2026-07-25 - `A4-STD-01` attested exhaustiveness of its *atoms* while the
   end-to-end claim rested on length-16 agreement, and `C7C3-FULL-01` wrote "no
   sampling in the exhaustive parts", a tautology.  Fix: two more regexes.
3. 2026-07-25 - `THOMAS-D2-02` was upgraded to `COMPUTED` by a state machine
   that traversed a finite object exhaustively, carried a negative control that
   fired, and contained no sampling of any kind.  Its state was `(parse, d)`.
   None of `|w|_a`, `|w|_b`, `#tok`, `#ab` -- the quantities the identity is
   *about* -- appeared anywhere in it.  `d` was defined to be `-1` exactly when
   `parse == 1`, and the acceptance test asked whether `d == -1` when
   `parse == 1`.  The traversal was complete and the object was the wrong one.

The third failure is the one that settles the design.  It passed every prose
gate because every sentence in its evidence cell was true.  No vocabulary check
can catch it, because the defect is not in the words: the author solved the
arithmetic by hand and coded only the *conclusion*, so the program confirmed the
author's algebra rather than the claim.  A `COMPUTED` label meant "an agent
reasoned correctly, probably".

So the label is no longer typed.  It is computed here, from the shape of what
actually ran, under three rules:

* **Scope is structural.**  A caller does not describe a procedure; it calls
  `exhaustive()` or `sampled()`, and the constructor fixes the ceiling.  There
  is no sentence to write and therefore none to get wrong.
* **The default is weak.**  A claim with no verdict caps at `UNREVIEWED`.
  Silence is never evidence.
* **A check must be brittle.**  Passing is not enough: the claim's own constants
  must be perturbable, and every perturbation must be rejected.  A procedure
  that accepts the claim and also accepts a false variant of it has not tested
  the claim.  This is what `THOMAS-D2-02` lacked -- its control perturbed the
  acceptance constant, not the identity -- and it is why `decide_linear_identity`
  below writes the transition function itself instead of taking one.
"""

from __future__ import annotations

from collections import deque
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Hashable, Iterable, Mapping, Sequence
import json

ROOT = Path(__file__).resolve().parents[1]
VERDICT_DIR = ROOT / "data" / "verdicts"
SCHEMA = "gsh-verdict-v1"

#: Ceilings, weakest first.  A run's ceiling for a claim is the weakest ceiling
#: among its load-bearing checks; a claim with no check at all is `UNREVIEWED`.
ORDER = ("UNREVIEWED", "EMPIRICAL", "COMPUTED")


class VerdictError(ValueError):
    """Raised when a check is built in a way that could not test its claim."""


@dataclass(frozen=True, slots=True)
class Control:
    """A deliberately false variant of the claim that the procedure must reject.

    `mutation` names the change in the claim's own vocabulary -- "the |w|_b
    coefficient 2 -> 1", not "tail_penalty=0".  The distinction is the whole
    point: a control that perturbs the checker tells you the checker is not a
    constant function, which is not a fact about the claim.
    """

    name: str
    mutation: str
    rejected: bool

    def to_json(self) -> dict[str, Any]:
        return {"name": self.name, "mutation": self.mutation, "rejected": self.rejected}


@dataclass(frozen=True, slots=True)
class Check:
    """One verified step, with the ceiling it can support."""

    name: str
    claim_ids: tuple[str, ...]
    scope: str  # "exhaustive" | "sampled"
    passed: bool
    detail: str
    universe: int | None = None
    sample: str | None = None
    controls: tuple[Control, ...] = ()
    load_bearing: bool = True
    #: `"step"` (the default) means this check verifies a *component* of the
    #: claim; `"claim"` means it decides the claim end to end.  Only a `"claim"`
    #: check can raise a ceiling.  This is the `A4-STD-01` sub-step loophole
    #: made structural: that row attested an exhaustive search of its atoms
    #: while the end-to-end statement rested on length-16 agreement, and no
    #: amount of vocabulary checking could tell the two apart.  Here the
    #: distinction is a field, the weak value is the default, and asserting the
    #: strong one is a specific claim a reviewer can go and falsify.
    covers: str = "step"

    @property
    def ceiling(self) -> str:
        """The strongest status this check alone could support."""
        if not self.passed:
            return "UNREVIEWED"
        if self.scope == "sampled":
            return "EMPIRICAL"
        # Exhaustive, but with no control that fired, is indistinguishable from a
        # checker that cannot fail.  "All N passed" and "the judge always says
        # pass" are the same output; only a control separates them.
        if not any(control.rejected for control in self.controls):
            return "UNREVIEWED"
        return "COMPUTED"

    def to_json(self) -> dict[str, Any]:
        return {
            "name": self.name,
            "claim_ids": list(self.claim_ids),
            "scope": self.scope,
            "passed": self.passed,
            "detail": self.detail,
            "universe": self.universe,
            "sample": self.sample,
            "controls": [control.to_json() for control in self.controls],
            "load_bearing": self.load_bearing,
            "covers": self.covers,
            "ceiling": self.ceiling,
        }


def _ids(claim_ids: str | Iterable[str]) -> tuple[str, ...]:
    if isinstance(claim_ids, str):
        return (claim_ids,)
    return tuple(claim_ids)


def exhaustive(
    name: str,
    claim_ids: str | Iterable[str],
    *,
    passed: bool,
    universe: int,
    detail: str,
    controls: Sequence[Control] = (),
    load_bearing: bool = True,
    covers: str = "step",
) -> Check:
    """A finite object was traversed completely.  `universe` is its measured size.

    `universe` is required and must be the number of objects actually visited,
    not an estimate: a traversal that reports a size it did not count is the
    same kind of claim the ledger is trying to stop making.
    """
    if universe < 1:
        raise VerdictError(f"{name}: an exhaustive check must have visited something")
    return Check(
        name=name,
        claim_ids=_ids(claim_ids),
        scope="exhaustive",
        passed=passed,
        detail=detail,
        universe=universe,
        controls=tuple(controls),
        load_bearing=load_bearing,
        covers=covers,
    )


def sampled(
    name: str,
    claim_ids: str | Iterable[str],
    *,
    passed: bool,
    sample: str,
    detail: str,
    load_bearing: bool = True,
    covers: str = "step",
) -> Check:
    """A finite sample was checked.  `sample` states its extent, e.g. "length <= 14".

    This is not a lesser way of writing `exhaustive`.  A sampled check that
    passes establishes nothing; it is recorded so that the gap is visible and so
    that a future failure has somewhere to be reported.  Mark a sampled check
    `load_bearing=False` only when something else decides the same claim.
    """
    return Check(
        name=name,
        claim_ids=_ids(claim_ids),
        scope="sampled",
        passed=passed,
        detail=detail,
        sample=sample,
        load_bearing=load_bearing,
        covers=covers,
    )


def conjunction(
    name: str,
    claim_ids: str | Iterable[str],
    *,
    parts: Sequence[Check],
    detail: str,
) -> Check:
    """Assert that `parts` together decide the claim, and inherit their strength.

    This is the only way to produce a `covers="claim"` check out of components,
    and it cannot overstate them: it passes exactly when every part passed, its
    ceiling is the weakest part's ceiling, and its controls are theirs.  What
    the author contributes is the one thing a program cannot supply -- the
    assertion that this particular list of verified components exhausts the
    claim -- and that assertion is written down, attached to a named row, and
    falsifiable by a reviewer who can name a missing part.
    """
    if not parts:
        raise VerdictError(f"{name}: a conjunction of nothing decides nothing")
    return Check(
        name=name,
        claim_ids=_ids(claim_ids),
        scope=min((part.scope for part in parts), key=["sampled", "exhaustive"].index),
        passed=all(part.passed for part in parts),
        detail=f"{detail} [{', '.join(part.name for part in parts)}]",
        universe=sum(part.universe or 0 for part in parts) or None,
        sample="; ".join(part.sample for part in parts if part.sample) or None,
        controls=tuple(control for part in parts for control in part.controls),
        covers="claim",
    )


# ---------------------------------------------------------------------------
# The brittleness harness for integer identities over words
# ---------------------------------------------------------------------------


@dataclass(frozen=True, slots=True)
class Observable:
    """An integer statistic of a word, defined by when it increases.

    `increment(control, letter, next_control)` returns how much the statistic
    grows on that transition, and `terminal(control)` how much it gains at the
    end of the word (this is where a quantity like `[the word ends mid-token]`
    lives).  The caller supplies the *meanings*; it never supplies the combined
    quantity, because that is what the claim is about.
    """

    name: str
    increment: Callable[[Hashable, str, Hashable], int]
    terminal: Callable[[Hashable], int] = lambda control: 0


def decide_linear_identity(
    name: str,
    claim_ids: str | Iterable[str],
    *,
    alphabet: Sequence[str],
    control_start: Hashable,
    control_step: Callable[[Hashable, str], Hashable],
    observables: Sequence[Observable],
    coefficients: Mapping[str, int],
    detail: str,
    modulus: int | None = None,
    bound: int = 4096,
    covers: str = "step",
) -> Check:
    """Decide `sum_k coefficients[k] * observable_k(w) == 0` for every word `w`.

    With `modulus = m` the identity is read in `Z/m` instead of `Z`, which is
    the usual shape here (`binom(w,aab) = M1 + 2*M2 (mod 4)`).  Working mod `m`
    also makes the state space finite outright, so `bound` only matters in the
    integer case.

    The identity is checked by breadth-first search over
    `(control state, running value of the linear form)`.  The caller supplies
    the control automaton and the meaning of each observable, and this function
    derives the transition on the linear form.  **The caller never writes that
    transition.**  That is deliberate: `THOMAS-D2-02` was certified by a machine
    whose author had pre-solved the arithmetic and coded only the answer, so the
    program agreed with the author by construction.  Here the arithmetic is done
    from the coefficients, which means it can be wrong -- and therefore tested.

    Termination.  The search is finite exactly when the running value stays
    bounded, which is what a true identity of this shape forces.  A perturbed
    coefficient usually makes the value drift without bound; exceeding `bound`
    reachable states is treated as rejection, which is correct, since an
    identity whose defect is unbounded is false on all but finitely many words.

    Every coefficient is perturbed to `+1` and to `-1` of its stated value, and
    each perturbation must be rejected.  A coefficient the traversal cannot
    notice is a coefficient the traversal is not testing, and the check fails
    rather than passing quietly.
    """
    names = [observable.name for observable in observables]
    missing = set(coefficients) - set(names)
    if missing:
        raise VerdictError(f"{name}: coefficients for unknown observables {sorted(missing)}")
    if not coefficients:
        raise VerdictError(f"{name}: an identity with no coefficients tests nothing")

    def reduce(value: int) -> int:
        return value % modulus if modulus else value

    def run(weights: Mapping[str, int]) -> tuple[bool, int]:
        """Whether the form vanishes at the end of every word, and states seen."""
        start = (control_start, 0)
        seen: set[tuple[Hashable, int]] = {start}
        frontier: deque[tuple[Hashable, int]] = deque([start])
        visited = 0
        while frontier:
            control, value = frontier.popleft()
            visited += 1
            final = value + sum(
                weights.get(observable.name, 0) * observable.terminal(control)
                for observable in observables
            )
            if reduce(final) != 0:
                return False, visited
            for letter in alphabet:
                nxt_control = control_step(control, letter)
                nxt_value = reduce(
                    value
                    + sum(
                        weights.get(observable.name, 0)
                        * observable.increment(control, letter, nxt_control)
                        for observable in observables
                    )
                )
                state = (nxt_control, nxt_value)
                if state not in seen:
                    if len(seen) >= bound:
                        # An unbounded defect: the identity fails on all but
                        # finitely many words.  Only reachable without a modulus.
                        return False, visited
                    seen.add(state)
                    frontier.append(state)
        return True, visited

    passed, visited = run(coefficients)

    controls: list[Control] = []
    for key, value in sorted(coefficients.items()):
        for delta in (+1, -1):
            perturbed = dict(coefficients)
            perturbed[key] = reduce(value + delta) if modulus else value + delta
            if perturbed[key] == value:
                continue  # a no-op modulo `m` is not a perturbation
            controls.append(
                Control(
                    name=f"{key} {value} -> {perturbed[key]}",
                    mutation=f"the {key} coefficient of the identity",
                    rejected=not run(perturbed)[0],
                )
            )
    if not controls:
        raise VerdictError(f"{name}: no coefficient could be perturbed")

    silent = [control.name for control in controls if not control.rejected]
    if passed and silent:
        # The identity holds, and so does a variant of it that differs in a
        # coefficient.  Either the observables do not mean what they are named,
        # or the identity is degenerate.  Either way the check has not tested it.
        passed = False
        detail = (
            f"{detail}; REJECTED: these perturbations were not noticed, so the "
            f"traversal does not depend on them: {', '.join(silent)}"
        )

    return Check(
        name=name,
        claim_ids=_ids(claim_ids),
        scope="exhaustive",
        passed=passed,
        detail=detail,
        universe=max(visited, 1),
        controls=tuple(controls),
        covers=covers,
    )


# ---------------------------------------------------------------------------
# Runs
# ---------------------------------------------------------------------------


@dataclass
class Run:
    """The checks one script performed, and the ceiling each claim earned."""

    script: str
    checks: list[Check] = field(default_factory=list)

    def add(self, check: Check) -> Check:
        self.checks.append(check)
        mark = "ok" if check.passed else "FAIL"
        extent = (
            f"{check.universe} states"
            if check.scope == "exhaustive"
            else f"sample: {check.sample}"
        )
        fired = sum(1 for control in check.controls if control.rejected)
        print(
            f"  [{mark}] {check.name} ({check.scope}, {extent}"
            + (f", {fired}/{len(check.controls)} controls fired" if check.controls else "")
            + f"): {check.detail}",
            flush=True,
        )
        return check

    @property
    def failed(self) -> list[Check]:
        return [check for check in self.checks if not check.passed]

    def ceiling(self, claim_id: str) -> str:
        """The strongest status this run's evidence supports for `claim_id`.

        Two conditions, both necessary.  Something must decide the claim end to
        end (`covers="claim"`); verifying components, however exhaustively, says
        nothing about their composition.  And every load-bearing check that
        touches the claim caps it, so one sampled step pulls the whole row down
        even when the rest is decided.
        """
        relevant = [
            check
            for check in self.checks
            if claim_id in check.claim_ids and check.load_bearing
        ]
        if not any(check.covers == "claim" for check in relevant):
            return "UNREVIEWED"
        return min((check.ceiling for check in relevant), key=ORDER.index)

    @property
    def claim_ids(self) -> list[str]:
        return sorted({cid for check in self.checks for cid in check.claim_ids})

    def to_json(self) -> dict[str, Any]:
        return {
            "schema": SCHEMA,
            "script": self.script,
            "checks": [check.to_json() for check in self.checks],
            "ceilings": {cid: self.ceiling(cid) for cid in self.claim_ids},
        }

    def write(self, path: Path | None = None) -> Path:
        """Emit the verdict file that `scripts/lint_claims.py` reads."""
        target = path or VERDICT_DIR / f"{Path(self.script).stem}.json"
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(
            json.dumps(self.to_json(), indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        return target

    def finish(self, path: Path | None = None) -> int:
        """Write the verdict file and return the process exit status."""
        target = self.write(path)
        shown = target.relative_to(ROOT) if target.is_relative_to(ROOT) else target
        print(f"\nverdict: {shown}")
        for claim_id in self.claim_ids:
            print(f"  {claim_id}: ceiling {self.ceiling(claim_id)}")
        if self.failed:
            print(
                "\nFAILED checks: " + ", ".join(check.name for check in self.failed),
            )
            return 1
        return 0


def load(path: str | Path) -> dict[str, Any]:
    """Read a verdict file, rejecting anything that is not one."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    if not isinstance(data, dict) or data.get("schema") != SCHEMA:
        raise VerdictError(f"{path}: not a {SCHEMA} document")
    return data


def ceilings() -> dict[str, str]:
    """Every claim's ceiling, from every verdict file on disk.

    When two runs speak about the same claim the weaker ceiling wins: a claim is
    only as strong as its weakest load-bearing evidence, which is the same rule
    the ledger states for status propagation.
    """
    result: dict[str, str] = {}
    if not VERDICT_DIR.is_dir():
        return result
    for path in sorted(VERDICT_DIR.glob("*.json")):
        for claim_id, ceiling in load(path).get("ceilings", {}).items():
            previous = result.get(claim_id)
            if previous is None or ORDER.index(ceiling) < ORDER.index(previous):
                result[claim_id] = ceiling
    return result
