# Retractions

Claims this repository made and has withdrawn, and the gates added so that the
same shape of error is caught by a program rather than by the next reader.

This file exists because the alternative is worse. A project whose value is that
its claims are honestly labelled has to be able to say when a label was wrong,
in one place, without hedging — and until 2026-07-25 these records were
scattered across a `README.md` bullet, a ledger header parenthesis, a research
rule, and a comment in `.gitignore`. A scientific retraction does not belong in
`.gitignore`.

Every entry names what was asserted, what is true instead, how it got past the
checks that existed, and what now stops it. The ledger rows are the normative
record; this file is the narrative one.

---

## 2026-07-22 → 2026-07-25 — "order ≤ 12 is settled", "the barrier moved to order 20"

**Withdrawn.** The barrier is at order 12, where Bourne 2017 left it, and `A_4`
is open.

**What was asserted.** That the full-alphabet `A_4` result established
`HeightOneForGroup A_4` (`A4-FULL-01`), hence all languages recognized by `A_4`
(`A4-ALLLANG-01`), hence all of order ≤ 12 (`ORD12-ALL-01`), hence that the
first unresolved case had moved to order 20 (`FRONTIER-ORD20-01`). `RESULTS.md`
§5.5 called it 解決した with no qualifier, and a workshop slide deck said so too.

**What is true.** The reconstruction of the counting features was checked on
words of length at most 4 plus 4,000 random words, and the final composition on
20,000 random words. A sample can refute and cannot establish. All four rows are
now `EMPIRICAL`, and `HeightOneForGroup A_4` is not established here. The
two-generator result (`A4-STD-01` / `A4-STD-02`) is unaffected and remains
`COMPUTED`; it does not imply the full-alphabet statement, because
`FULL-ALPH-RED-01` needs the full alphabet.

**How it passed.** `COMPUTED` had no definition that distinguished exhausting a
finite object from sampling one, so the label was honestly applied under the
definition then in force. The prose then outran even that: the verb "解決した"
was written where the label said only "a program agreed on the cases it tried".

**What stops it now.** `COMPUTED` and `EMPIRICAL` are separate labels with the
distinction written into the ledger header. `scripts/ci/lint_claims.py` refuses
a `COMPUTED` row that cites sampling, refuses prose that attaches a stronger
label to an `EMPIRICAL` row, and refuses five specific sentences that were
written in this repository and are false. The slide deck is out of version
control (`SLIDE-WITHDRAW-01`).

---

## 2026-07-25 — "the sampled rows have been upgraded to decided ones"

**Withdrawn for one row of the four.** `THOMAS-D2-02` was not decided by the
program that claimed to decide it.

**What was asserted.** That `scripts/completeness_upgrade.py` re-established
four demoted rows by exhaustive traversal, "with a negative control that must
fire". For `THOMAS-D2-02` the evidence cell read: the automaton on
`(parse state, signed defect D)` "reaches exactly 2 states and the identity
holds at both — an exhaustive traversal, no sampling — which covers every word".

**What is true.** Every sentence in that cell was accurate, and the check was
empty. The state was `(parse, d)`; `d` was defined to be `-1` exactly when
`parse == 1`, and the acceptance test asked whether `d == -1` when `parse == 1`.
None of `|w|_a`, `|w|_b`, `#tok`, `#ab` — the quantities the identity is about —
appeared anywhere in the machine, so all four coefficients of the identity could
be changed without it noticing. Its negative control perturbed the acceptance
constant, not the claim. The author had solved the arithmetic by hand and coded
the conclusion; the program confirmed the author's algebra.

The identity itself is true, and is now decided: ten coefficient perturbations,
all rejected. The other three rows of that commit (`A5-GEN145-01`,
`WATOM-45-01`, `LAAB-04-01`'s composite) were re-checked and are genuine.

**How it passed.** Every gate up to that point read the *description* of a
computation. This description was true. The failure was not a sample dressed as
an exhaustion — it was an exhaustive traversal of the wrong finite object, and
no vocabulary check can see the difference.

**What stops it now.** `tools/verdict.py` computes the label from what ran.
Scope is chosen by which constructor a script calls, so there is no sentence to
get wrong; the default is the weak one; and a check must be *brittle* — the
claim's own constants must be perturbable and every perturbation rejected.
`decide_linear_identity` derives the transition function from the coefficients
itself, so a pre-solved defect has nowhere to live. `lint_claims.py` refuses a
`COMPUTED` row whose verdict does not reach `COMPUTED`; the twenty rows that
predate the machinery are listed in `data/verdicts/PENDING.md` with the specific
step each still lacks, and that list may shrink and never grow.

---

## 2026-07-25 — "the ladder's import closure contains no unproved declaration"

**Withdrawn as written, and then made true.** `GSH/Recognition.lean` said this
while importing the file that held the repository's one `sorry`. The
*dependency* closure was clean and `GSHTest/Axioms.lean` proved it, so no
mathematical claim was affected — but the sentence a reader would check first
was false. The unproved declaration now sits alone in `GSH/Conjecture.lean`,
which nothing imports.

The same audit was, at the time, eight hand-written names. It has been replaced
by a sweep over every theorem in the `GSH` namespace, so that a new theorem is
audited whether or not anyone remembers it.

---

## 2026-07-25 — the gate that was supposed to fix all this, reviewed adversarially

**Six ways past it, executed, on the day it was written.** An adversarial review
of `tools/verdict.py` found that `load()` trusted the ceiling recorded in the
verdict file, so a committed JSON with no checks promoted any row; that
`Check.ceiling` asked whether *any* control fired while the documented rule was
*every*; that the brittleness rule constrained the combination of observables
and not the observables, so the `THOMAS-D2-02` attack reproduced one level down;
that `PENDING.md` rejected stale entries but not new ones, making "may shrink
and never grow" a request rather than a constraint; that `covers="claim"` was a
plain string a caller could assert; and that the Lean sweep enumerated only
`.thmInfo`, so an `axiom` declaration and a proof-valued `def` consuming it both
passed — as did `set_option ... in axiom`, which the source regex missed because
it required declaration position.

All six are fixed, each with a regression test that reproduces the original
attack. The general lesson is the one this file keeps recording: **the gate was
written by the same process it was meant to constrain, and it inherited the same
blind spot.** It took an adversary to find that, not a re-read.

## What has *not* been withdrawn

Worth stating, because a retractions file read alone gives a false impression.
`WEIS-L2-GSH-01` (the full Weis `L2` has generalized star-height 1, and
restricted star-height 2), `F20-STD-01`, `A4-STD-01`/`-02`, `LAAB-04-01`, and
the four Lean theorems up to order 5 were all re-examined during the audits
above and stand. None of the retractions here touches them.
