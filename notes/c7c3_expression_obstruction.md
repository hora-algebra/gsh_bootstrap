# Why the height-one expression for `C_7 : C_3` does not close on the full alphabet

Ledger rows: `C7C3-SUB9-01`, `C7C3-EXPR-OBS-01` (both `UNREVIEWED`; see §5 for
why, and note that the reason is the verdict machinery and not the mathematics).
Program: `scripts/research/c7c3_expression_equivalence.py`.
Obligation: `N-C7C3-EXPR-001`.

## 1. What was being attempted, and why it would have mattered

`FULL-ALPH-RED-01` (`PROVED`) says `HeightOneForGroup G` is *equivalent* to the
identity fibre over the full `|G|`-letter alphabet having generalized star
height at most one. So for `C_7 : C_3` it is enough to

1. build a generalized regular expression of syntactic star height at most one
   denoting `{ w : eval(w) = e }` over all 21 letters,
2. compile it,
3. decide language equality against the 21-state word-problem automaton by
   product reachability.

That would have established `HeightOneForGroup (C_7 : C_3)` and removed the
group from the 24 of `COVER-LE59-01` — the first group of order above 12 to
leave that list. **It did not work.** This note records where it stops, because
that is the part worth keeping.

## 2. What was decided along the way

All of the following are complete finite decisions, not samples. Each expression
was compiled with `tools/regex_cert.py` and proved equal to an independently
built reference automaton by product reachability, and each star height was
measured by machine rather than counted by eye.

**Star-free blocks over all 21 letters** (height 0): `LOOP`, `TOKEN`, `NR`,
`AVOID_1`, `AVOID_2`, `OPEN_0`, `OPEN_1`, `OPEN_2` — 5, 5, 4, 3, 3, 5, 4, 4
states. The derivation that makes them writable with forbidden factors alone:
inside an excursion the phase walk is rigid, so the `eps` sequence of the movers
is **equivalent** to "the first two are equal, then they alternate, and the last
two are equal".

**Cut-counting features** (height 1, 21 states each): the base cut at each phase
mod 7, the cut skipping non-movers at each phase mod 7, and the `eps`-letter
counts mod 3. Eighteen of them.

**The 9-letter sub-alphabet closes completely.** On
`{(1,b) : b in C_7} u {y, y^2}` — the seven kernel elements together with the two
non-trivial elements of `C_3`, which generate the group — twenty-one cut features
assemble over `GF(7)` into an expression of measured star height 1 that compiles
to 21 states and is proved equal to the identity fibre over those letters by
product reachability.

This does **not** give `HeightOneForGroup`. `FULL-ALPH-RED-01` needs the full
alphabet, and `F20-SUB10-OBS-01` already established that a sub-alphabet success
need not lift.

## 3. The obstruction, decided

The feature that is missing is the **phase-resolved pair cut**: the number of
positions arriving at phase `q` whose preceding letter is `l` and whose own
letter is a mover `g`, counted mod 7.

That it is missing is a rank computation on the cycle space of the phase
automaton over `GF(7)`, not a search:

    cycle generators                                     1323
    rank(letter counts, all 441 adjacent-pair counts,
         the three base cuts, the 21 non-mover phase counts)   437
    rank(the same, plus beta')                                 438

So `beta'` lies **exactly one dimension** outside the span. No Boolean assembly
of those features denotes the identity fibre — **at any star height**. Adding
the phase-resolved pair counts takes the rank to 1021 and `beta'` is then inside,
so that one family is precisely what is absent.

The minimal witness is a pair of words of length 5, with none of length at most
4 (checked exhaustively):

    w1 = (2,5)(2,5)(2,0)(2,5)(1,3)   eval = (1,1)   not in T
    w2 = (2,5)(2,0)(2,5)(2,5)(1,3)   eval = (1,0)   in T

They are the **same multiset of letters** — one adjacent transposition apart —
so every feature invariant under that swap fails to separate them, and all the
constructible features are.

## 4. Why the missing feature was not built

Its block language has the shape `(skipped tokens)* . (cutting token)`, and the
skipped tokens are loops of unbounded length. That star **is** star-free: the
block automaton has 12 raw states and its transition monoid, enumerated
completely, has 90 elements and is aperiodic for both `eps(g) = 1` and
`eps(g) = 2`. By Schützenberger a height-one expression therefore **exists**.
It was not constructed.

Two routes were tried and both failed, which is why the note says "not
constructed" rather than "does not exist":

- The §2 method did not reach it **at any window that was tried**: the locally
  testable approximation on flagged mover sequences differs at windows 1 through
  7, with the witness growing as the window does (`m1m2`, `m1m1m1`, `m1gm2m2`,
  …). The natural reading is that the phase depends on how far the current loop
  has run and no bounded mover window sees that — **but seven refuted windows and
  a visible pattern are not a proof for all windows**, and this note earlier said
  they were. They are an `EMPIRICAL` obstruction: they refute windows 1..7 and
  nothing more.

  This is decidable rather than extrapolable, which is what the next attempt
  should do first. A language is locally testable exactly when its syntactic
  semigroup lies in the variety **LT**: `eSe` is idempotent and commutative for
  every idempotent `e`.

  **Run it on the right object.** That is the syntactic semigroup of the *alive
  language of a pair-cut block*, over its six flagged mover letters — mover
  class in `{m1, m2, g}` times whether a non-mover run sat immediately before —
  taken from that language's **minimal** automaton. An earlier version of this
  note said to use the 90-element monoid printed above instead. That is a
  different language over a different alphabet (the block language, over all 21
  letters), so it cannot answer this question at all.

  **This does not weaken the star-free conclusion above, and the difference is
  worth being explicit about**, because the same 90-element monoid carries both
  and only one of the two uses is legitimate. Aperiodicity is inherited by
  divisors, and the syntactic monoid of a language divides the transition monoid
  of any automaton recognising it — so an aperiodic transition monoid, minimised
  or not, is already enough for Schützenberger, and the star-freeness of the
  block language stands. Membership in `LT` is not transported that way, and in
  any case the alive language is not the block language, so neither half of the
  earlier pointer survives. Until the right check runs, treat the window claim
  as unproved.
- A breadth-first enumeration of the star-free closure of the four class letters,
  de-duplicated by canonical minimal DFA and capped at 9 states, exhausted
  7.2 × 10^5 languages in 240 s without reaching it. **That is a failed search
  and proves nothing**, and it is not re-run by the committed script.

The remaining route is to implement Schützenberger's constructive proof and read
off the expression. Whether the result is of usable size is **unverified**.

## 5. Status, and what caps it

Both rows are `UNREVIEWED`. Nothing the two rows *claim* is sampled — those
decisions are product reachability and exact rank — so `EMPIRICAL` would be the
wrong label for them, and
`COMPUTED` is unavailable because the ledger requires a `tools/verdict.py`
verdict for new `COMPUTED` rows and `data/verdicts/PENDING.md` is closed to new
entries by its own terms. `N-C7C3-EXPR-001` records both the migration and the
remaining mathematics.

The window result of §4 is the exception and is deliberately not part of either
row: it refutes windows 1..7 and is `EMPIRICAL`, which is why §4 now says so and
why the LT check is the first thing to run. Keeping it out of the rows is what
lets the rows say "nothing sampled" truthfully.

## 6. What this does to the surrounding claims

`C7C3-FULL-01` is untouched: it is about the reconstruction from certified
features, which section 7 of `metacyclic_full_alphabet.py` decides. This note is
about a different question — whether an explicit height-one *expression* can be
written — and the answer is that the features constructed so far provably cannot
give one.

`FAMILY-A-PRED-01` is also untouched in its own terms: it predicts the
multi-mover mechanism certifies Family A, and it does. What this note shows is
that certifying the mechanism is strictly weaker than producing the expression,
which the ledger rows already said and which now has a decided example.
