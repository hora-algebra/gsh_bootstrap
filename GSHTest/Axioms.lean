import GSH

/-!
# Axiom audit

Machine-checked evidence that the finite-group ladder is not quietly resting on
the one `sorry` the repository intentionally keeps
(`GSH.generalized_star_height_conjecture`, obligation `L-GSH-CHALLENGE-001`).

`#guard_msgs` turns each `#print axioms` into a **test**: if any declaration
below ever acquires `sorryAx`, `Lean.ofReduceBool` (i.e. `native_decide`), or
any other axiom, this file stops compiling.  Reading the build log is not
required and not trusted.

The permitted axioms are the three standard ones — `propext`,
`Classical.choice`, `Quot.sound`.  `Classical.choice` is unobjectionable here:
every statement audited below is a `Prop`, and no constructive content is
claimed for any of them (see `AGENTS.md`, "Forbidden shortcuts").

The last entry is a **negative control**: it asserts that the open conjecture
*does* depend on `sorryAx`.  Without it, an audit that silently stopped
inspecting anything would still pass.
-/

/-! ### Height-one closure and counting infrastructure -/

/-- info: 'GSH.Counting.hasHeightAtMost_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.Counting.hasHeightAtMost_count

/-! ### Transfer along morphisms -/

/-- info: 'GSH.HeightOneForGroup.of_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GSH.HeightOneForGroup.of_injective

/-- info: 'GSH.HeightOneForGroup.of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.HeightOneForGroup.of_surjective

/-- info: 'GSH.HeightOneForGroup.subgroup' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GSH.HeightOneForGroup.subgroup

/-! ### The commutative case and the order ladder -/

/-- info: 'GSH.heightOne_of_commGroup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOne_of_commGroup

/-- info: 'GSH.heightOne_of_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOne_of_mul_comm

/-- info: 'GSH.mul_comm_of_card_le_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.mul_comm_of_card_le_five

/-- info: 'GSH.heightOneUpTo_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOneUpTo_five

/-! ### Negative control

The open conjecture is the only declaration in the repository that is allowed
to depend on `sorryAx`.  If this test starts failing because `sorryAx`
disappeared, that is either a proof of the generalized star-height conjecture
or, far more likely, a bug in this audit. -/

/-- info: 'GSH.generalized_star_height_conjecture' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in
#print axioms GSH.generalized_star_height_conjecture
