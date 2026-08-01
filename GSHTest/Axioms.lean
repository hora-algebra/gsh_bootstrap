import GSH
import GSH.Conjecture

/-!
# Axiom audit

Machine-checked evidence that nothing in the repository rests on the one `sorry`
it intentionally keeps (`GSH.generalized_star_height_conjecture`, obligation
`L-GSH-CHALLENGE-001`), or on `native_decide`, or on an `axiom` someone added.

The permitted axioms are the three standard ones — `propext`,
`Classical.choice`, `Quot.sound`.  `Classical.choice` is unobjectionable here:
every statement audited is a `Prop`, and no constructive content is claimed for
any of them (see `AGENTS.md`, "Forbidden shortcuts").

## Why this is a sweep and not a list

Until 2026-07-25 this file was eight hand-written `#print axioms` lines.  Every
one of them passed, and the audit was still nearly worthless, because **a new
theorem was audited only if someone remembered to add its name here**.  A future
`heightOneUpTo_eleven` would have gone in with zero friction and no gate would
have noticed; the four declarations that already existed and were not listed
(`HeightOneForGroup.of_mulEquiv`, `HeightOneUpTo.mono`,
`RegexCertificate.checker_sound`, `a5_isSimple`) show the drift was not
hypothetical.  An audit whose coverage depends on an author's memory measures
the author.

So the check now enumerates every theorem in the `GSH` namespace from the
environment and fails on any axiom outside the three, with exactly one
exemption.  Adding a theorem adds it to the audit.

The sweep runs twice.  The second run drops the exemption and **must** find the
conjecture: an audit that silently stopped inspecting anything would otherwise
pass, which is the same failure mode `tools/verdict.py` exists to prevent on the
Python side — "all N passed" and "the judge always says pass" are the same
output until a control separates them.
-/

open Lean Elab Command in
/-- Audit every theorem under `GSH`, exempting the given names.  Returns the
offenders it found, so that the caller can either demand none or demand a
specific one. -/
def auditGSH (exempt : Array Name) : CommandElabM (Array (Name × Array Name)) := do
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let env ← getEnv
  -- Every kind of declaration that can carry or consume an axiom, not only
  -- `.thmInfo`. An adversarial review on 2026-07-25 showed the earlier version
  -- missing two things at once: an `axiom` declaration under `GSH` is
  -- `.axiomInfo` and was skipped outright, and a proof-valued `def` consuming
  -- it -- `def hiddenConsequence : False := hiddenAxiom` -- is `.defnInfo` and
  -- was skipped too. Both compiled and both passed. Auditing definitions as
  -- well as theorems costs nothing here and closes the pair.
  let names : Array Name := env.constants.fold (init := #[]) fun acc name info =>
    if (`GSH).isPrefixOf name && !name.isInternal && !exempt.contains name then
      match info with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ | .axiomInfo _ => acc.push name
      | _ => acc
    else acc
  let mut offenders : Array (Name × Array Name) := #[]
  for name in names do
    -- An `axiom` under `GSH` is forbidden outright (AGENTS.md), and
    -- `collectAxioms` of an axiom reports only itself, so name it here.
    if let some (.axiomInfo _) := env.find? name then
      offenders := offenders.push (name, #[name])
      continue
    let used ← liftCoreM (collectAxioms name)
    let extra := used.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do
      offenders := offenders.push (name, extra)
  return offenders

open Lean Elab Command in
run_cmd do
  let exempt : Array Name := #[``GSH.generalized_star_height_conjecture]

  -- The audit proper.
  let offenders ← auditGSH exempt
  unless offenders.isEmpty do
    let report := offenders.map fun (name, axs) => s!"{name} uses {axs}"
    throwError "axiom audit failed:{indentD (String.intercalate "\n" report.toList)}"

  -- The negative control.  Without the exemption the sweep has to catch the
  -- conjecture; if it does not, the sweep is not looking at anything.
  let control ← auditGSH #[]
  unless control.any (fun (name, axs) =>
      name == ``GSH.generalized_star_height_conjecture && axs.contains ``sorryAx) do
    throwError
      "the axiom audit's own control did not fire: the sweep failed to notice that \
       GSH.generalized_star_height_conjecture depends on sorryAx. Either the \
       conjecture has been proved, or this audit is inspecting nothing."
  unless control.size == 1 do
    let report := control.map fun (name, axs) => s!"{name} uses {axs}"
    throwError "more declarations than the conjecture depend on a forbidden \
      axiom:{indentD (String.intercalate "\n" report.toList)}"

  logInfo "axiom audit: every theorem under GSH is clean; the control fired."

/-! ## The headline theorems, spelled out

The sweep is the gate.  These stay because they record *which* axioms each
result uses, which is information the sweep does not print, and because a reader
who wants to check one result by hand should not have to run a metaprogram. -/

/-- info: 'GSH.Counting.hasHeightAtMost_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.Counting.hasHeightAtMost_count

/-- info: 'GSH.HeightOneForGroup.of_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GSH.HeightOneForGroup.of_injective

/-- info: 'GSH.HeightOneForGroup.of_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.HeightOneForGroup.of_surjective

/-- info: 'GSH.heightOne_of_mul_comm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOne_of_mul_comm

/-- info: 'GSH.heightOneUpTo_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOneUpTo_five

/-- info: 'GSH.heightOneForGroup_of_fullIdentityFiber' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOneForGroup_of_fullIdentityFiber

/-- info: 'GSH.heightOne_S3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOne_S3

/-- info: 'GSH.heightOne_D4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOne_D4

/-- info: 'GSH.heightOne_Q8' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOne_Q8

/-- info: 'GSH.heightOne_D5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.heightOne_D5

/-- info: 'GSH.HasHeightAtMost.reverse' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GSH.HasHeightAtMost.reverse

/-- info: 'GSH.HasHeightAtMost.booleanCombination' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GSH.HasHeightAtMost.booleanCombination

/-- info: 'GSH.syntacticMorphism_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms GSH.syntacticMorphism_eq_iff

/-- info: 'GSH.generalized_star_height_conjecture' depends on axioms: [propext, sorryAx, Quot.sound] -/
#guard_msgs in
#print axioms GSH.generalized_star_height_conjecture
