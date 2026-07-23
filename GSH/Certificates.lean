import GSH.Recognition

/-!
# Certificate boundary and experiment metadata

Consolidated 2026-07-23 from `GSH/Certificates/RegexCertificate.lean` and
`GSH/Experiments/FiniteSearch.lean`, definitions unchanged.

The certificate structure mirrors the JSON certificate at a semantic level.
The executable Python checker is not trusted by Lean; the eventual goal is a
verified checker whose acceptance theorem has the shape of `checker_sound`
below.  Search output is intentionally kept outside the trusted theorem
layer: a run must carry resource bounds and hashes, and only checked
certificates cross into mathematical claims.
-/

set_option autoImplicit false

namespace GSH

universe u v

structure RegexCertificate (α : Type u) (σ : Type v) where
  expression : GRegex α
  claimedHeight : Nat
  target : DFA α σ

namespace RegexCertificate

variable {α : Type u} {σ : Type v}

/-- Purely syntactic part of certificate validity. -/
def HeightValid (C : RegexCertificate α σ) : Prop :=
  C.expression.starHeight ≤ C.claimedHeight

/-- Semantic equivalence part; an executable implementation should decide this
for finite alphabets and state types. -/
def SemanticallyValid (C : RegexCertificate α σ) : Prop :=
  C.expression.denote = C.target.language

-- BLUEPRINT: L-CERT-001
/-- Soundness interface for a future Boolean checker. -/
theorem checker_sound
    [Fintype α] [DecidableEq α] [Fintype σ] [DecidableEq σ]
    (check : RegexCertificate α σ → Bool)
    (hcheck : ∀ C, check C = true → HeightValid C ∧ SemanticallyValid C)
    (C : RegexCertificate α σ) (h : check C = true) :
    HasHeightAtMost C.target.language C.claimedHeight := by
  rcases hcheck C h with ⟨height_ok, semantics_ok⟩
  exact ⟨C.expression, semantics_ok, height_ok⟩

end RegexCertificate

/-- Metadata for one search run; only checked certificates cross into
mathematical claims. -/
structure SearchManifest where
  approachId : String
  commit : String
  inputSha256 : String
  outputSha256 : String
  stateBound : Nat
  expressionSizeBound : Nat
  wallClockSeconds : Nat
  deriving Repr

end GSH
