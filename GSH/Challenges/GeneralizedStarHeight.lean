import Mathlib.Data.Set.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Basic

/-!
# The generalized star-height conjecture (open challenge)

This file contains the **entire definition chain** of the generalized
star-height conjecture in one place, ending with the explicitly open
challenge theorem.  Reading this one file from top to bottom is enough to
know exactly what is being conjectured.

These are not copies: the definitions below are the *single source of
truth* for the whole repository.  `GSH/Recognition.lean`,
`GSH/Groups.lean`, `GSH/Certificates.lean`, and every other Lean module of
the project import this file (directly or transitively);
nothing here is defined anywhere else.  (History: until 2026-07-23 the
material of §1 lived in `GSH/Language/Basic.lean`, §2–§4 in
`GSH/Regex/Generalized.lean`, and §5 in `GSH/Blueprint.lean`; they were
consolidated here, unchanged, so that the conjecture is readable in one
file without duplicating definitions.)

This file imports only mathlib.  In particular the registered `sorry`
placeholders elsewhere in the repository (in `GSH/Recognition.lean`:
obligations L-SYN-002 and L-SF-001) are *not* in its import closure and
cannot affect the meaning of the statement below.  The only `sorry` in this
file is the final theorem — the open challenge itself.

## The conjecture in ordinary mathematical language

Let `α` be a finite alphabet and `α*` the set of finite words over `α`.
*Generalized regular expressions* over `α` are built from the empty
language, the empty word, and the single letters, using union,
concatenation, complement (relative to the full `α*`), and Kleene star.
The *generalized star height* `h(L)` of a language `L ⊆ α*` is the least
nesting depth of the Kleene-star operator over all generalized regular
expressions denoting `L`; complement contributes nothing to the depth.

> **Conjecture (height-one collapse).**  For every finite alphabet `α` and
> every regular language `L ⊆ α*`, we have `h(L) ≤ 1`.

Open since the 1960s.  It is the structural conjecture, **not** the
distinct algorithmic problem of computing `h(L)` for an input `L`.  No
regular language of generalized star height `> 1` is known; height `> 0`
occurs (e.g. `(aa)*` over `α = {a}` has height exactly `1`).

## 日本語での要約

有限アルファベット `α` 上の一般化正規表現とは、空言語・空語・各文字から
和集合・連接・補集合（`α*` 全体に対する）・クリーネ星で作られる式のこと。
言語 `L` の一般化スター高さ `h(L)` とは、`L` を表すそのような式全体に
わたる星の入れ子の深さの最小値である。**予想: すべての正規言語 `L` に
ついて `h(L) ≤ 1`**（1960年代からの未解決問題）。この予想の定義一式は
すべて本ファイル内にあり、末尾の `sorry` がその未解決の挑戦そのものである。

## Contents

1. Words, languages, and the language operations
   (concatenation, power, Kleene star, complement)
2. Syntax of generalized regular expressions (`GRegex`)
3. Semantics (`GRegex.denote`) and star height (`GRegex.starHeight`)
4. Semantic properties of languages:
   `HasHeightAtMost`, `IsRegular`, `IsStarFree`, `HeightOneCollapse`
5. The conjecture (`GeneralizedHeightOneConjecture`) and the open
   challenge theorem (the one `sorry`)

## Statement-audit notes

* Fully unfolded, the statement reads
  `∀ (α : Type u) [Fintype α], ∀ L : Language α, IsRegular L →
  HasHeightAtMost L 1`.
* `Language α` is `Set (List α)`, so complement is always relative to the
  fixed free monoid `α*`.
* `HasHeightAtMost L 1` demands a witnessing expression with
  `denote r = L` — **exact** language equality, not agreement on a finite
  sample — and `starHeight r ≤ 1`.
* `IsRegular` is *defined* as "denoted by some generalized regular
  expression".  Classically this coincides with DFA regularity, but that
  equivalence is a separate formalization target and is not assumed here.
* The empty alphabet is included (a trivial boundary case); no
  `Nonempty α` or `DecidableEq α` assumption is imposed.
* The alphabet ranges over an arbitrary universe `u`.  This generality is
  mathematically inessential (every finite type is equivalent to some
  `Fin n`), but the universe-invariance of the statement has not been
  formalized.
* This file records an open challenge; the final declaration is not
  evidence that the conjecture has been proved.

## Relation to the finite-group ladder

The repository attacks the conjecture through recognition by finite groups.
`HeightOneForGroup G` (defined downstream, in `GSH/Recognition.lean` §5)
says: for **every** finite alphabet `α`, **every** monoid morphism
`φ : α* →* G`, and **every** accepting subset `S ⊆ G`, the recognized
language `φ⁻¹(S)` satisfies `HasHeightAtMost (φ⁻¹(S)) 1` in the sense of
§4 below.  ("Recognized by `G`" means membership in such a preimage, *not*
that the syntactic monoid equals `G`.)  Proving `HeightOneForGroup G` for
particular groups (`A_4`, `Dic_3`, `A_5`, … in `GSH/Groups.lean`) is
strictly weaker than the conjecture stated in this file; the conjecture
implies all of them, not conversely.

## Cross-references

* Proof obligation: `PROOF_OBLIGATIONS.md`, row `L-GSH-CHALLENGE-001`
  (acceptance: a formal-language expert approves the statement and this
  file compiles).
* Claims ledger: `CLAIMS_LEDGER.md`, row `GLOBAL-ONE`, status
  `CONJECTURAL`.  This file registers the conjecture; it does not upgrade
  its status.

## References

* J.-É. Pin, H. Straubing, and D. Thérien,
  *Some Results on the Generalized Star-Height Problem*, Information and
  Computation 101 (1992), 219–250.  https://hal.science/hal-00019978
* J.-É. Pin, *Open Problems about Regular Languages, 35 Years Later*,
  Theoretical Computer Science 701 (2017), 23–46.
  https://hal.science/hal-01614375
* T. Bourne, *Counting Subwords and Other Results Related to the Generalised
  Star-Height Problem for Regular Languages*, PhD thesis (2017).
  https://research-repository.st-andrews.ac.uk/handle/10023/12024
-/

set_option autoImplicit false

namespace GSH

universe u

/-! ### 1.  Words, languages, and the language operations

A word over `α` is a finite sequence of letters, encoded as a `List α`;
`[]` is the empty word (written `ε` in the literature) and `u ++ v` is
concatenation.  A language is an arbitrary set of words; complement is
therefore always relative to the full `α*`. -/

abbrev Word (α : Type u) := List α
abbrev Language (α : Type u) := Set (Word α)

namespace Language

variable {α : Type u}

/-- The empty language. -/
def empty : Language α := ∅

/-- The language containing only the empty word. -/
def epsilon : Language α := {[]}

/-- The singleton one-letter language. -/
def letter (a : α) : Language α := {[a]}

/-- Boolean complement inside the full free monoid `List α`. -/
def compl (L : Language α) : Language α := Lᶜ

/-- Language concatenation: `{ u ++ v | u ∈ L, v ∈ K }`. -/
def concat (L K : Language α) : Language α :=
  {w | ∃ u ∈ L, ∃ v ∈ K, u ++ v = w}

/-- The `n`-fold concatenation power, with zeroth power `{ε}`. -/
def power (L : Language α) : Nat → Language α
  | 0 => epsilon
  | n + 1 => concat (power L n) L

/-- Kleene star as the union of all finite powers. -/
def star (L : Language α) : Language α :=
  {w | ∃ n : Nat, w ∈ power L n}

@[simp] theorem mem_empty (w : Word α) : w ∉ (empty : Language α) := by
  simp [empty]

@[simp] theorem mem_epsilon_iff (w : Word α) : w ∈ (epsilon : Language α) ↔ w = [] := by
  simp [epsilon]

@[simp] theorem mem_letter_iff (a : α) (w : Word α) : w ∈ letter a ↔ w = [a] := by
  simp [letter]

@[simp] theorem mem_compl_iff (L : Language α) (w : Word α) :
    w ∈ compl L ↔ w ∉ L := by
  rfl

@[simp] theorem mem_concat_iff (L K : Language α) (w : Word α) :
    w ∈ concat L K ↔ ∃ u ∈ L, ∃ v ∈ K, u ++ v = w := by
  rfl

@[simp] theorem power_zero (L : Language α) : power L 0 = epsilon := by
  rfl

@[simp] theorem power_succ (L : Language α) (n : Nat) :
    power L (n + 1) = concat (power L n) L := by
  rfl

@[simp] theorem mem_star_iff (L : Language α) (w : Word α) :
    w ∈ star L ↔ ∃ n : Nat, w ∈ power L n := by
  rfl

end Language

/-! ### 2.  Syntax of generalized regular expressions

Complement is a primitive constructor; this is what distinguishes
*generalized* regular expressions from ordinary ones. -/

/-- Generalized regular expressions: formal syntax trees whose meaning is
assigned by `GRegex.denote` below.  `zero` denotes the empty language,
`epsilon` the language `{ε}`, `atom a` the singleton `{a}`; `union`,
`concat`, `compl`, and `star` denote the corresponding language
operations. -/
inductive GRegex (α : Type u) where
  | zero : GRegex α
  | epsilon : GRegex α
  | atom : α → GRegex α
  | union : GRegex α → GRegex α → GRegex α
  | concat : GRegex α → GRegex α → GRegex α
  | compl : GRegex α → GRegex α
  | star : GRegex α → GRegex α
  deriving Repr

namespace GRegex

variable {α : Type u}

/-! ### 3.  Semantics and star height -/

/-- Denotational semantics over finite words. -/
def denote : GRegex α → Language α
  | zero => Language.empty
  | epsilon => Language.epsilon
  | atom a => Language.letter a
  | union r s => denote r ∪ denote s
  | concat r s => Language.concat (denote r) (denote s)
  | compl r => Language.compl (denote r)
  | star r => Language.star (denote r)

/-- Maximum nesting depth of the Kleene-star constructor.  Union,
concatenation, and — crucially — complement do not increase the height;
each application of `star` increases it by one. -/
def starHeight : GRegex α → Nat
  | zero | epsilon | atom _ => 0
  | union r s | concat r s => max (starHeight r) (starHeight s)
  | compl r => starHeight r
  | star r => starHeight r + 1

@[simp] theorem starHeight_zero : starHeight (zero : GRegex α) = 0 := rfl
@[simp] theorem starHeight_epsilon : starHeight (epsilon : GRegex α) = 0 := rfl
@[simp] theorem starHeight_atom (a : α) : starHeight (atom a) = 0 := rfl
@[simp] theorem starHeight_compl (r : GRegex α) :
    starHeight (compl r) = starHeight r := rfl
@[simp] theorem starHeight_star (r : GRegex α) :
    starHeight (star r) = starHeight r + 1 := rfl

end GRegex

/-! ### 4.  Semantic properties of languages -/

/-- A semantic upper bound on generalized star height: some expression of
star height `≤ n` denotes `L` **exactly**.  This is the quantity
`h(L) ≤ n` — an existential over all expressions for `L`. -/
def HasHeightAtMost {α : Type u} (L : Language α) (n : Nat) : Prop :=
  ∃ r : GRegex α, GRegex.denote r = L ∧ GRegex.starHeight r ≤ n

/-- Regularity expressed through generalized regular expressions. -/
def IsRegular {α : Type u} (L : Language α) : Prop :=
  ∃ r : GRegex α, GRegex.denote r = L

/-- Star-free means generalized height at most zero. -/
def IsStarFree {α : Type u} (L : Language α) : Prop :=
  HasHeightAtMost L 0

/-- The height-one collapse statement for one alphabet. -/
def HeightOneCollapse (α : Type u) : Prop :=
  ∀ L : Language α, IsRegular L → HasHeightAtMost L 1

/-! ### 5.  The conjecture -/

/-- **The generalized star-height conjecture** (global height-one collapse
over finite alphabets), with all quantifiers explicit:

for every finite alphabet `α`, for every language `L` over `α`, if `L` is
regular then some generalized regular expression of star height at most `1`
denotes `L` exactly.

Ledger row `GLOBAL-ONE` in `CLAIMS_LEDGER.md`, status `CONJECTURAL`. -/
def GeneralizedHeightOneConjecture : Prop :=
  ∀ (α : Type u) [Fintype α], HeightOneCollapse α

/-- **The open challenge** (obligation `L-GSH-CHALLENGE-001` in
`PROOF_OBLIGATIONS.md`).  The `sorry` below *is* the open problem: this
declaration records the target statement and is not evidence that the
conjecture has been proved. -/
-- BLUEPRINT: L-GSH-CHALLENGE-001
theorem generalized_star_height_conjecture : GeneralizedHeightOneConjecture := by
  sorry

end GSH
