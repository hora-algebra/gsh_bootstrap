import GSH.Height.Q8FullFiber
import GSH.Height.D4ArrowAssembly
import GSH.Height.Counting

/-!
# Generalized star height one for `Q₈`

The letter map `q8ToD4` is not a group homomorphism.  The exact correction
proved in `Q8FullFiber` splits the quaternion identity fibre into two cells:
flip count zero modulo four over the dihedral identity fibre, and flip count
two modulo four over the dihedral `r 2` fibre.
-/

set_option autoImplicit false

namespace GSH

/-- Whether a quaternion letter uses the `xa` constructor. -/
def q8FlipBit : Q8Alphabet → Bool
  | .a _ => false
  | .xa _ => true

theorem count_map_q8FlipBit (word : Word Q8Alphabet) :
    (word.map q8FlipBit).count true = q8FlipCount word := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      rcases letter with i | i <;> simp [q8FlipBit, q8FlipCount, ih]

/-- Quaternion words with a prescribed flip count modulo four. -/
def q8FlipResidue (residue : Fin 4) : Language Q8Alphabet :=
  Language.inverseLetterMap q8FlipBit
    {word : Word Bool | word.count true % 4 = residue.1}

theorem mem_q8FlipResidue_iff (residue : Fin 4)
    (word : Word Q8Alphabet) :
    word ∈ q8FlipResidue residue ↔
      q8FlipCount word % 4 = residue.1 := by
  simp [q8FlipResidue, count_map_q8FlipBit]

theorem hasHeightAtMost_q8FlipResidue (residue : Fin 4) :
    HasHeightAtMost (q8FlipResidue residue) 1 := by
  exact (Counting.hasHeightAtMost_count (true : Bool) residue.2).inverseLetterMap
    q8FlipBit

/-- A fixed dihedral product fibre under the quaternion-to-dihedral letter
map.  No multiplicativity of the letter map is asserted. -/
def q8D4Fiber (target : D4Alphabet) : Language Q8Alphabet :=
  {word | (word.map q8ToD4).prod = target}

theorem mem_q8D4Fiber_iff (target : D4Alphabet)
    (word : Word Q8Alphabet) :
    word ∈ q8D4Fiber target ↔
      (word.map q8ToD4).prod = target := by
  rfl

theorem hasHeightAtMost_q8D4Fiber (target : D4Alphabet) :
    HasHeightAtMost (q8D4Fiber target) 1 := by
  let R : Recognition Q8Alphabet D4Alphabet :=
    { morphism := FreeMonoid.lift q8ToD4
      accepting := {target} }
  have h := heightOne_D4 Q8Alphabet R
  simpa [q8D4Fiber, R, Recognition.language,
    FreeMonoid.lift_ofList] using h

/-- The exact two-cell correction of the dihedral pullback. -/
def q8CorrectedD4Fiber : Language Q8Alphabet :=
  (q8FlipResidue ⟨0, by omega⟩ ∩ q8D4Fiber 1) ∪
    (q8FlipResidue ⟨2, by omega⟩ ∩
      q8D4Fiber (DihedralGroup.r (2 : ZMod 4)))

theorem fullIdentityFiber_q8_eq_correctedD4 :
    fullIdentityFiber Q8Alphabet = q8CorrectedD4Fiber := by
  ext word
  rw [mem_fullIdentityFiber_iff, q8_prod_eq_one_iff_correctedD4]
  simp only [q8CorrectedD4Fiber, Set.mem_union, Set.mem_inter_iff]
  rw [mem_q8FlipResidue_iff, mem_q8D4Fiber_iff,
    mem_q8FlipResidue_iff, mem_q8D4Fiber_iff]

theorem hasHeightAtMost_q8CorrectedD4Fiber :
    HasHeightAtMost q8CorrectedD4Fiber 1 :=
  ((hasHeightAtMost_q8FlipResidue ⟨0, by omega⟩).inter
      (hasHeightAtMost_q8D4Fiber 1)).union
    ((hasHeightAtMost_q8FlipResidue ⟨2, by omega⟩).inter
      (hasHeightAtMost_q8D4Fiber (DihedralGroup.r (2 : ZMod 4))))

/-- The full-alphabet identity fibre of `Q₈` has generalized star height at
most one. -/
theorem heightOne_fullIdentityFiber_Q8 :
    HasHeightAtMost (fullIdentityFiber (QuaternionGroup 2)) 1 :=
  hasHeightAtMost_q8CorrectedD4Fiber.congr
    fullIdentityFiber_q8_eq_correctedD4.symm

/-- Every language recognized by `Q₈`, over every finite alphabet and every
accepting subset, has generalized star height at most one. -/
theorem heightOne_Q8 : HeightOneForGroup (QuaternionGroup 2) :=
  heightOneForGroup_of_fullIdentityFiber heightOne_fullIdentityFiber_Q8

end GSH
