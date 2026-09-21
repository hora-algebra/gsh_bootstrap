import GSH.Groups.SmallOrder
import GSH.Results.A4FullAlphabet
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The group-theoretic order-twelve fork

This file isolates the only classification needed above order eleven.  Four
Sylow `3`-subgroups give the faithful conjugation action on four points and
hence identify the group with `A₄`.  The unique-Sylow branch is treated below
by constructing a commutative subgroup of index two.
-/

set_option autoImplicit false

namespace GSH
namespace OrderTwelveClassification

universe u v

noncomputable section

variable {G : Type v} [Group G] [Fintype G]

/-- If an order-twelve group has four Sylow `3`-subgroups, conjugation on
those four subgroups identifies it with `A₄`. -/
theorem mulEquiv_A4_of_card_sylow_three_eq_four
    (hcard : Nat.card G = 12)
    (hSylow : Nat.card (Sylow 3 G) = 4) : Nonempty (G ≃* A4) := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let X := Sylow 3 G
  let f : G →* Equiv.Perm X := MulAction.toPermHom G X
  have hXcard : Nat.card X = 4 := hSylow
  letI : MulAction.IsPretransitive f.range X :=
    MulAction.IsPretransitive.of_smul_eq
      (fun g : G => (⟨f g, ⟨g, rfl⟩⟩ : f.range)) (by intros; rfl)
  have hfour_dvd_range : 4 ∣ Nat.card f.range := by
    let x : X := default
    rw [← hXcard, ← MulAction.index_stabilizer_of_transitive f.range x]
    exact (MulAction.stabilizer f.range x).index_dvd_card
  have hker_mul_range : Nat.card f.ker * Nat.card f.range = 12 := by
    have hmul := f.ker.card_mul_index
    rw [Subgroup.index_ker, hcard] at hmul
    exact hmul
  have hker_pos : 0 < Nat.card f.ker := Nat.card_pos
  have hrange_pos : 0 < Nat.card f.range := Nat.card_pos
  have hrange_ge : 4 ≤ Nat.card f.range :=
    Nat.le_of_dvd hrange_pos hfour_dvd_range
  have hker_le : Nat.card f.ker ≤ 3 := by nlinarith [hker_mul_range]
  have hker : Nat.card f.ker = 1 := by
    have hcases : Nat.card f.ker = 1 ∨ Nat.card f.ker = 2 ∨
        Nat.card f.ker = 3 := by omega
    rcases hcases with h1 | h2 | h3
    · exact h1
    · have hrange : Nat.card f.range = 6 := by nlinarith [hker_mul_range]
      rw [hrange] at hfour_dvd_range
      norm_num at hfour_dvd_range
    · have hrange : Nat.card f.range = 4 := by nlinarith [hker_mul_range]
      have hindexKer : f.ker.index = 4 := by
        rw [Subgroup.index_ker]
        exact hrange
      have hPgroup : IsPGroup 3 f.ker :=
        IsPGroup.of_card (n := 1) (by norm_num; exact h3)
      have hnotdvd : ¬3 ∣ f.ker.index := by rw [hindexKer]; norm_num
      let Q : Sylow 3 G := hPgroup.toSylow hnotdvd
      have hQnormal : Q.Normal := by
        change f.ker.Normal
        infer_instance
      letI : Q.Normal := hQnormal
      letI : Unique (Sylow 3 G) := Sylow.unique_of_normal Q hQnormal
      have hone : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
      omega
  have hf : Function.Injective f :=
    f.ker_eq_bot_iff.mp (f.ker.eq_bot_of_card_eq hker)
  have hrangeCard : Nat.card f.range = 12 := by
    rw [← hcard]
    exact Nat.card_congr (f.ofInjective hf).symm.toEquiv
  have hpermCard : Nat.card (Equiv.Perm X) = 24 := by
    rw [Nat.card_perm, hXcard]
    norm_num [Nat.factorial]
  have hrangeIndex : f.range.index = 2 := by
    have hmul := f.range.card_mul_index
    rw [hrangeCard, hpermCard] at hmul
    omega
  letI : DecidableEq X := Classical.decEq X
  have hrangeEq : f.range = alternatingGroup X :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hrangeIndex
  have hXFintype : Fintype.card X = 4 := by
    simpa [Nat.card_eq_fintype_card] using hXcard
  let eX : X ≃ Fin 4 := Fintype.equivFinOfCardEq hXFintype
  exact ⟨(f.ofInjective hf).trans
    ((MulEquiv.subgroupCongr hrangeEq).trans eX.altCongrHom)⟩

/-- A central subgroup of order three inside a group of order six forces
commutativity. -/
private theorem commutative_of_card_six_of_central_three
    (C : Subgroup G) (K : Subgroup C)
    (hCcard : Nat.card C = 6) (hKcard : Nat.card K = 3)
    (hKcenter : K ≤ Subgroup.center C) :
    ∀ a b : C, a * b = b * a := by
  letI : K.Normal :=
    ⟨fun n hn g => by
      have hc := Subgroup.mem_center_iff.mp (hKcenter hn) g
      simpa [hc] using hn⟩
  have hquotCard : Nat.card (C ⧸ K) = 2 := by
    have hmul := K.card_eq_card_quotient_mul_card_subgroup
    rw [hCcard, hKcard] at hmul
    omega
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclic (C ⧸ K) := isCyclic_of_prime_card hquotCard
  exact (QuotientGroup.mk' K).isMulCommutative_of_isCyclic_of_ker_le_center
    (by simpa using hKcenter) |>.is_comm.comm

/-- If the Sylow `3`-subgroup is unique, an order-twelve group has a
commutative subgroup of index two. -/
theorem exists_commutative_index_two_of_card_sylow_three_eq_one
    (hcard : Nat.card G = 12)
    (hSylow : Nat.card (Sylow 3 G) = 1) :
    ∃ H : Subgroup G, H.index = 2 ∧ ∀ a b : H, a * b = b * a := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := default
  have hPcard : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hcard]
    rw [show 12 = 3 * 4 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [show 4 = 2 * 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.prime_three.factorization, Nat.prime_two.factorization]
    norm_num
  letI : IsCyclic P := isCyclic_of_prime_card hPcard
  have hPcomm : ∀ a b : P, a * b = b * a :=
    (inferInstance : IsMulCommutative P).is_comm.comm
  letI : Subsingleton (Sylow 3 G) := by
    rw [← Fintype.card_le_one_iff_subsingleton,
      ← Nat.card_eq_fintype_card, hSylow]
  have hPnormal : P.Normal := Sylow.normal_of_subsingleton P
  letI : P.Normal := hPnormal
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  have hP_le_C : P.1 ≤ C := by
    intro x hx y hy
    exact congrArg Subtype.val (hPcomm ⟨y, hy⟩ ⟨x, hx⟩)
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  have hNtop : N = ⊤ := Subgroup.normalizer_eq_top_iff.mpr hPnormal
  let action : N →* MulAut P := P.1.normalizerMonoidHom
  have hAutCard : Nat.card (MulAut P) = 2 := by
    rw [IsCyclic.card_mulAut, hPcard, Nat.totient_prime Nat.prime_three]
  have hrangeDvd : Nat.card action.range ∣ 2 := by
    rw [← hAutCard]
    exact action.range.card_subgroup_dvd_card
  have hrangePos : 0 < Nat.card action.range := Nat.card_pos
  have hrangeCases : Nat.card action.range = 1 ∨ Nat.card action.range = 2 := by
    exact (Nat.dvd_prime Nat.prime_two).mp hrangeDvd
  have hCindex : C.index = Nat.card action.range := by
    have hrel : C.relIndex N = Nat.card action.range := by
      have hker : C.subgroupOf N = action.ker := by
        dsimp [C, N, action]
        simpa only [Sylow.coe_coe] using P.1.normalizerMonoidHom_ker.symm
      rw [Subgroup.relIndex, hker, Subgroup.index_ker]
    simpa [hNtop, C] using hrel
  rcases hrangeCases with hrangeOne | hrangeTwo
  · have hCtop : C = ⊤ := Subgroup.index_eq_one.mp (by omega)
    have hPcenter : P.1 ≤ Subgroup.center G := by
      exact (Subgroup.centralizer_eq_top_iff_subset.mp hCtop)
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime
      (G := G) 2 (n := 1) (by rw [hcard]; norm_num)
    have hKcardTwo : Nat.card K = 2 := by simpa using hKcard
    letI : CommGroup P :=
      { (inferInstance : Group P) with mul_comm := hPcomm }
    have hKcomm : ∀ a b : K, a * b = b * a := by
      letI := isCyclic_of_prime_card (α := K) (p := 2) hKcardTwo
      exact (inferInstance : IsMulCommutative K).is_comm.comm
    letI : CommGroup K :=
      { (inferInstance : Group K) with mul_comm := hKcomm }
    let productHom : P × K →* G :=
      { toFun := fun pair => pair.1.1 * pair.2.1
        map_one' := by simp
        map_mul' := by
          intro a b
          change (a.1.1 * b.1.1) * (a.2.1 * b.2.1) =
            (a.1.1 * a.2.1) * (b.1.1 * b.2.1)
          have hc := Subgroup.mem_center_iff.mp (hPcenter b.1.2) a.2.1
          calc
            (a.1.1 * b.1.1) * (a.2.1 * b.2.1) =
                a.1.1 * (b.1.1 * a.2.1) * b.2.1 := by group
            _ = a.1.1 * (a.2.1 * b.1.1) * b.2.1 := by rw [hc]
            _ = (a.1.1 * a.2.1) * (b.1.1 * b.2.1) := by group }
    have hdisjoint : Disjoint P.1 K :=
      Subgroup.disjoint_of_coprime_natCard (by
        rw [hPcard, hKcardTwo]
        norm_num)
    have hproductInj : Function.Injective productHom :=
      Subgroup.mul_injective_of_disjoint hdisjoint
    let H : Subgroup G := productHom.range
    have hHcard : Nat.card H = 6 := by
      calc
        Nat.card H = Nat.card (P × K) :=
          Nat.card_congr (productHom.ofInjective hproductInj).symm.toEquiv
        _ = Nat.card P * Nat.card K := Nat.card_prod P K
        _ = 6 := by rw [hPcard, hKcardTwo]
    have hHindex : H.index = 2 := by
      have hmul := H.card_mul_index
      rw [hHcard, hcard] at hmul
      omega
    refine ⟨H, hHindex, ?_⟩
    intro a b
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    change a.1 * b.1 = b.1 * a.1
    rw [← hx, ← hy, ← map_mul, mul_comm x y, map_mul]
  · have hCindexTwo : C.index = 2 := by omega
    have hCcard : Nat.card C = 6 := by
      have hmul := C.card_mul_index
      rw [hCindexTwo, hcard] at hmul
      omega
    let K : Subgroup C := P.1.subgroupOf C
    have hKcard : Nat.card K = 3 := by
      rw [← hPcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP_le_C).toEquiv
    have hKcenter : K ≤ Subgroup.center C := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (y.2 x.1 hx).symm
    exact ⟨C, hCindexTwo,
      commutative_of_card_six_of_central_three C K hCcard hKcard hKcenter⟩

/-- For a group of order twelve the number of Sylow `3`-subgroups is exactly
one or four. -/
theorem card_sylow_three_eq_one_or_four (hcard : Nat.card G = 12) :
    Nat.card (Sylow 3 G) = 1 ∨ Nat.card (Sylow 3 G) = 4 := by
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := default
  have hPcard : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hcard]
    rw [show 12 = 3 * 4 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num)]
    rw [show 4 = 2 * 2 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Nat.prime_three.factorization, Nat.prime_two.factorization]
    norm_num
  have hPindex : P.1.index = 4 := by
    have hmul := P.1.card_mul_index
    rw [hPcard, hcard] at hmul
    omega
  have hdvd : Nat.card (Sylow 3 G) ∣ 4 := by
    rw [← hPindex]
    exact P.card_dvd_index
  have hpos : 0 < Nat.card (Sylow 3 G) := Nat.card_pos
  have hle : Nat.card (Sylow 3 G) ≤ 4 := Nat.le_of_dvd (by omega) hdvd
  have hmod := card_sylow_modEq_one 3 G
  interval_cases h : Nat.card (Sylow 3 G)
  all_goals simp_all [Nat.ModEq]

/-- Every group of order exactly twelve has the height-one property. -/
theorem heightOne_of_card_twelve (G : Type v) [Group G] [Fintype G]
    (hcard : Fintype.card G = 12) : HeightOneForGroup.{u, v} G := by
  have hnat : Nat.card G = 12 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  rcases card_sylow_three_eq_one_or_four hnat with hone | hfour
  · obtain ⟨H, hindex, hcomm⟩ :=
      exists_commutative_index_two_of_card_sylow_three_eq_one hnat hone
    exact IndexTwoEmbedding.heightOne_of_commutative_index_two H hindex hcomm
  · obtain ⟨e⟩ := mulEquiv_A4_of_card_sylow_three_eq_four hnat hfour
    exact HeightOneForGroup.of_mulEquiv e
      A4FullAlphabet.heightOneForGroup_A4

/-- **Every language recognized by a finite group of order at most twelve has
generalized star height at most one.** -/
theorem heightOneUpTo_twelve : HeightOneUpTo.{u, v} 12 := by
  intro G _ _ hle
  by_cases hcard : Fintype.card G = 12
  · exact heightOne_of_card_twelve G hcard
  · exact heightOneUpTo_eleven G (by omega)

end
end OrderTwelveClassification

universe u v

/-- **Every language recognized by a finite group of order at most twelve has
generalized star height at most one.** -/
theorem heightOneUpTo_twelve : HeightOneUpTo.{u, v} 12 :=
  OrderTwelveClassification.heightOneUpTo_twelve

end GSH
