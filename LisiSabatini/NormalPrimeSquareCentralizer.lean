module

public import LisiSabatini.SectionConstructionCore
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Centralizers of normal subgroups of prime-squared order

Let `N` be a normal subgroup of a finite `p`-group `G`, with
`|N| = p ^ 2`.  Conjugation induces a `p`-subgroup of `Aut(N)`.
If `N` is cyclic, the order of `Aut(N)` is `p * (p - 1)`.  Otherwise
`N` has exponent `p`, hence is a two-dimensional vector space over
`ZMod p`; its automorphism group is `GL₂(p)`, whose order contains only
one factor of `p`.  In either case the conjugation image has order at
most `p`, so the centralizer of `N` has index at most `p`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open Subgroup

open scoped IsMulCommutative

/-! ## Elementary arithmetic for the two automorphism groups -/

/-- A `p`-power dividing `p * (p - 1)` has exponent at most one. -/
private theorem pow_exponent_le_one_of_dvd_prime_mul_pred
    {p k : ℕ} (hp : p.Prime) (hdiv : p ^ k ∣ p * (p - 1)) :
    k ≤ 1 := by
  by_contra hk
  have hk2 : 2 ≤ k := by omega
  have hpSqDvdPow : p ^ 2 ∣ p ^ k := pow_dvd_pow p hk2
  have hpSqDvd : p ^ 2 ∣ p * (p - 1) := hpSqDvdPow.trans hdiv
  have hpDvdPred : p ∣ p - 1 := by
    rw [pow_two] at hpSqDvd
    exact (Nat.mul_dvd_mul_iff_left hp.pos).mp hpSqDvd
  have hpPredPos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have := Nat.le_of_dvd hpPredPos hpDvdPred
  omega

/-- A `p`-power dividing the order of `GL₂(p)` has exponent at most one. -/
private theorem pow_exponent_le_one_of_dvd_glTwo_order
    {p k : ℕ} (hp : p.Prime)
    (hdiv : p ^ k ∣ (p ^ 2 - 1) * (p ^ 2 - p)) :
    k ≤ 1 := by
  by_contra hk
  have hk2 : 2 ≤ k := by omega
  have hpSqDvdPow : p ^ 2 ∣ p ^ k := pow_dvd_pow p hk2
  have hpSqDvdProduct :
      p ^ 2 ∣ (p ^ 2 - 1) * (p ^ 2 - p) :=
    hpSqDvdPow.trans hdiv
  have hcoprime : (p ^ 2).Coprime (p ^ 2 - 1) := by
    apply (Nat.coprime_self_sub_right
      (show 1 ≤ p ^ 2 from one_le_pow₀ hp.one_le)).mpr
    exact Nat.coprime_one_right _
  have hpSqDvdSecond : p ^ 2 ∣ p ^ 2 - p :=
    hcoprime.dvd_of_dvd_mul_left hpSqDvdProduct
  have hsecond : p ^ 2 - p = p * (p - 1) := by
    rw [pow_two, Nat.mul_sub_left_distrib]
    simp
  rw [hsecond, pow_two] at hpSqDvdSecond
  have hpDvdPred : p ∣ p - 1 :=
    (Nat.mul_dvd_mul_iff_left hp.pos).mp hpSqDvdSecond
  have hpPredPos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have := Nat.le_of_dvd hpPredPos hpDvdPred
  omega

/-! ## Kernel of normal conjugation -/

/-- The kernel of conjugation on a normal subgroup is its pointwise
centralizer in the ambient group. -/
theorem ker_conjNormal_eq_centralizer
    {G : Type*} [Group G] (N : Subgroup G) (hN : N.Normal) :
    letI : N.Normal := hN
    (MulAut.conjNormal : G →* MulAut N).ker =
      Subgroup.centralizer (N : Set G) := by
  let : N.Normal := hN
  let conjN : G →* MulAut N := MulAut.conjNormal
  ext g
  simp only [MonoidHom.mem_ker]
  constructor
  · intro hg n hn
    have heval := DFunLike.congr_fun hg ⟨n, hn⟩
    have heval' := congrArg Subtype.val heval
    have hconj : g * n * g⁻¹ = n := by
      simpa only [conjN, MulAut.conjNormal_apply,
        MulAut.one_apply] using heval'
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  · intro hg
    apply MulEquiv.ext
    intro n
    apply Subtype.ext
    simpa only [conjN, MulAut.conjNormal_apply,
      MulAut.one_apply] using
        (mul_inv_eq_of_eq_mul (hg n n.2).symm)

/-! ## The cyclic branch -/

/-- In the cyclic order-`p²` branch, the normal conjugation image has
cardinality at most `p`. -/
private theorem natCard_conjNormal_range_le_prime_of_isCyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (N : Subgroup G) (hN : N.Normal)
    (hcard : Nat.card N = p ^ 2) (hcyclic : IsCyclic N) :
    letI : N.Normal := hN
    Nat.card (MulAut.conjNormal : G →* MulAut N).range ≤ p := by
  let : Fact p.Prime := ⟨hp⟩
  let : N.Normal := hN
  let : IsCyclic N := hcyclic
  let conjN : G →* MulAut N := MulAut.conjNormal
  have hRangeP : IsPGroup p conjN.range :=
    hGp.of_surjective conjN.rangeRestrict conjN.rangeRestrict_surjective
  obtain ⟨k, hkcard⟩ := IsPGroup.iff_card.mp hRangeP
  have hdivAut : Nat.card conjN.range ∣ Nat.card (MulAut N) :=
    conjN.range.card_subgroup_dvd_card
  have hAutCard : Nat.card (MulAut N) = p * (p - 1) := by
    rw [IsCyclic.card_mulAut, hcard]
    simpa using Nat.totient_prime_pow hp (show 0 < 2 by omega)
  have hkdiv : p ^ k ∣ p * (p - 1) := by
    rw [← hkcard, ← hAutCard]
    exact hdivAut
  have hkle : k ≤ 1 :=
    pow_exponent_le_one_of_dvd_prime_mul_pred hp hkdiv
  rw [hkcard]
  simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hkle

/-! ## The elementary-abelian branch -/

/-- Cardinality of the linear-map model of `GL₂(p)`. -/
private theorem natCard_linearGeneralLinearTwo_zmod
    (p : ℕ) (hp : p.Prime) :
    Nat.card
        (LinearMap.GeneralLinearGroup (ZMod p) (Fin 2 → ZMod p)) =
      (p ^ 2 - 1) * (p ^ 2 - p) := by
  let : Fact p.Prime := ⟨hp⟩
  calc
    Nat.card
        (LinearMap.GeneralLinearGroup (ZMod p) (Fin 2 → ZMod p)) =
        Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)) :=
      (Nat.card_congr Matrix.GeneralLinearGroup.toLin.toEquiv).symm
    _ = (p ^ 2 - 1) * (p ^ 2 - p) := by
      simpa [ZMod.card, Fin.prod_univ_two] using
        (Matrix.card_GL_field (𝔽 := ZMod p) 2)

/-- In the noncyclic order-`p²` branch, normal conjugation is a
two-dimensional linear action and its image has cardinality at most `p`. -/
private theorem natCard_coordinateConjugation_range_le_prime_of_not_isCyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (N : Subgroup G) (hN : N.Normal)
    (hcard : Nat.card N = p ^ 2) (hnotCyclic : ¬ IsCyclic N) :
    ∃ S : ElementaryAbelianSection G,
      S.N = N ∧ S.r = p ∧ S.d = 2 ∧
        Nat.card S.conjugation.range ≤ p := by
  let : Fact p.Prime := ⟨hp⟩
  let : IsMulCommutative N :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hcard
  have hexponent : Monoid.exponent N = p :=
    (not_isCyclic_iff_exponent_eq_prime hp hcard).mp hnotCyclic
  have hpow : ∀ x : N, x ^ p = 1 := by
    intro x
    rw [← hexponent]
    exact Monoid.pow_exponent_eq_one x
  let zmodModule : Module (ZMod p) (Additive N) :=
    AddCommGroup.zmodModule fun x ↦ by
      simpa using congrArg Additive.ofMul (hpow x.toMul)
  let finiteModule : Module.Finite (ZMod p) (Additive N) :=
    Module.Finite.of_finite
  let freeModule : Module.Free (ZMod p) (Additive N) :=
    @Module.Free.of_divisionRing (ZMod p) (Additive N)
      (inferInstance) (inferInstance) zmodModule
  have hfinrank : Module.finrank (ZMod p) (Additive N) = 2 := by
    apply Nat.pow_right_injective hp.two_le
    calc
      p ^ Module.finrank (ZMod p) (Additive N) =
          Nat.card (Additive N) := by
        rw [@Module.natCard_eq_pow_finrank
          (ZMod p) (Additive N) (inferInstance) (inferInstance)
          zmodModule finiteModule, Nat.card_zmod]
      _ = Nat.card N := Nat.card_congr Additive.ofMul
      _ = p ^ 2 := hcard
  let basis : Module.Basis (Fin 2) (ZMod p) (Additive N) :=
    @Module.finBasisOfFinrankEq (ZMod p) (Additive N)
      (inferInstance) (inferInstance) zmodModule freeModule
      (inferInstance) finiteModule 2 hfinrank
  let coordinates : Additive N ≃+ (Fin 2 → ZMod p) :=
    basis.equivFun.toAddEquiv
  let S : ElementaryAbelianSection G :=
    ElementaryAbelianSection.ofCoordinates N hN p 2 hp coordinates
  let : Finite S.conjugation.range :=
    Finite.of_surjective S.conjugation.rangeRestrict
      S.conjugation.rangeRestrict_surjective
  have hRangeP : IsPGroup p S.conjugation.range :=
    hGp.of_surjective S.conjugation.rangeRestrict
      S.conjugation.rangeRestrict_surjective
  obtain ⟨k, hkcard⟩ := IsPGroup.iff_card.mp hRangeP
  have hdivGL :
      Nat.card S.conjugation.range ∣
        Nat.card
          (LinearMap.GeneralLinearGroup (ZMod p) (Fin 2 → ZMod p)) :=
    S.conjugation.range.card_subgroup_dvd_card
  have hkdiv : p ^ k ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
    rw [← hkcard, ← natCard_linearGeneralLinearTwo_zmod p hp]
    exact hdivGL
  have hkle : k ≤ 1 :=
    pow_exponent_le_one_of_dvd_glTwo_order hp hkdiv
  refine ⟨S, rfl, rfl, rfl, ?_⟩
  rw [hkcard]
  simpa only [pow_one] using Nat.pow_le_pow_right hp.pos hkle

/-! ## Centralizer index -/

/-- A normal subgroup of order `p²` in a finite `p`-group has pointwise
centralizer of index at most `p`. -/
theorem centralizer_index_le_prime_of_normal_natCard_eq_prime_sq
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (N : Subgroup G) (hN : N.Normal)
    (hcard : Nat.card N = p ^ 2) :
    (Subgroup.centralizer (N : Set G)).index ≤ p := by
  by_cases hcyclic : IsCyclic N
  · let : N.Normal := hN
    let conjN : G →* MulAut N := MulAut.conjNormal
    rw [← ker_conjNormal_eq_centralizer N hN,
      Subgroup.index_ker]
    exact natCard_conjNormal_range_le_prime_of_isCyclic
      hp hGp N hN hcard hcyclic
  · obtain ⟨S, hSN, _hSr, _hSd, hRange⟩ :=
      natCard_coordinateConjugation_range_le_prime_of_not_isCyclic
        hp hGp N hN hcard hcyclic
    have hker : S.conjugation.ker =
        Subgroup.centralizer (N : Set G) := by
      ext g
      rw [← hSN]
      exact S.mem_conjugation_ker_iff_mem_centralizer g
    rw [← hker, Subgroup.index_ker]
    exact hRange

end LisiSabatini
