import LisiSabatini.HallBergerExtraspecialExtension
import LisiSabatini.HobbyFrattiniTheoremCore
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The residual factor in the Hall--Berger decomposition

This file isolates the classification-free step needed at the end of the
Berger--Kovács--Newman central-product argument.  A finite `2`-group whose
derived subgroup is central of order two, whose center is cyclic, and whose
involutions are central is already extraspecial.

The point is to avoid invoking the classification of finite `2`-groups with
a unique involution.  If the cyclic center had order greater than two, its
unique involution would be a square.  Quotienting by the central subgroup of
central squares then produces an abelian `2`-group with at most two elements
killed by squaring, hence a cyclic group.  The original group would therefore
be commutative, contradicting that its derived subgroup has order two.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- A finite `2`-group with central derived subgroup of order two and cyclic
center is extraspecial as soon as every element whose square is one is
central.  This is the classification-free residual-factor step in the
Hall--Berger proof. -/
theorem isExtraspecial_of_cyclicCenter_of_squareOne_mem_center
    {D : Type u} [Group D] [Finite D]
    (hD2 : IsPGroup 2 D)
    (hD : HasCentralCommutatorOfOrderTwo D)
    (hZcyclic : IsCyclic (Subgroup.center D))
    (hinv : ∀ x : D, x ^ 2 = 1 → x ∈ Subgroup.center D) :
    IsExtraspecial 2 D := by
  let Z : Subgroup D := Subgroup.center D
  letI : IsCyclic Z := hZcyclic
  let R : Subgroup Z := (powMonoidHom 2 : Z →* Z).range
  let S : Subgroup D := R.map Z.subtype
  have htwoDvdZ : 2 ∣ Nat.card Z := by
    rw [← hD.card_commutator]
    exact Subgroup.card_dvd_of_le hD.commutator_le_center
  have hgcd : (Nat.card Z).gcd 2 = 2 :=
    Nat.gcd_eq_right_iff_dvd.mpr htwoDvdZ
  have hRindex : R.index = 2 := by
    simpa only [R, hgcd] using
      (IsCyclic.index_powMonoidHom_range Z 2)
  have hScenter : S ≤ Subgroup.center D := by
    rintro x ⟨z, _hz, rfl⟩
    exact z.2
  letI : S.Normal :=
    { conj_mem := fun x hx g => by
        have hxc : x ∈ Subgroup.center D := hScenter hx
        have hxg : g * x = x * g :=
          Subgroup.mem_center_iff.mp hxc g
        rw [hxg]
        simpa only [mul_inv_cancel_right] using hx }
  by_cases hZle : Nat.card Z ≤ 2
  · have hZge : 2 ≤ Nat.card Z :=
      Nat.le_of_dvd Nat.card_pos htwoDvdZ
    exact hD.isExtraspecial_of_card_center hD2
      (Nat.le_antisymm hZle hZge)
  · have hZgt : 2 < Nat.card Z := Nat.lt_of_not_ge hZle
    have hRcardMul : Nat.card R * 2 = Nat.card Z := by
      simpa only [hRindex] using R.card_mul_index
    have hRcardGt : 1 < Nat.card R := by omega
    have hR2 : IsPGroup 2 R :=
      (hD2.to_subgroup Z).to_subgroup R
    have htwoDvdR : 2 ∣ Nat.card R := by
      rcases hR2.card_eq_or_dvd with hcard | hdvd
      · omega
      · exact hdvd
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨r, hrOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := R) 2 htwoDvdR
    have hrSqR : r ^ 2 = 1 := by
      rw [← hrOrder]
      exact pow_orderOf_eq_one r
    have hrSqZ : (r : Z) ^ 2 = 1 :=
      congrArg Subtype.val hrSqR
    have hrNeZ : (r : Z) ≠ 1 := by
      intro hr
      have hrR : r = 1 := Subtype.ext hr
      rw [hrR, orderOf_one] at hrOrder
      norm_num at hrOrder
    have hcommLeS : commutator D ≤ S := by
      intro c hc
      by_cases hcOne : c = 1
      · simpa only [hcOne] using S.one_mem
      · let c' : commutator D := ⟨c, hc⟩
        have hcSqComm : c' ^ 2 = 1 := by
          have hpow :
              c' ^ Nat.card (commutator D) = 1 :=
            pow_card_eq_one'
          simpa only [hD.card_commutator] using hpow
        have hcSqD : c ^ 2 = 1 :=
          congrArg Subtype.val hcSqComm
        let cZ : Z := ⟨c, hD.commutator_le_center hc⟩
        have hcSqZ : cZ ^ 2 = 1 := by
          apply Subtype.ext
          exact hcSqD
        have hcNeZ : cZ ≠ 1 := by
          intro h
          exact hcOne (congrArg Subtype.val h)
        have hcr : cZ = (r : Z) :=
          eq_of_sq_eq_one_of_ne_one_of_isCyclic hZcyclic
            hcSqZ hrSqZ hcNeZ hrNeZ
        apply Subgroup.mem_map.mpr
        exact ⟨(r : Z), r.2, congrArg Subtype.val hcr.symm⟩
    let A := D ⧸ S
    have hAcomm :
        Std.Commutative (· * · : A → A → A) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
        hcommLeS
    let groupA : Group A := inferInstance
    letI : CommGroup A :=
      { groupA with mul_comm := hAcomm.comm }
    have hA2 : IsPGroup 2 A := hD2.to_quotient S
    let f : Z →* A :=
      (QuotientGroup.mk' S).comp Z.subtype
    have hRker : R ≤ f.ker := by
      intro z hz
      rw [MonoidHom.mem_ker]
      change QuotientGroup.mk' S (z : D) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    have hRangeCard : Nat.card f.range ≤ 2 := by
      rw [← Subgroup.index_ker f]
      exact Nat.le_of_dvd (by norm_num)
        (hRindex ▸ Subgroup.index_dvd_of_le hRker)
    have hKernelLeRange :
        (powMonoidHom 2 : A →* A).ker ≤ f.range := by
      intro a ha
      obtain ⟨x, hx⟩ :=
        QuotientGroup.mk'_surjective S a
      have haSq : a ^ 2 = 1 :=
        MonoidHom.mem_ker.mp ha
      have hxSqS : x ^ 2 ∈ S := by
        rw [← QuotientGroup.eq_one_iff]
        change QuotientGroup.mk' S (x ^ 2) = 1
        rw [map_pow, hx, haSq]
      rcases hxSqS with ⟨z, hzR, hzx⟩
      rcases hzR with ⟨w, hw⟩
      have hxSq :
          x ^ 2 = (w : D) ^ 2 := by
        have hw' : w ^ 2 = z := by
          simpa only [powMonoidHom_apply] using hw
        calc
          x ^ 2 = (z : D) := hzx.symm
          _ = (w ^ 2 : Z) := by rw [hw']
          _ = (w : D) ^ 2 := rfl
      let y : D := x * (w : D)⁻¹
      have hxw : Commute x (w : D) :=
        Subgroup.mem_center_iff.mp w.2 x
      have hySq : y ^ 2 = 1 := by
        have hpow := hxw.inv_right.mul_pow 2
        dsimp only [y]
        rw [hpow, hxSq]
        group
      have hyCenter : y ∈ Subgroup.center D :=
        hinv y hySq
      have hxEq : x = y * (w : D) := by
        dsimp only [y]
        group
      have hxCenter : x ∈ Subgroup.center D := by
        rw [hxEq]
        exact (Subgroup.center D).mul_mem hyCenter w.2
      apply MonoidHom.mem_range.mpr
      refine ⟨⟨x, hxCenter⟩, ?_⟩
      simpa only [f, MonoidHom.comp_apply, Subgroup.coe_subtype] using hx
    have hKernelCard :
        Nat.card (powMonoidHom 2 : A →* A).ker ≤ 2 :=
      (Subgroup.card_le_of_le hKernelLeRange).trans hRangeCard
    have hAcyclic : IsCyclic A :=
      isCyclic_of_isPGroup_of_natCard_primeKernel_le_prime
        Nat.prime_two hA2 hKernelCard
    letI : IsCyclic A := hAcyclic
    have hDcomm : ∀ x y : D, x * y = y * x :=
      commutative_of_cyclic_center_quotient
        (QuotientGroup.mk' S) (by
          rw [QuotientGroup.ker_mk']
          exact hScenter)
    have hcenterTop : Subgroup.center D = ⊤ := by
      ext x
      simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
      intro y
      exact hDcomm y x
    have hcommBot : commutator D = ⊥ :=
      (commutator_eq_bot_iff_center_eq_top D).mpr hcenterTop
    have hcommCard : Nat.card (commutator D) = 1 := by
      rw [hcommBot, Subgroup.card_bot]
    rw [hD.card_commutator] at hcommCard
    omega

end LisiSabatini
