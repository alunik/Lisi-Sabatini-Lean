module

public import LisiSabatini.SylowPairQuadraticBound
public import Mathlib.Data.Real.Basic

/-!
# A trivial intersection gives a whole good double coset

If P and gQg⁻¹ meet trivially, every element of PgQ is a good conjugator.
The product parametrization P × Q → PgQ is injective, so there are at least
|P||Q| good conjugators. No enumeration of the ambient group is required.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace LisiSabatini

universe uG

private theorem mem_conjugate_sylow_iff
    {G : Type uG} [Group G] {p : ℕ} (Q : Sylow p G) (x z : G) :
    z ∈ ((x • Q : Sylow p G) : Subgroup G) ↔
      x⁻¹ * z * x ∈ (Q : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (MulAut.conj x)⁻¹ z ∈ (Q : Subgroup G) ↔ _
  rw [MulAut.conj_inv_apply]

/-- Every element of a good double coset is a good conjugator. -/
theorem mixedSylowInter_double_coset_eq_bot
    {G : Type uG} [Group G] {p : ℕ}
    (P Q : Sylow p G) {g : G} (hg : mixedSylowInter P Q g = ⊥)
    (a : P) (b : Q) :
    mixedSylowInter P Q ((a : G) * g * (b : G)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro z hz
  apply Subgroup.mem_bot.mpr
  have hzP : z ∈ (P : Subgroup G) := hz.1
  have hzQ := (mem_conjugate_sylow_iff Q _ z).mp hz.2
  have hyP : (a : G)⁻¹ * z * (a : G) ∈ (P : Subgroup G) :=
    P.mul_mem (P.mul_mem (P.inv_mem a.property) hzP) a.property
  have hyQ : g⁻¹ * ((a : G)⁻¹ * z * (a : G)) * g ∈ (Q : Subgroup G) := by
    have h := Q.mul_mem (Q.mul_mem b.property hzQ) (Q.inv_mem b.property)
    convert h using 1
    group
  have hy : (a : G)⁻¹ * z * (a : G) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hg]
    exact ⟨hyP, (mem_conjugate_sylow_iff Q g _).mpr hyQ⟩
  calc
    z = (a : G) * ((a : G)⁻¹ * z * (a : G)) * (a : G)⁻¹ := by group
    _ = 1 := by rw [hy]; group

/-- A trivial mixed intersection makes the double-coset parametrization
injective. -/
theorem doubleCosetMap_injective_of_mixedSylowInter_eq_bot
    {G : Type uG} [Group G] {p : ℕ}
    (P Q : Sylow p G) {g : G} (hg : mixedSylowInter P Q g = ⊥) :
    Function.Injective (fun ab : P × Q ↦ (ab.1 : G) * g * (ab.2 : G)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  change (a : G) * g * (b : G) = (c : G) * g * (d : G) at heq
  have hyP : (c : G)⁻¹ * (a : G) ∈ (P : Subgroup G) :=
    P.mul_mem (P.inv_mem c.property) a.property
  have hyQ : g⁻¹ * ((c : G)⁻¹ * (a : G)) * g ∈ (Q : Subgroup G) := by
    have hcalc : g⁻¹ * ((c : G)⁻¹ * (a : G)) * g = (d : G) * (b : G)⁻¹ := by
      calc
        _ = g⁻¹ * (c : G)⁻¹ * ((a : G) * g * (b : G)) * (b : G)⁻¹ := by group
        _ = g⁻¹ * (c : G)⁻¹ * ((c : G) * g * (d : G)) * (b : G)⁻¹ := by rw [heq]
        _ = _ := by group
    rw [hcalc]
    exact Q.mul_mem d.property (Q.inv_mem b.property)
  have hy : (c : G)⁻¹ * (a : G) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hg]
    exact ⟨hyP, (mem_conjugate_sylow_iff Q g _).mpr hyQ⟩
  have hac : a = c := Subtype.ext (inv_mul_eq_one.mp hy).symm
  subst c
  have hbd : b = d := Subtype.ext (mul_left_cancel heq)
  exact Prod.ext rfl hbd

/-- One trivial intersection supplies at least |P||Q| good conjugators. -/
theorem card_mul_card_le_good_conjugators
    {G : Type uG} [Group G] [Finite G] {p : ℕ}
    (P Q : Sylow p G) {g : G} (hg : mixedSylowInter P Q g = ⊥) :
    Nat.card P * Nat.card Q ≤ {x : G | mixedSylowInter P Q x = ⊥}.ncard := by
  let f : P × Q → ↥{x : G | mixedSylowInter P Q x = ⊥} :=
    fun ab ↦ ⟨(ab.1 : G) * g * (ab.2 : G), mixedSylowInter_double_coset_eq_bot P Q hg ab.1 ab.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact doubleCosetMap_injective_of_mixedSylowInter_eq_bot P Q hg
      (congrArg Subtype.val hab)
  have h := Nat.card_le_card_of_injective f hf
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_prod] using h

/-- The bad-conjugator count leaves room for an entire good double coset. -/
theorem bad_conjugators_add_card_mul_le
    {G : Type uG} [Group G] [Finite G] {p : ℕ}
    (P Q : Sylow p G) {g : G} (hg : mixedSylowInter P Q g = ⊥) :
    (mixedSylowPairBadConjugators P Q).ncard + Nat.card P * Nat.card Q ≤ Nat.card G := by
  have hgood := card_mul_card_le_good_conjugators P Q hg
  have hpartition := Set.ncard_add_ncard_compl (mixedSylowPairBadConjugators P Q)
  have heq : (mixedSylowPairBadConjugators P Q)ᶜ = {x : G | mixedSylowInter P Q x = ⊥} := by
    ext x
    simp
  rw [heq] at hpartition
  omega

/-- Conjugating the two rows independently transports a good conjugator. -/
theorem mixedSylowInter_conjugate_rows_eq_bot
    {G : Type uG} [Group G] {p : ℕ}
    (P Q : Sylow p G) {g : G} (hg : mixedSylowInter P Q g = ⊥) (a b : G) :
    mixedSylowInter (a • P) (b • Q) (a * g * b⁻¹) = ⊥ := by
  have hsmul : (a * g * b⁻¹) • (b • Q) = a • (g • Q) := by
    rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul]
  rw [mixedSylowInter, hsmul, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
    ← Subgroup.smul_inf]
  change MulAut.conj a • mixedSylowInter P Q g = ⊥
  rw [hg, Subgroup.smul_bot]

/-- Existence of one trivial Sylow pair implies existence for every prescribed
mixed pair of Sylow rows at that prime. -/
theorem exists_mixedSylowInter_eq_bot_of_one_pair
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R S : Sylow p G) (hRS : ∃ g : G, mixedSylowInter R S g = ⊥)
    (P Q : Sylow p G) : ∃ x : G, mixedSylowInter P Q x = ⊥ := by
  obtain ⟨g, hg⟩ := hRS
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G R P
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G S Q
  exact ⟨a * g * b⁻¹, mixedSylowInter_conjugate_rows_eq_bot R S hg a b⟩

/-- A single good pair bounds the failure density for every mixed pair. -/
theorem bad_probability_le_of_one_trivial_pair
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R : Sylow p G) (hR : ∃ g : G, sylowInter R g = ⊥)
    (P Q : Sylow p G) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) / Nat.card G ≤
      1 - (Nat.card R : ℝ) ^ 2 / Nat.card G := by
  obtain ⟨x, hx⟩ := exists_mixedSylowInter_eq_bot_of_one_pair R R
    (by simpa only [mixedSylowInter, sylowInter] using hR) P Q
  have hbound := bad_conjugators_add_card_mul_le P Q hx
  have hP : Nat.card P = Nat.card R := Nat.card_congr (P.equiv R).toEquiv
  have hQ : Nat.card Q = Nat.card R := Nat.card_congr (Q.equiv R).toEquiv
  rw [hP, hQ] at hbound
  have hreal : ((mixedSylowPairBadConjugators P Q).ncard : ℝ) +
      (Nat.card R : ℝ)^2 ≤ Nat.card G := by
    rw [pow_two]
    exact_mod_cast hbound
  have hpos : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  apply (div_le_iff₀ hpos).mpr
  have heq : (1 - (Nat.card R : ℝ)^2 / Nat.card G) * Nat.card G =
      Nat.card G - (Nat.card R : ℝ)^2 := by field_simp
  rw [heq]
  linarith

end LisiSabatini
