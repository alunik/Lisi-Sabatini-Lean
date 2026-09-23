module

public import LisiSabatini.SylowDoubleCosetBound
public import Mathlib.Algebra.BigOperators.Field

/-!
# Counting several disjoint good double cosets

A family of good double cosets with distinct representatives gives an injective
map from the index type times the two Sylow subgroups into the good conjugators.
The resulting bound transports to independently prescribed Sylow rows.
Despite the filename, every result holds for arbitrary finite groups.
-/

@[expose] public section

noncomputable section

open scoped Pointwise BigOperators

namespace LisiSabatini

universe uG uI uJ

/-- Products from distinct good double cosets never coincide. The separation
hypothesis is phrased as a finite membership test in the second Sylow row. -/
theorem familyDoubleCosetMap_injective
    {G : Type uG} [Group G] {p : ℕ} (P Q : Sylow p G)
    {I : Type uI} (g : I → G)
    (hgood : ∀ i, mixedSylowInter P Q (g i) = ⊥)
    (hsep : ∀ i j, i ≠ j → ∀ a : G, a ∈ (P : Subgroup G) →
      (g i)⁻¹ * a * g j ∉ (Q : Subgroup G)) :
    Function.Injective (fun t : I × P × Q ↦ (t.2.1 : G) * g t.1 * (t.2.2 : G)) := by
  rintro ⟨i, a, b⟩ ⟨j, c, d⟩ heq
  change (a : G) * g i * (b : G) = (c : G) * g j * (d : G) at heq
  have hij : i = j := by
    by_contra hne
    apply hsep i j hne ((a : G)⁻¹ * (c : G))
      (P.mul_mem (P.inv_mem a.property) c.property)
    have hcalc : (g i)⁻¹ * ((a : G)⁻¹ * (c : G)) * g j =
        (b : G) * (d : G)⁻¹ := by
      calc
        _ = (g i)⁻¹ * (a : G)⁻¹ * ((c : G) * g j * (d : G)) * (d : G)⁻¹ := by group
        _ = (g i)⁻¹ * (a : G)⁻¹ * ((a : G) * g i * (b : G)) * (d : G)⁻¹ := by rw [← heq]
        _ = _ := by group
    rw [hcalc]
    exact Q.mul_mem b.property (Q.inv_mem d.property)
  subst j
  have habcd : (a, b) = (c, d) :=
    doubleCosetMap_injective_of_mixedSylowInter_eq_bot P Q (hgood i) heq
  exact Prod.ext rfl habcd

/-- Distinct good double cosets contribute their full combined cardinality. -/
theorem family_card_mul_card_le_good_conjugators
    {G : Type uG} [Group G] [Finite G] {p : ℕ} (P Q : Sylow p G)
    {I : Type uI} [Finite I] (g : I → G)
    (hgood : ∀ i, mixedSylowInter P Q (g i) = ⊥)
    (hsep : ∀ i j, i ≠ j → ∀ a : G, a ∈ (P : Subgroup G) →
      (g i)⁻¹ * a * g j ∉ (Q : Subgroup G)) :
    Nat.card I * Nat.card P * Nat.card Q ≤
      {x : G | mixedSylowInter P Q x = ⊥}.ncard := by
  let f : I × P × Q → ↥{x : G | mixedSylowInter P Q x = ⊥} :=
    fun t ↦ ⟨(t.2.1 : G) * g t.1 * (t.2.2 : G),
      mixedSylowInter_double_coset_eq_bot P Q (hgood t.1) t.2.1 t.2.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    exact familyDoubleCosetMap_injective P Q g hgood hsep (congrArg Subtype.val hab)
  have h := Nat.card_le_card_of_injective f hf
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_prod, Nat.mul_assoc] using h

/-- The failure count excludes every certified good double coset. -/
theorem bad_conjugators_add_family_card_mul_le
    {G : Type uG} [Group G] [Finite G] {p : ℕ} (P Q : Sylow p G)
    {I : Type uI} [Finite I] (g : I → G)
    (hgood : ∀ i, mixedSylowInter P Q (g i) = ⊥)
    (hsep : ∀ i j, i ≠ j → ∀ a : G, a ∈ (P : Subgroup G) →
      (g i)⁻¹ * a * g j ∉ (Q : Subgroup G)) :
    (mixedSylowPairBadConjugators P Q).ncard +
      Nat.card I * Nat.card P * Nat.card Q ≤ Nat.card G := by
  have hgoodcard := family_card_mul_card_le_good_conjugators P Q g hgood hsep
  have hpartition := Set.ncard_add_ncard_compl (mixedSylowPairBadConjugators P Q)
  have heq : (mixedSylowPairBadConjugators P Q)ᶜ =
      {x : G | mixedSylowInter P Q x = ⊥} := by
    ext x
    simp
  rw [heq] at hpartition
  omega

/-- Independent changes of the two Sylow rows preserve the combined count. -/
theorem family_card_mul_card_le_good_conjugators_conjugate_rows
    {G : Type uG} [Group G] [Finite G] {p : ℕ} (P Q : Sylow p G)
    {I : Type uI} [Finite I] (g : I → G)
    (hgood : ∀ i, mixedSylowInter P Q (g i) = ⊥)
    (hsep : ∀ i j, i ≠ j → ∀ a : G, a ∈ (P : Subgroup G) →
      (g i)⁻¹ * a * g j ∉ (Q : Subgroup G)) (a b : G) :
    Nat.card I * Nat.card P * Nat.card Q ≤
      {x : G | mixedSylowInter (a • P) (b • Q) x = ⊥}.ncard := by
  let f : I × P × Q → ↥{x : G | mixedSylowInter (a • P) (b • Q) x = ⊥} :=
    fun t ↦ ⟨a * ((t.2.1 : G) * g t.1 * (t.2.2 : G)) * b⁻¹,
      mixedSylowInter_conjugate_rows_eq_bot P Q
        (mixedSylowInter_double_coset_eq_bot P Q (hgood t.1) t.2.1 t.2.2) a b⟩
  have hf : Function.Injective f := by
    intro s t hst
    have heq := congrArg Subtype.val hst
    change a * ((s.2.1 : G) * g s.1 * (s.2.2 : G)) * b⁻¹ =
      a * ((t.2.1 : G) * g t.1 * (t.2.2 : G)) * b⁻¹ at heq
    exact familyDoubleCosetMap_injective P Q g hgood hsep
      (mul_left_cancel (mul_right_cancel heq))
  have h := Nat.card_le_card_of_injective f hf
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_prod, Nat.mul_assoc] using h

/-- A certificate for one pair of Sylow rows bounds the failure count for any
independently prescribed pair at the same prime. -/
theorem bad_conjugators_add_family_card_mul_le_of_one_pair
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R S : Sylow p G) {I : Type uI} [Finite I] (g : I → G)
    (hgood : ∀ i, mixedSylowInter R S (g i) = ⊥)
    (hsep : ∀ i j, i ≠ j → ∀ a : G, a ∈ (R : Subgroup G) →
      (g i)⁻¹ * a * g j ∉ (S : Subgroup G)) (P Q : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard +
      Nat.card I * Nat.card R * Nat.card S ≤ Nat.card G := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G R P
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G S Q
  have hgoodcard :=
    family_card_mul_card_le_good_conjugators_conjugate_rows R S g hgood hsep a b
  have hpartition := Set.ncard_add_ncard_compl
    (mixedSylowPairBadConjugators (a • R) (b • S))
  have heq : (mixedSylowPairBadConjugators (a • R) (b • S))ᶜ =
      {x : G | mixedSylowInter (a • R) (b • S) x = ⊥} := by
    ext x
    simp
  rw [heq] at hpartition
  omega

/-- The normalized failure bound from several certified good double cosets. -/
theorem bad_probability_le_of_disjoint_good_double_cosets
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (R S : Sylow p G) {I : Type uI} [Finite I] (g : I → G)
    (hgood : ∀ i, mixedSylowInter R S (g i) = ⊥)
    (hsep : ∀ i j, i ≠ j → ∀ a : G, a ∈ (R : Subgroup G) →
      (g i)⁻¹ * a * g j ∉ (S : Subgroup G)) (P Q : Sylow p G) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) / Nat.card G ≤
      1 - (Nat.card I : ℝ) * Nat.card R * Nat.card S / Nat.card G := by
  have hbound := bad_conjugators_add_family_card_mul_le_of_one_pair R S g hgood hsep P Q
  have hreal : ((mixedSylowPairBadConjugators P Q).ncard : ℝ) +
      (Nat.card I : ℝ) * Nat.card R * Nat.card S ≤ Nat.card G := by
    exact_mod_cast hbound
  have hpos : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  apply (div_le_iff₀ hpos).mpr
  have heq : (1 - (Nat.card I : ℝ) * Nat.card R * Nat.card S / Nat.card G) *
      Nat.card G = Nat.card G - (Nat.card I : ℝ) * Nat.card R * Nat.card S := by
    field_simp
  rw [heq]
  linarith

/-- A strict total failure budget from disjoint good double cosets gives a
common conjugator for an arbitrary finite family of prescribed Sylow pairs.
The prime labels need not be distinct for this counting statement. -/
theorem exists_common_mixedSylowInter_bot_of_doubleCoset_budget
    {G : Type uG} [Group G] [Finite G]
    {I : Type uI} [Fintype I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (R S : ∀ i, Sylow (p i) G)
    (J : I → Type uJ) [∀ i, Finite (J i)] (g : ∀ i, J i → G)
    (hgood : ∀ i j, mixedSylowInter (R i) (S i) (g i j) = ⊥)
    (hsep : ∀ i j k, j ≠ k → ∀ a : G, a ∈ (R i : Subgroup G) →
      (g i j)⁻¹ * a * g i k ∉ (S i : Subgroup G))
    (hbudget : (∑ i, (1 - (Nat.card (J i) : ℝ) * Nat.card (R i) *
      Nat.card (S i) / Nat.card G)) < 1)
    (P Q : ∀ i, Sylow (p i) G) :
    ∃ x : G, ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  apply exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt p P Q
  have hpos : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
  have hratio :
      ((∑ i, (mixedSylowPairBadConjugators (P i) (Q i)).ncard : ℕ) : ℝ) /
        Nat.card G < 1 := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine (Finset.sum_le_sum fun i _hi ↦ ?_).trans_lt hbudget
    let : Fact (p i).Prime := ⟨hp i⟩
    exact bad_probability_le_of_disjoint_good_double_cosets
      (R i) (S i) (g i) (hgood i) (hsep i) (P i) (Q i)
  have hcast := (div_lt_one hpos).1 hratio
  exact_mod_cast hcast

end LisiSabatini
