module

public import LisiSabatini.SymmetricDoubleCosetBound
public import LisiSabatini.SymmetricDoubleCosetArithmetic
public import LisiSabatini.SymmetricDoubleCosetCertificates
public import LisiSabatini.CyclicSylowQuadraticBound
public import LisiSabatini.AlternatingSylowQuadraticFormula

/-!
# Completing the double-coset bounds in degrees nine, ten, and twelve

The binary estimate comes from actual disjoint good double cosets. The
remaining prime rows use the exact cyclic-witness class sums. A full-group
union bound then handles independently prescribed left and right Sylow rows.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI

local instance doubleCosetCompletionDecidableRel (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _

private def SymmetricDoubleCosetCertificateData (n : ℕ) : Prop :=
  ∃ R : Sylow 2 (Equiv.Perm (Fin n)),
    Nat.card R = doubleCosetSylowTwoOrder n ∧
    ∃ g : Fin (doubleCosetGoodCount n) → Equiv.Perm (Fin n),
      (∀ i, mixedSylowInter R R (g i) = ⊥) ∧
      (∀ i j, i ≠ j → ∀ a ∈ (R : Subgroup (Equiv.Perm (Fin n))),
        (g i)⁻¹ * a * g j ∉ (R : Subgroup (Equiv.Perm (Fin n))))

private theorem doubleCoset_binary_probability_bound
    {n : ℕ} (hcert : SymmetricDoubleCosetCertificateData n)
    (P Q : Sylow 2 (Equiv.Perm (Fin n))) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) /
        (Nat.card (Equiv.Perm (Fin n)) : ℝ) ≤ doubleCosetBinaryFailureCost n := by
  obtain ⟨R, hR, g, hgood, hsep⟩ := hcert
  have h := bad_probability_le_of_disjoint_good_double_cosets
    R R g hgood hsep P Q
  rw [Nat.card_fin, hR] at h
  simpa only [doubleCosetBinaryFailureCost, doubleCosetGoodMass,
    Nat.cast_mul, Nat.cast_pow, natCard_perm_fin, pow_two, mul_assoc] using h

private theorem doubleCoset_prime_probability_bound
    {n p : ℕ} (hcert : SymmetricDoubleCosetCertificateData n) (hp : p.Prime)
    (P Q : Sylow p (Equiv.Perm (Fin n))) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) /
        (Nat.card (Equiv.Perm (Fin n)) : ℝ) ≤ doubleCosetRefinedPrimeCost n p := by
  by_cases hp2 : p = 2
  · subst p
    rw [doubleCosetRefinedPrimeCost, ite_eq_left rfl]
    exact doubleCoset_binary_probability_bound hcert P Q
  · rw [doubleCosetRefinedPrimeCost, ite_eq_right hp2]
    let : Fact p.Prime := ⟨hp⟩
    have h := bad_probability_le_cyclic_quadratic_cost P Q
    rwa [normalizedSameRowSylowQuadraticCost_perm_eq_profile hp P] at h

private theorem doubleCoset_subfamily_budget
    {n : ℕ} (hn : n = 9 ∨ n = 10 ∨ n = 12)
    {I : Type uI} [Fintype I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (∑ i, doubleCosetRefinedPrimeCost n (p i)) < 1 := by
  classical
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl | rfl <;> omega
  have hn12 : n ≤ 12 := by rcases hn with rfl | rfl | rfl <;> omega
  let s : Finset I := Finset.univ.filter fun i ↦ p i ≤ n
  have hcut : (∑ i ∈ s, doubleCosetRefinedPrimeCost n (p i)) =
      ∑ i, doubleCosetRefinedPrimeCost n (p i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _hi hnot
    apply doubleCosetRefinedPrimeCost_eq_zero_of_lt hn2
    exact Nat.lt_of_not_ge (fun hle ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩))
  rw [← hcut]
  have hle : (∑ i ∈ s, doubleCosetRefinedPrimeCost n (p i)) ≤
      doubleCosetRefinedBudget n := by
    apply Finset.sum_le_sum_of_injOn p
    · intro i _hi j _hj hij
      exact hinj hij
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact mem_doubleCosetSmallDegreePrimes_of_prime_le_twelve (hp i)
        ((Finset.mem_filter.mp hi).2.trans hn12)
    · intro i _hi
      exact le_rfl
    · intro q _hq _hnot
      exact doubleCosetRefinedPrimeCost_nonneg hn q
  apply hle.trans_lt
  rcases hn with rfl | rfl | rfl
  · exact doubleCosetRefinedBudget_9_lt_one
  · exact doubleCosetRefinedBudget_10_lt_one
  · exact doubleCosetRefinedBudget_12_lt_one

private theorem doubleCoset_common_conjugator_of_certificate
    {n : ℕ} (hn : n = 9 ∨ n = 10 ∨ n = 12)
    (hcert : SymmetricDoubleCosetCertificateData n)
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin n))) :
    ∃ x : Equiv.Perm (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let : Fintype I := Fintype.ofFinite I
  apply exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt p P Q
  have hc : (0 : ℝ) < (Nat.card (Equiv.Perm (Fin n)) : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card (Equiv.Perm (Fin n)))
  have hratio :
      ((∑ i, (mixedSylowPairBadConjugators (P i) (Q i)).ncard : ℕ) : ℝ) /
        (Nat.card (Equiv.Perm (Fin n)) : ℝ) < 1 := by
    rw [Nat.cast_sum, Finset.sum_div]
    exact (Finset.sum_le_sum (fun i _hi ↦
      doubleCoset_prime_probability_bound hcert (hp i) (P i) (Q i))).trans_lt
        (doubleCoset_subfamily_budget hn p hp hinj)
  exact_mod_cast (div_lt_one hc).mp hratio

/-- Universal mixed Sylow synchronization in symmetric degrees nine, ten,
and twelve, using the concrete kernel-checked double-coset certificates. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_nine_ten_twelve
    (n : ℕ) (hn : n = 9 ∨ n = 10 ∨ n = 12)
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin n))) :
    ∃ x : Equiv.Perm (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  have hcert : SymmetricDoubleCosetCertificateData n := by
    simpa only [SymmetricDoubleCosetCertificateData] using
      exists_symmetricDoubleCosetCertificate n hn
  exact doubleCoset_common_conjugator_of_certificate hn hcert p hp hinj P Q

/-- Lisi--Sabatini in symmetric degrees nine, ten, and twelve. -/
theorem hasLisiSabatini_symmetricGroup_nine_ten_twelve
    (n : ℕ) (hn : n = 9 ∨ n = 10 ∨ n = 12) :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinj P
  obtain ⟨x, hx⟩ := exists_common_mixedSylowInter_bot_symmetricGroup_nine_ten_twelve
    n hn p hp hinj P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  change mixedSylowInter (P i) (P i) x ≤ _
  rw [hx i]
  exact bot_le

end LisiSabatini
