module

public import LisiSabatini.SymmetricSmallDegreeMatchingBound
public import LisiSabatini.SymmetricSmallDegreeMatchingCostFormula
public import LisiSabatini.SymmetricSmallDegreeMatchingArithmetic
public import LisiSabatini.SymmetricSmallDegreeBadCardTransport

/-!
# Symmetric degrees fourteen and sixteen

Matching-flip compression proves a strict full-group budget in degrees
fourteen and sixteen. The result covers every finite injectively
prime-labelled family of independently prescribed left and right Sylow
rows. All class counts and rational inequalities are kernel-checked.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI

local instance matchingCompletionDecidableRel (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _

/-- Matching compression supplies a uniform binary-row probability bound
for every positive even symmetric degree. -/
theorem bad_probability_le_matchingRefinedTwoCost (m : ℕ) (hm : 0 < m)
    (P Q : Sylow 2 (Equiv.Perm (Fin (2 * m)))) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) /
        (Nat.card (Equiv.Perm (Fin (2 * m))) : ℝ) ≤ matchingRefinedTwoCost (2 * m) := by
  classical
  obtain ⟨R, hR⟩ := exists_sylow_two_ge_finPairFlipSubgroup m
  have h := bad_ncard_add_matching_le_quadratic_add_swaps R R
    (finPairMatching m) (finPairMatching m)
    (finPairMatching_involutive m) (finPairMatching_involutive m) hR hR
  change (mixedSylowPairBadConjugators R R).ncard +
      (∑ C, subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
        (finPairFlipSubgroup m) (fun _ ↦ True) C) ≤
    (∑ C, mixedSylowPairQuadraticClassTerm R R C) +
      ∑ C, subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
        (finPairFlipSubgroup m) (fun g ↦ g.IsSwap) C at h
  have hcast :
      ((mixedSylowPairBadConjugators R R).ncard : ℝ) +
        ((∑ C, subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
          (finPairFlipSubgroup m) (fun _ ↦ True) C : ℕ) : ℝ) ≤
      ((∑ C, mixedSylowPairQuadraticClassTerm R R C : ℕ) : ℝ) +
        ((∑ C, subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
          (finPairFlipSubgroup m) (fun g ↦ g.IsSwap) C : ℕ) : ℝ) := by
    exact_mod_cast h
  have hscaled := div_le_div_of_nonneg_right hcast
    (show (0 : ℝ) ≤ (Nat.card (Equiv.Perm (Fin (2 * m))) : ℝ) from Nat.cast_nonneg _)
  rw [add_div, add_div, normalized_matchingIncidenceCost_eq_binomial_sum,
    normalized_matchingSwapIncidenceCost_eq m hm] at hscaled
  change ((mixedSylowPairBadConjugators R R).ncard : ℝ) / _ + _ ≤
    normalizedSameRowSylowQuadraticCost (Equiv.Perm (Fin (2 * m))) R + _ at hscaled
  rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile Nat.prime_two R,
    ← ncard_mixed_bad_eq_reference P Q R] at hscaled
  simp only [matchingRefinedTwoCost, matchingQuadraticProfileCost,
    matchingTranspositionProfileCost, show 2 * m / 2 = m by omega]
  linarith

/-- Every row in either degree satisfies the refined arithmetic bound. -/
theorem bad_probability_le_matchingRefinedPrimeCost
    {n p : ℕ} (hn : n = 14 ∨ n = 16) (hp : p.Prime)
    (P Q : Sylow p (Equiv.Perm (Fin n))) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) /
        (Nat.card (Equiv.Perm (Fin n)) : ℝ) ≤ matchingRefinedPrimeCost n p := by
  by_cases hp2 : p = 2
  · subst p
    rw [matchingRefinedPrimeCost, ite_eq_left rfl]
    rcases hn with rfl | rfl
    · exact bad_probability_le_matchingRefinedTwoCost 7 (by decide) P Q
    · exact bad_probability_le_matchingRefinedTwoCost 8 (by decide) P Q
  · rw [matchingRefinedPrimeCost, ite_eq_right hp2]
    let : Fact p.Prime := ⟨hp⟩
    have h := bad_probability_le_cyclic_quadratic_cost P Q
    rwa [normalizedSameRowSylowQuadraticCost_perm_eq_profile hp P] at h

/-- The full refined budget dominates every injectively prime-labelled
subfamily, including labels larger than the symmetric degree. -/
theorem sum_matchingRefinedPrimeCost_lt_one
    {n : ℕ} (hn : n = 14 ∨ n = 16)
    {I : Type uI} [Fintype I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (∑ i, matchingRefinedPrimeCost n (p i)) < 1 := by
  classical
  have hn2 : 2 ≤ n := by rcases hn with rfl | rfl <;> omega
  have hn16 : n ≤ 16 := by rcases hn with rfl | rfl <;> omega
  let s : Finset I := Finset.univ.filter fun i ↦ p i ≤ n
  have hcut : (∑ i ∈ s, matchingRefinedPrimeCost n (p i)) =
      ∑ i, matchingRefinedPrimeCost n (p i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _hi hnot
    apply matchingRefinedPrimeCost_eq_zero_of_lt hn2
    exact Nat.lt_of_not_ge (fun hle ↦ hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩))
  rw [← hcut]
  have hle : (∑ i ∈ s, matchingRefinedPrimeCost n (p i)) ≤
      matchingRefinedSmallDegreeBudget n := by
    apply Finset.sum_le_sum_of_injOn p
    · intro i _hi j _hj hij
      exact hinj hij
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      exact mem_matchingSmallDegreePrimes_of_prime_le_sixteen (hp i)
        ((Finset.mem_filter.mp hi).2.trans hn16)
    · intro i _hi
      exact le_rfl
    · intro q _hq _hnot
      exact matchingRefinedPrimeCost_nonneg hn q
  apply hle.trans_lt
  rcases hn with rfl | rfl
  · exact matchingRefinedSmallDegreeBudget_14_lt_one
  · exact matchingRefinedSmallDegreeBudget_16_lt_one

/-- Universal mixed Sylow synchronization in symmetric degrees 14 and 16. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_fourteen_sixteen
    {n : ℕ} (hn : n = 14 ∨ n = 16)
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
      bad_probability_le_matchingRefinedPrimeCost hn (hp i) (P i) (Q i))).trans_lt
        (sum_matchingRefinedPrimeCost_lt_one hn p hp hinj)
  exact_mod_cast (div_lt_one hc).mp hratio

/-- Lisi--Sabatini in symmetric degrees 14 and 16. -/
theorem hasLisiSabatini_symmetricGroup_fourteen_sixteen
    {n : ℕ} (hn : n = 14 ∨ n = 16) : HasLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinj P
  obtain ⟨x, hx⟩ := exists_common_mixedSylowInter_bot_symmetricGroup_fourteen_sixteen
    hn p hp hinj P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  change mixedSylowInter (P i) (P i) x ≤ _
  rw [hx i]
  exact bot_le

end LisiSabatini
