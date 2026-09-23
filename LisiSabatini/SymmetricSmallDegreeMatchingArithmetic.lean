module

public import LisiSabatini.AlternatingSylowCycleProfile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime

/-!
# Matching-corrected finite-degree budgets

The binary row subtracts all matching-flip incidences and adds back only
single-edge incidences. Odd-prime rows count cyclic subgroups rather than
individual generators. All exact arithmetic is checked by the Lean kernel.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

set_option maxRecDepth 10000

/-- Exact quadratic class profile of the independent pair-flip subgroup. -/
def matchingQuadraticProfileCost (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n / 2),
    (Nat.choose (n / 2) j : ℝ) ^ 2 / (primeCycleClassCard n 2 j : ℝ)

/-- Expected number of common matching edges. -/
def matchingTranspositionProfileCost (n : ℕ) : ℝ :=
  (n / 2 : ℕ) ^ 2 / (primeCycleClassCard n 2 1 : ℝ)

/-- Binary cost after grouping all common matching flips by a single edge. -/
def matchingRefinedTwoCost (n : ℕ) : ℝ :=
  symmetricSylowProfileQuadraticCost n 2 - matchingQuadraticProfileCost n +
    matchingTranspositionProfileCost n

/-- Correct the binary row; divide other rows by the number of generators. -/
def matchingRefinedPrimeCost (n p : ℕ) : ℝ :=
  if p = 2 then matchingRefinedTwoCost n
  else symmetricSylowProfileQuadraticCost n p / ((p - 1 : ℕ) : ℝ)

/-- Every prime that can divide `14!` or `16!`. -/
def matchingSmallDegreePrimes : Finset ℕ := {2, 3, 5, 7, 11, 13}

def matchingRefinedSmallDegreeBudget (n : ℕ) : ℝ :=
  ∑ p ∈ matchingSmallDegreePrimes, matchingRefinedPrimeCost n p

private theorem matchingProfile_14_2 :
    sylowCycleProfile 14 2 =
      1 + Polynomial.C 7 * Polynomial.X + Polynomial.C 27 * Polynomial.X ^ 2 +
      Polynomial.C 65 * Polynomial.X ^ 3 + Polynomial.C 115 * Polynomial.X ^ 4 +
      Polynomial.C 141 * Polynomial.X ^ 5 + Polynomial.C 121 * Polynomial.X ^ 6 +
      Polynomial.C 51 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_14_3 :
    sylowCycleProfile 14 3 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 24 * Polynomial.X ^ 2 +
      Polynomial.C 50 * Polynomial.X ^ 3 + Polynomial.C 52 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_14_5 :
    sylowCycleProfile 14 5 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_14_7 :
    sylowCycleProfile 14 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_14_11 :
    sylowCycleProfile 14 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem matchingProfile_14_13 :
    sylowCycleProfile 14 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem matchingProfile_16_2 :
    sylowCycleProfile 16 2 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 +
      Polynomial.C 104 * Polynomial.X ^ 3 + Polynomial.C 230 * Polynomial.X ^ 4 +
      Polynomial.C 376 * Polynomial.X ^ 5 + Polynomial.C 484 * Polynomial.X ^ 6 +
      Polynomial.C 408 * Polynomial.X ^ 7 + Polynomial.C 417 * Polynomial.X ^ 8 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_16_3 :
    sylowCycleProfile 16 3 =
      1 + Polynomial.C 10 * Polynomial.X + Polynomial.C 40 * Polynomial.X ^ 2 +
      Polynomial.C 98 * Polynomial.X ^ 3 + Polynomial.C 152 * Polynomial.X ^ 4 +
      Polynomial.C 104 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_16_5 :
    sylowCycleProfile 16 5 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 48 * Polynomial.X ^ 2 +
      Polynomial.C 64 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_16_7 :
    sylowCycleProfile 16 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem matchingProfile_16_11 :
    sylowCycleProfile 16 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem matchingProfile_16_13 :
    sylowCycleProfile 16 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic needs a larger elaboration budget.
theorem matchingRefinedTwoCost_14_eq :
    matchingRefinedTwoCost 14 = (751307 / 945945 : ℝ) := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  norm_num [matchingRefinedTwoCost,
    matchingQuadraticProfileCost,
    matchingTranspositionProfileCost,
    symmetricSylowProfileQuadraticCost,
    matchingProfile_14_2,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc7,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    primeCycleClassCard,
    Nat.factorial,
    Nat.choose]

theorem matchingRefinedTwoCost_14_nonneg :
    0 ≤ matchingRefinedTwoCost 14 := by
  rw [matchingRefinedTwoCost_14_eq]
  norm_num

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic needs a larger elaboration budget.
theorem matchingRefinedSmallDegreeBudget_14_eq :
    matchingRefinedSmallDegreeBudget 14 = (25465631 / 30270240 : ℝ) := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  norm_num [matchingRefinedSmallDegreeBudget,
    matchingSmallDegreePrimes,
    matchingRefinedPrimeCost,
    matchingRefinedTwoCost,
    matchingQuadraticProfileCost,
    matchingTranspositionProfileCost,
    symmetricSylowProfileQuadraticCost,
    matchingProfile_14_2,
    matchingProfile_14_3,
    matchingProfile_14_5,
    matchingProfile_14_7,
    matchingProfile_14_11,
    matchingProfile_14_13,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc7,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    primeCycleClassCard,
    Nat.factorial,
    Nat.choose]

theorem matchingRefinedSmallDegreeBudget_14_lt_one :
    matchingRefinedSmallDegreeBudget 14 < 1 := by
  rw [matchingRefinedSmallDegreeBudget_14_eq]
  norm_num

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic needs a larger elaboration budget.
theorem matchingRefinedTwoCost_16_eq :
    matchingRefinedTwoCost 16 = (269032 / 315315 : ℝ) := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  norm_num [matchingRefinedTwoCost,
    matchingQuadraticProfileCost,
    matchingTranspositionProfileCost,
    symmetricSylowProfileQuadraticCost,
    matchingProfile_16_2,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc8,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    primeCycleClassCard,
    Nat.factorial,
    Nat.choose]

theorem matchingRefinedTwoCost_16_nonneg :
    0 ≤ matchingRefinedTwoCost 16 := by
  rw [matchingRefinedTwoCost_16_eq]
  norm_num

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic needs a larger elaboration budget.
theorem matchingRefinedSmallDegreeBudget_16_eq :
    matchingRefinedSmallDegreeBudget 16 = (87267893329 / 96864768000 : ℝ) := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  norm_num [matchingRefinedSmallDegreeBudget,
    matchingSmallDegreePrimes,
    matchingRefinedPrimeCost,
    matchingRefinedTwoCost,
    matchingQuadraticProfileCost,
    matchingTranspositionProfileCost,
    symmetricSylowProfileQuadraticCost,
    matchingProfile_16_2,
    matchingProfile_16_3,
    matchingProfile_16_5,
    matchingProfile_16_7,
    matchingProfile_16_11,
    matchingProfile_16_13,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc8,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    primeCycleClassCard,
    Nat.factorial,
    Nat.choose]

theorem matchingRefinedSmallDegreeBudget_16_lt_one :
    matchingRefinedSmallDegreeBudget 16 < 1 := by
  rw [matchingRefinedSmallDegreeBudget_16_eq]
  norm_num

/-- Every term of either finite-degree refined budget is nonnegative. -/
theorem matchingRefinedPrimeCost_nonneg {n : ℕ} (hn : n = 14 ∨ n = 16) (p : ℕ) :
    0 ≤ matchingRefinedPrimeCost n p := by
  unfold matchingRefinedPrimeCost
  split_ifs with hp
  · rcases hn with rfl | rfl
    · exact matchingRefinedTwoCost_14_nonneg
    · exact matchingRefinedTwoCost_16_nonneg
  · apply div_nonneg _ (Nat.cast_nonneg _)
    unfold symmetricSylowProfileQuadraticCost
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Primes larger than the symmetric degree contribute nothing. -/
theorem matchingRefinedPrimeCost_eq_zero_of_lt {n p : ℕ}
    (hn : 2 ≤ n) (hp : n < p) : matchingRefinedPrimeCost n p = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hdiv : n / p = 0 := Nat.div_eq_of_lt hp
  simp [matchingRefinedPrimeCost, hp2, symmetricSylowProfileQuadraticCost, hdiv]

/-- The finite prime list contains every possible prime divisor of either degree. -/
theorem mem_matchingSmallDegreePrimes_of_prime_le_sixteen {p : ℕ}
    (hp : p.Prime) (hle : p ≤ 16) : p ∈ matchingSmallDegreePrimes := by
  interval_cases p <;> norm_num [matchingSmallDegreePrimes] at *

/-- Expanded arithmetic form of the refined budget. -/
theorem matchingRefinedSmallDegreeBudget_eq (n : ℕ) :
    matchingRefinedSmallDegreeBudget n =
      (∑ p ∈ matchingSmallDegreePrimes,
        symmetricSylowProfileQuadraticCost n p / ((p - 1 : ℕ) : ℝ)) -
        matchingQuadraticProfileCost n + matchingTranspositionProfileCost n := by
  norm_num [matchingRefinedSmallDegreeBudget, matchingSmallDegreePrimes,
    matchingRefinedPrimeCost, matchingRefinedTwoCost]
  ring

theorem matchingCorrectedCyclicBudget_14_lt_one :
    (∑ p ∈ matchingSmallDegreePrimes,
      symmetricSylowProfileQuadraticCost 14 p / ((p - 1 : ℕ) : ℝ)) -
      matchingQuadraticProfileCost 14 + matchingTranspositionProfileCost 14 < 1 := by
  rw [← matchingRefinedSmallDegreeBudget_eq]
  exact matchingRefinedSmallDegreeBudget_14_lt_one

theorem matchingCorrectedCyclicBudget_16_lt_one :
    (∑ p ∈ matchingSmallDegreePrimes,
      symmetricSylowProfileQuadraticCost 16 p / ((p - 1 : ℕ) : ℝ)) -
      matchingQuadraticProfileCost 16 + matchingTranspositionProfileCost 16 < 1 := by
  rw [← matchingRefinedSmallDegreeBudget_eq]
  exact matchingRefinedSmallDegreeBudget_16_lt_one

end LisiSabatini
