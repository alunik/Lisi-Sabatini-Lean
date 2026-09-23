module

public import LisiSabatini.AlternatingSylowCycleProfile
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.NormNum.Prime

/-!
# Double-coset mass budgets for degrees nine, ten, and twelve

These arithmetic certificates combine a lower bound for the good binary
mass with exact cyclic-subgroup bounds for odd primes. The specified counts
of good double cosets are numerical inputs here; their group-theoretic
certificates and disjointness must be supplied by the completion module.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

set_option maxRecDepth 10000

/-- Number of disjoint good binary double cosets used in each degree. -/
def doubleCosetGoodCount (n : ℕ) : ℕ :=
  if n = 9 then 7 else if n = 10 then 6 else if n = 12 then 41 else 0

/-- Binary Sylow orders in the three target degrees. -/
def doubleCosetSylowTwoOrder (n : ℕ) : ℕ :=
  if n = 9 then 128 else if n = 10 then 256 else if n = 12 then 1024 else 0

/-- Full-group mass of the proposed disjoint good double cosets. -/
def doubleCosetGoodMass (n : ℕ) : ℝ :=
  ((doubleCosetGoodCount n * (doubleCosetSylowTwoOrder n) ^ 2 : ℕ) : ℝ) /
    (n.factorial : ℝ)

/-- Binary failure upper bound complementary to the good mass. -/
def doubleCosetBinaryFailureCost (n : ℕ) : ℝ := 1 - doubleCosetGoodMass n

/-- Exact odd-prime union-bound budget using cyclic witnesses. -/
def doubleCosetOddPrimes : Finset ℕ := {3, 5, 7, 11}

def doubleCosetOddCyclicBudget (n : ℕ) : ℝ :=
  ∑ p ∈ doubleCosetOddPrimes,
    symmetricSylowProfileQuadraticCost n p / ((p - 1 : ℕ) : ℝ)

/-- Binary good-mass correction and cyclic odd-prime rows. -/
def doubleCosetRefinedPrimeCost (n p : ℕ) : ℝ :=
  if p = 2 then doubleCosetBinaryFailureCost n
  else symmetricSylowProfileQuadraticCost n p / ((p - 1 : ℕ) : ℝ)

def doubleCosetSmallDegreePrimes : Finset ℕ := {2, 3, 5, 7, 11}

def doubleCosetRefinedBudget (n : ℕ) : ℝ :=
  ∑ p ∈ doubleCosetSmallDegreePrimes, doubleCosetRefinedPrimeCost n p

private theorem doubleCosetProfile_9_3 :
    sylowCycleProfile 9 3 =
      1 +
      Polynomial.C 6 * Polynomial.X +
      Polynomial.C 12 * Polynomial.X ^ 2 +
      Polynomial.C 26 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem doubleCosetProfile_9_5 :
    sylowCycleProfile 9 5 =
      1 +
      Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem doubleCosetProfile_9_7 :
    sylowCycleProfile 9 7 =
      1 +
      Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem doubleCosetProfile_9_11 :
    sylowCycleProfile 9 11 =
      1 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]

private theorem doubleCosetProfile_10_3 :
    sylowCycleProfile 10 3 =
      1 +
      Polynomial.C 6 * Polynomial.X +
      Polynomial.C 12 * Polynomial.X ^ 2 +
      Polynomial.C 26 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem doubleCosetProfile_10_5 :
    sylowCycleProfile 10 5 =
      1 +
      Polynomial.C 8 * Polynomial.X +
      Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem doubleCosetProfile_10_7 :
    sylowCycleProfile 10 7 =
      1 +
      Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem doubleCosetProfile_10_11 :
    sylowCycleProfile 10 11 =
      1 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]

private theorem doubleCosetProfile_12_3 :
    sylowCycleProfile 12 3 =
      1 +
      Polynomial.C 8 * Polynomial.X +
      Polynomial.C 24 * Polynomial.X ^ 2 +
      Polynomial.C 50 * Polynomial.X ^ 3 +
      Polynomial.C 52 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem doubleCosetProfile_12_5 :
    sylowCycleProfile 12 5 =
      1 +
      Polynomial.C 8 * Polynomial.X +
      Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem doubleCosetProfile_12_7 :
    sylowCycleProfile 12 7 =
      1 +
      Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem doubleCosetProfile_12_11 :
    sylowCycleProfile 12 11 =
      1 +
      Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- The exact factorial and polynomial arithmetic exceeds the default budget.
theorem doubleCosetOddCyclicBudget_9_eq :
    doubleCosetOddCyclicBudget 9 = (607 / 2160 : ℝ) := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  norm_num [doubleCosetOddCyclicBudget,
    doubleCosetOddPrimes,
    symmetricSylowProfileQuadraticCost,
    doubleCosetProfile_9_3,
    doubleCosetProfile_9_5,
    doubleCosetProfile_9_7,
    hIcc0,
    hIcc1,
    hIcc3,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    primeCycleClassCard,
    Nat.factorial]

theorem doubleCosetGoodMass_9_eq :
    doubleCosetGoodMass 9 = (128 / 405 : ℝ) := by
  norm_num [doubleCosetGoodMass, doubleCosetGoodCount, doubleCosetSylowTwoOrder, Nat.factorial]

theorem doubleCosetOddCyclicBudget_9_lt_goodMass :
    doubleCosetOddCyclicBudget 9 < doubleCosetGoodMass 9 := by
  rw [doubleCosetOddCyclicBudget_9_eq, doubleCosetGoodMass_9_eq]
  norm_num

theorem doubleCosetBinaryFailureCost_9_nonneg :
    0 ≤ doubleCosetBinaryFailureCost 9 := by
  rw [doubleCosetBinaryFailureCost, doubleCosetGoodMass_9_eq]
  norm_num

set_option maxHeartbeats 2000000 in
-- The exact factorial and polynomial arithmetic exceeds the default budget.
theorem doubleCosetOddCyclicBudget_10_eq :
    doubleCosetOddCyclicBudget 10 = (2899 / 28350 : ℝ) := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  norm_num [doubleCosetOddCyclicBudget,
    doubleCosetOddPrimes,
    symmetricSylowProfileQuadraticCost,
    doubleCosetProfile_10_3,
    doubleCosetProfile_10_5,
    doubleCosetProfile_10_7,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    primeCycleClassCard,
    Nat.factorial]

theorem doubleCosetGoodMass_10_eq :
    doubleCosetGoodMass 10 = (512 / 4725 : ℝ) := by
  norm_num [doubleCosetGoodMass, doubleCosetGoodCount, doubleCosetSylowTwoOrder, Nat.factorial]

theorem doubleCosetOddCyclicBudget_10_lt_goodMass :
    doubleCosetOddCyclicBudget 10 < doubleCosetGoodMass 10 := by
  rw [doubleCosetOddCyclicBudget_10_eq, doubleCosetGoodMass_10_eq]
  norm_num

theorem doubleCosetBinaryFailureCost_10_nonneg :
    0 ≤ doubleCosetBinaryFailureCost 10 := by
  rw [doubleCosetBinaryFailureCost, doubleCosetGoodMass_10_eq]
  norm_num

set_option maxHeartbeats 2000000 in
-- The exact factorial and polynomial arithmetic exceeds the default budget.
theorem doubleCosetOddCyclicBudget_12_eq :
    doubleCosetOddCyclicBudget 12 = (7137833 / 79833600 : ℝ) := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  norm_num [doubleCosetOddCyclicBudget,
    doubleCosetOddPrimes,
    symmetricSylowProfileQuadraticCost,
    doubleCosetProfile_12_3,
    doubleCosetProfile_12_5,
    doubleCosetProfile_12_7,
    doubleCosetProfile_12_11,
    hIcc1,
    hIcc2,
    hIcc4,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    primeCycleClassCard,
    Nat.factorial]

theorem doubleCosetGoodMass_12_eq :
    doubleCosetGoodMass 12 = (41984 / 467775 : ℝ) := by
  norm_num [doubleCosetGoodMass, doubleCosetGoodCount, doubleCosetSylowTwoOrder, Nat.factorial]

theorem doubleCosetOddCyclicBudget_12_lt_goodMass :
    doubleCosetOddCyclicBudget 12 < doubleCosetGoodMass 12 := by
  rw [doubleCosetOddCyclicBudget_12_eq, doubleCosetGoodMass_12_eq]
  norm_num

theorem doubleCosetBinaryFailureCost_12_nonneg :
    0 ≤ doubleCosetBinaryFailureCost 12 := by
  rw [doubleCosetBinaryFailureCost, doubleCosetGoodMass_12_eq]
  norm_num

/-- Separate the good binary mass from the odd-prime incidence budget. -/
theorem doubleCosetRefinedBudget_eq (n : ℕ) :
    doubleCosetRefinedBudget n =
      1 - doubleCosetGoodMass n + doubleCosetOddCyclicBudget n := by
  norm_num [doubleCosetRefinedBudget, doubleCosetSmallDegreePrimes,
    doubleCosetRefinedPrimeCost, doubleCosetBinaryFailureCost,
    doubleCosetOddCyclicBudget, doubleCosetOddPrimes]

theorem doubleCosetRefinedBudget_9_eq :
    doubleCosetRefinedBudget 9 = (6253 / 6480 : ℝ) := by
  rw [doubleCosetRefinedBudget_eq, doubleCosetGoodMass_9_eq,
    doubleCosetOddCyclicBudget_9_eq]
  norm_num

theorem doubleCosetRefinedBudget_9_lt_one : doubleCosetRefinedBudget 9 < 1 := by
  rw [doubleCosetRefinedBudget_9_eq]
  norm_num

theorem doubleCosetRefinedBudget_10_eq :
    doubleCosetRefinedBudget 10 = (28177 / 28350 : ℝ) := by
  rw [doubleCosetRefinedBudget_eq, doubleCosetGoodMass_10_eq,
    doubleCosetOddCyclicBudget_10_eq]
  norm_num

theorem doubleCosetRefinedBudget_10_lt_one : doubleCosetRefinedBudget 10 < 1 := by
  rw [doubleCosetRefinedBudget_10_eq]
  norm_num

theorem doubleCosetRefinedBudget_12_eq :
    doubleCosetRefinedBudget 12 = (239418491 / 239500800 : ℝ) := by
  rw [doubleCosetRefinedBudget_eq, doubleCosetGoodMass_12_eq,
    doubleCosetOddCyclicBudget_12_eq]
  norm_num

theorem doubleCosetRefinedBudget_12_lt_one : doubleCosetRefinedBudget 12 < 1 := by
  rw [doubleCosetRefinedBudget_12_eq]
  norm_num

/-- The finite prime list contains all prime divisors relevant to these degrees. -/
theorem mem_doubleCosetSmallDegreePrimes_of_prime_le_twelve {p : ℕ}
    (hp : p.Prime) (hle : p ≤ 12) : p ∈ doubleCosetSmallDegreePrimes := by
  interval_cases p <;> norm_num [doubleCosetSmallDegreePrimes] at *

/-- Each refined row is nonnegative in the three certified degrees. -/
theorem doubleCosetRefinedPrimeCost_nonneg {n : ℕ}
    (hn : n = 9 ∨ n = 10 ∨ n = 12) (p : ℕ) :
    0 ≤ doubleCosetRefinedPrimeCost n p := by
  unfold doubleCosetRefinedPrimeCost
  split_ifs
  · rcases hn with rfl | rfl | rfl
    · exact doubleCosetBinaryFailureCost_9_nonneg
    · exact doubleCosetBinaryFailureCost_10_nonneg
    · exact doubleCosetBinaryFailureCost_12_nonneg
  · apply div_nonneg _ (Nat.cast_nonneg _)
    unfold symmetricSylowProfileQuadraticCost
    apply Finset.sum_nonneg
    intro j _
    exact div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- Labels above the degree make no contribution. -/
theorem doubleCosetRefinedPrimeCost_eq_zero_of_lt {n p : ℕ}
    (hn : 2 ≤ n) (hp : n < p) : doubleCosetRefinedPrimeCost n p = 0 := by
  have hp2 : p ≠ 2 := by omega
  have hdiv : n / p = 0 := Nat.div_eq_of_lt hp
  simp [doubleCosetRefinedPrimeCost, hp2, symmetricSylowProfileQuadraticCost, hdiv]

end LisiSabatini
