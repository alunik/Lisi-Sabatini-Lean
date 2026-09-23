module

public import LisiSabatini.AlternatingSylowCycleProfile
public import Mathlib.Tactic.IntervalCases

/-!
# Exact finite-degree Sylow-profile budgets

The certificates below compute the already verified Sylow cycle-profile
recurrence and check strict rational inequalities in the Lean kernel.
They use no permutation-group enumeration or external computation oracle.
The explicit polynomial identities are private certificate data; public
interfaces below concern the original group-theoretic cost functions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

set_option maxRecDepth 10000

private def paperSmallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37}

private def paperSymmetricFiniteBudget (n : ℕ) : ℝ :=
  ∑ p ∈ paperSmallPrimes, symmetricSylowProfileQuadraticCost n p

private def paperAlternatingFiniteBudget (n : ℕ) : ℝ :=
  ∑ p ∈ paperSmallPrimes, alternatingSylowProfileQuadraticCost n p

private theorem paperProfile_11_2 :
    sylowCycleProfile 11 2 =
      1 + Polynomial.C 5 * Polynomial.X + Polynomial.C 14 * Polynomial.X ^ 2 +
      Polynomial.C 22 * Polynomial.X ^ 3 + Polynomial.C 29 * Polynomial.X ^ 4 +
      Polynomial.C 17 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_11_3 :
    sylowCycleProfile 11 3 =
      1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 12 * Polynomial.X ^ 2 +
      Polynomial.C 26 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_11_5 :
    sylowCycleProfile 11 5 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_11_7 :
    sylowCycleProfile 11 7 = 1 + Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_11_11 :
    sylowCycleProfile 11 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_11_lt :
    paperSymmetricFiniteBudget 11 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_11_2,
    paperProfile_11_3,
    paperProfile_11_5,
    paperProfile_11_7,
    paperProfile_11_11,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_13_2 :
    sylowCycleProfile 13 2 =
      1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 21 * Polynomial.X ^ 2 +
      Polynomial.C 44 * Polynomial.X ^ 3 + Polynomial.C 71 * Polynomial.X ^ 4 +
      Polynomial.C 70 * Polynomial.X ^ 5 + Polynomial.C 51 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_13_3 :
    sylowCycleProfile 13 3 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 24 * Polynomial.X ^ 2 +
      Polynomial.C 50 * Polynomial.X ^ 3 + Polynomial.C 52 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_13_5 :
    sylowCycleProfile 13 5 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_13_7 :
    sylowCycleProfile 13 7 = 1 + Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_13_11 :
    sylowCycleProfile 13 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_13_13 :
    sylowCycleProfile 13 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_13_lt :
    paperSymmetricFiniteBudget 13 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_13_2,
    paperProfile_13_3,
    paperProfile_13_5,
    paperProfile_13_7,
    paperProfile_13_11,
    paperProfile_13_13,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_15_2 :
    sylowCycleProfile 15 2 =
      1 + Polynomial.C 7 * Polynomial.X + Polynomial.C 27 * Polynomial.X ^ 2 +
      Polynomial.C 65 * Polynomial.X ^ 3 + Polynomial.C 115 * Polynomial.X ^ 4 +
      Polynomial.C 141 * Polynomial.X ^ 5 + Polynomial.C 121 * Polynomial.X ^ 6 +
      Polynomial.C 51 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_15_3 :
    sylowCycleProfile 15 3 =
      1 + Polynomial.C 10 * Polynomial.X + Polynomial.C 40 * Polynomial.X ^ 2 +
      Polynomial.C 98 * Polynomial.X ^ 3 + Polynomial.C 152 * Polynomial.X ^ 4 +
      Polynomial.C 104 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_15_5 :
    sylowCycleProfile 15 5 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 48 * Polynomial.X ^ 2 +
      Polynomial.C 64 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_15_7 :
    sylowCycleProfile 15 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_15_11 :
    sylowCycleProfile 15 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_15_13 :
    sylowCycleProfile 15 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_15_lt :
    paperSymmetricFiniteBudget 15 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_15_2,
    paperProfile_15_3,
    paperProfile_15_5,
    paperProfile_15_7,
    paperProfile_15_11,
    paperProfile_15_13,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_17_2 :
    sylowCycleProfile 17 2 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 +
      Polynomial.C 104 * Polynomial.X ^ 3 + Polynomial.C 230 * Polynomial.X ^ 4 +
      Polynomial.C 376 * Polynomial.X ^ 5 + Polynomial.C 484 * Polynomial.X ^ 6 +
      Polynomial.C 408 * Polynomial.X ^ 7 + Polynomial.C 417 * Polynomial.X ^ 8 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_17_3 :
    sylowCycleProfile 17 3 =
      1 + Polynomial.C 10 * Polynomial.X + Polynomial.C 40 * Polynomial.X ^ 2 +
      Polynomial.C 98 * Polynomial.X ^ 3 + Polynomial.C 152 * Polynomial.X ^ 4 +
      Polynomial.C 104 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_17_5 :
    sylowCycleProfile 17 5 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 48 * Polynomial.X ^ 2 +
      Polynomial.C 64 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_17_7 :
    sylowCycleProfile 17 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_17_11 :
    sylowCycleProfile 17 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_17_13 :
    sylowCycleProfile 17 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_17_17 :
    sylowCycleProfile 17 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_17_lt :
    paperSymmetricFiniteBudget 17 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_17_2,
    paperProfile_17_3,
    paperProfile_17_5,
    paperProfile_17_7,
    paperProfile_17_11,
    paperProfile_17_13,
    paperProfile_17_17,
    hIcc0,
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
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_18_2 :
    sylowCycleProfile 18 2 =
      1 + Polynomial.C 9 * Polynomial.X + Polynomial.C 44 * Polynomial.X ^ 2 +
      Polynomial.C 140 * Polynomial.X ^ 3 + Polynomial.C 334 * Polynomial.X ^ 4 +
      Polynomial.C 606 * Polynomial.X ^ 5 + Polynomial.C 860 * Polynomial.X ^ 6 +
      Polynomial.C 892 * Polynomial.X ^ 7 + Polynomial.C 825 * Polynomial.X ^ 8 +
      Polynomial.C 417 * Polynomial.X ^ 9 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_18_3 :
    sylowCycleProfile 18 3 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 60 * Polynomial.X ^ 2 +
      Polynomial.C 196 * Polynomial.X ^ 3 + Polynomial.C 456 * Polynomial.X ^ 4 +
      Polynomial.C 624 * Polynomial.X ^ 5 + Polynomial.C 676 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_18_5 :
    sylowCycleProfile 18 5 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 48 * Polynomial.X ^ 2 +
      Polynomial.C 64 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_18_7 :
    sylowCycleProfile 18 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_18_11 :
    sylowCycleProfile 18 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_18_13 :
    sylowCycleProfile 18 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_18_17 :
    sylowCycleProfile 18 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_18_lt :
    paperSymmetricFiniteBudget 18 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_18_2,
    paperProfile_18_3,
    paperProfile_18_5,
    paperProfile_18_7,
    paperProfile_18_11,
    paperProfile_18_13,
    paperProfile_18_17,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc6,
    hIcc9,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_19_2 :
    sylowCycleProfile 19 2 =
      1 + Polynomial.C 9 * Polynomial.X + Polynomial.C 44 * Polynomial.X ^ 2 +
      Polynomial.C 140 * Polynomial.X ^ 3 + Polynomial.C 334 * Polynomial.X ^ 4 +
      Polynomial.C 606 * Polynomial.X ^ 5 + Polynomial.C 860 * Polynomial.X ^ 6 +
      Polynomial.C 892 * Polynomial.X ^ 7 + Polynomial.C 825 * Polynomial.X ^ 8 +
      Polynomial.C 417 * Polynomial.X ^ 9 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_19_3 :
    sylowCycleProfile 19 3 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 60 * Polynomial.X ^ 2 +
      Polynomial.C 196 * Polynomial.X ^ 3 + Polynomial.C 456 * Polynomial.X ^ 4 +
      Polynomial.C 624 * Polynomial.X ^ 5 + Polynomial.C 676 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_19_5 :
    sylowCycleProfile 19 5 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 48 * Polynomial.X ^ 2 +
      Polynomial.C 64 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_19_7 :
    sylowCycleProfile 19 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_19_11 :
    sylowCycleProfile 19 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_19_13 :
    sylowCycleProfile 19 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_19_17 :
    sylowCycleProfile 19 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_19_19 :
    sylowCycleProfile 19 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_19_lt :
    paperSymmetricFiniteBudget 19 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_19_2,
    paperProfile_19_3,
    paperProfile_19_5,
    paperProfile_19_7,
    paperProfile_19_11,
    paperProfile_19_13,
    paperProfile_19_17,
    paperProfile_19_19,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc6,
    hIcc9,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_20_2 :
    sylowCycleProfile 20 2 =
      1 + Polynomial.C 10 * Polynomial.X + Polynomial.C 55 * Polynomial.X ^ 2 +
      Polynomial.C 200 * Polynomial.X ^ 3 + Polynomial.C 546 * Polynomial.X ^ 4 +
      Polynomial.C 1148 * Polynomial.X ^ 5 + Polynomial.C 1926 * Polynomial.X ^ 6 +
      Polynomial.C 2504 * Polynomial.X ^ 7 + Polynomial.C 2685 * Polynomial.X ^ 8 +
      Polynomial.C 2058 * Polynomial.X ^ 9 + Polynomial.C 1251 * Polynomial.X ^ 10 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_20_3 :
    sylowCycleProfile 20 3 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 60 * Polynomial.X ^ 2 +
      Polynomial.C 196 * Polynomial.X ^ 3 + Polynomial.C 456 * Polynomial.X ^ 4 +
      Polynomial.C 624 * Polynomial.X ^ 5 + Polynomial.C 676 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_20_5 :
    sylowCycleProfile 20 5 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 96 * Polynomial.X ^ 2 +
      Polynomial.C 256 * Polynomial.X ^ 3 + Polynomial.C 256 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_20_7 :
    sylowCycleProfile 20 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_20_11 :
    sylowCycleProfile 20 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_20_13 :
    sylowCycleProfile 20 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_20_17 :
    sylowCycleProfile 20 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_20_19 :
    sylowCycleProfile 20 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_20_lt :
    paperSymmetricFiniteBudget 20 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_20_2,
    paperProfile_20_3,
    paperProfile_20_5,
    paperProfile_20_7,
    paperProfile_20_11,
    paperProfile_20_13,
    paperProfile_20_17,
    paperProfile_20_19,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_21_2 :
    sylowCycleProfile 21 2 =
      1 + Polynomial.C 10 * Polynomial.X + Polynomial.C 55 * Polynomial.X ^ 2 +
      Polynomial.C 200 * Polynomial.X ^ 3 + Polynomial.C 546 * Polynomial.X ^ 4 +
      Polynomial.C 1148 * Polynomial.X ^ 5 + Polynomial.C 1926 * Polynomial.X ^ 6 +
      Polynomial.C 2504 * Polynomial.X ^ 7 + Polynomial.C 2685 * Polynomial.X ^ 8 +
      Polynomial.C 2058 * Polynomial.X ^ 9 + Polynomial.C 1251 * Polynomial.X ^ 10 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_21_3 :
    sylowCycleProfile 21 3 =
      1 + Polynomial.C 14 * Polynomial.X + Polynomial.C 84 * Polynomial.X ^ 2 +
      Polynomial.C 316 * Polynomial.X ^ 3 + Polynomial.C 848 * Polynomial.X ^ 4 +
      Polynomial.C 1536 * Polynomial.X ^ 5 + Polynomial.C 1924 * Polynomial.X ^ 6 +
      Polynomial.C 1352 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_21_5 :
    sylowCycleProfile 21 5 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 96 * Polynomial.X ^ 2 +
      Polynomial.C 256 * Polynomial.X ^ 3 + Polynomial.C 256 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_21_7 :
    sylowCycleProfile 21 7 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 108 * Polynomial.X ^ 2 +
      Polynomial.C 216 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_21_11 :
    sylowCycleProfile 21 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_21_13 :
    sylowCycleProfile 21 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_21_17 :
    sylowCycleProfile 21 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_21_19 :
    sylowCycleProfile 21 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_21_lt :
    paperSymmetricFiniteBudget 21 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_21_2,
    paperProfile_21_3,
    paperProfile_21_5,
    paperProfile_21_7,
    paperProfile_21_11,
    paperProfile_21_13,
    paperProfile_21_17,
    paperProfile_21_19,
    hIcc0,
    hIcc1,
    hIcc3,
    hIcc4,
    hIcc7,
    hIcc10,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_22_2 :
    sylowCycleProfile 22 2 =
      1 + Polynomial.C 11 * Polynomial.X + Polynomial.C 65 * Polynomial.X ^ 2 +
      Polynomial.C 255 * Polynomial.X ^ 3 + Polynomial.C 746 * Polynomial.X ^ 4 +
      Polynomial.C 1694 * Polynomial.X ^ 5 + Polynomial.C 3074 * Polynomial.X ^ 6 +
      Polynomial.C 4430 * Polynomial.X ^ 7 + Polynomial.C 5189 * Polynomial.X ^ 8 +
      Polynomial.C 4743 * Polynomial.X ^ 9 + Polynomial.C 3309 * Polynomial.X ^ 10 +
      Polynomial.C 1251 * Polynomial.X ^ 11 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_22_3 :
    sylowCycleProfile 22 3 =
      1 + Polynomial.C 14 * Polynomial.X + Polynomial.C 84 * Polynomial.X ^ 2 +
      Polynomial.C 316 * Polynomial.X ^ 3 + Polynomial.C 848 * Polynomial.X ^ 4 +
      Polynomial.C 1536 * Polynomial.X ^ 5 + Polynomial.C 1924 * Polynomial.X ^ 6 +
      Polynomial.C 1352 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_22_5 :
    sylowCycleProfile 22 5 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 96 * Polynomial.X ^ 2 +
      Polynomial.C 256 * Polynomial.X ^ 3 + Polynomial.C 256 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_22_7 :
    sylowCycleProfile 22 7 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 108 * Polynomial.X ^ 2 +
      Polynomial.C 216 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_22_11 :
    sylowCycleProfile 22 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_22_13 :
    sylowCycleProfile 22 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_22_17 :
    sylowCycleProfile 22 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_22_19 :
    sylowCycleProfile 22 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_22_lt :
    paperSymmetricFiniteBudget 22 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_22_2,
    paperProfile_22_3,
    paperProfile_22_5,
    paperProfile_22_7,
    paperProfile_22_11,
    paperProfile_22_13,
    paperProfile_22_17,
    paperProfile_22_19,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc7,
    hIcc11,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_23_2 :
    sylowCycleProfile 23 2 =
      1 + Polynomial.C 11 * Polynomial.X + Polynomial.C 65 * Polynomial.X ^ 2 +
      Polynomial.C 255 * Polynomial.X ^ 3 + Polynomial.C 746 * Polynomial.X ^ 4 +
      Polynomial.C 1694 * Polynomial.X ^ 5 + Polynomial.C 3074 * Polynomial.X ^ 6 +
      Polynomial.C 4430 * Polynomial.X ^ 7 + Polynomial.C 5189 * Polynomial.X ^ 8 +
      Polynomial.C 4743 * Polynomial.X ^ 9 + Polynomial.C 3309 * Polynomial.X ^ 10 +
      Polynomial.C 1251 * Polynomial.X ^ 11 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_23_3 :
    sylowCycleProfile 23 3 =
      1 + Polynomial.C 14 * Polynomial.X + Polynomial.C 84 * Polynomial.X ^ 2 +
      Polynomial.C 316 * Polynomial.X ^ 3 + Polynomial.C 848 * Polynomial.X ^ 4 +
      Polynomial.C 1536 * Polynomial.X ^ 5 + Polynomial.C 1924 * Polynomial.X ^ 6 +
      Polynomial.C 1352 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_23_5 :
    sylowCycleProfile 23 5 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 96 * Polynomial.X ^ 2 +
      Polynomial.C 256 * Polynomial.X ^ 3 + Polynomial.C 256 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_23_7 :
    sylowCycleProfile 23 7 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 108 * Polynomial.X ^ 2 +
      Polynomial.C 216 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_23_11 :
    sylowCycleProfile 23 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_23_13 :
    sylowCycleProfile 23 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_23_17 :
    sylowCycleProfile 23 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_23_19 :
    sylowCycleProfile 23 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_23_23 :
    sylowCycleProfile 23 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_23_lt :
    paperSymmetricFiniteBudget 23 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_23_2,
    paperProfile_23_3,
    paperProfile_23_5,
    paperProfile_23_7,
    paperProfile_23_11,
    paperProfile_23_13,
    paperProfile_23_17,
    paperProfile_23_19,
    paperProfile_23_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc7,
    hIcc11,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_23_lt :
    paperAlternatingFiniteBudget 23 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_23_2,
    paperProfile_23_3,
    paperProfile_23_5,
    paperProfile_23_7,
    paperProfile_23_11,
    paperProfile_23_13,
    paperProfile_23_17,
    paperProfile_23_19,
    paperProfile_23_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc7,
    hIcc11,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_24_2 :
    sylowCycleProfile 24 2 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 78 * Polynomial.X ^ 2 +
      Polynomial.C 340 * Polynomial.X ^ 3 + Polynomial.C 1119 * Polynomial.X ^ 4 +
      Polynomial.C 2904 * Polynomial.X ^ 5 + Polynomial.C 6148 * Polynomial.X ^ 6 +
      Polynomial.C 10632 * Polynomial.X ^ 7 + Polynomial.C 15311 * Polynomial.X ^ 8 +
      Polynomial.C 17948 * Polynomial.X ^ 9 + Polynomial.C 17294 * Polynomial.X ^ 10 +
      Polynomial.C 11940 * Polynomial.X ^ 11 + Polynomial.C 7089 * Polynomial.X ^ 12 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_24_3 :
    sylowCycleProfile 24 3 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 112 * Polynomial.X ^ 2 +
      Polynomial.C 484 * Polynomial.X ^ 3 + Polynomial.C 1480 * Polynomial.X ^ 4 +
      Polynomial.C 3232 * Polynomial.X ^ 5 + Polynomial.C 4996 * Polynomial.X ^ 6 +
      Polynomial.C 5200 * Polynomial.X ^ 7 + Polynomial.C 2704 * Polynomial.X ^ 8 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_24_5 :
    sylowCycleProfile 24 5 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 96 * Polynomial.X ^ 2 +
      Polynomial.C 256 * Polynomial.X ^ 3 + Polynomial.C 256 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_24_7 :
    sylowCycleProfile 24 7 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 108 * Polynomial.X ^ 2 +
      Polynomial.C 216 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_24_11 :
    sylowCycleProfile 24 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_24_13 :
    sylowCycleProfile 24 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_24_17 :
    sylowCycleProfile 24 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_24_19 :
    sylowCycleProfile 24 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_24_23 :
    sylowCycleProfile 24 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_24_lt :
    paperSymmetricFiniteBudget 24 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_24_2,
    paperProfile_24_3,
    paperProfile_24_5,
    paperProfile_24_7,
    paperProfile_24_11,
    paperProfile_24_13,
    paperProfile_24_17,
    paperProfile_24_19,
    paperProfile_24_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc8,
    hIcc12,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_25_2 :
    sylowCycleProfile 25 2 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 78 * Polynomial.X ^ 2 +
      Polynomial.C 340 * Polynomial.X ^ 3 + Polynomial.C 1119 * Polynomial.X ^ 4 +
      Polynomial.C 2904 * Polynomial.X ^ 5 + Polynomial.C 6148 * Polynomial.X ^ 6 +
      Polynomial.C 10632 * Polynomial.X ^ 7 + Polynomial.C 15311 * Polynomial.X ^ 8 +
      Polynomial.C 17948 * Polynomial.X ^ 9 + Polynomial.C 17294 * Polynomial.X ^ 10 +
      Polynomial.C 11940 * Polynomial.X ^ 11 + Polynomial.C 7089 * Polynomial.X ^ 12 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_25_3 :
    sylowCycleProfile 25 3 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 112 * Polynomial.X ^ 2 +
      Polynomial.C 484 * Polynomial.X ^ 3 + Polynomial.C 1480 * Polynomial.X ^ 4 +
      Polynomial.C 3232 * Polynomial.X ^ 5 + Polynomial.C 4996 * Polynomial.X ^ 6 +
      Polynomial.C 5200 * Polynomial.X ^ 7 + Polynomial.C 2704 * Polynomial.X ^ 8 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_25_5 :
    sylowCycleProfile 25 5 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 160 * Polynomial.X ^ 2 +
      Polynomial.C 640 * Polynomial.X ^ 3 + Polynomial.C 1280 * Polynomial.X ^ 4 +
      Polynomial.C 3524 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_25_7 :
    sylowCycleProfile 25 7 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 108 * Polynomial.X ^ 2 +
      Polynomial.C 216 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_25_11 :
    sylowCycleProfile 25 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_25_13 :
    sylowCycleProfile 25 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_25_17 :
    sylowCycleProfile 25 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_25_19 :
    sylowCycleProfile 25 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_25_23 :
    sylowCycleProfile 25 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_25_lt :
    paperSymmetricFiniteBudget 25 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_25_2,
    paperProfile_25_3,
    paperProfile_25_5,
    paperProfile_25_7,
    paperProfile_25_11,
    paperProfile_25_13,
    paperProfile_25_17,
    paperProfile_25_19,
    paperProfile_25_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc8,
    hIcc12,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_25_lt :
    paperAlternatingFiniteBudget 25 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_25_2,
    paperProfile_25_3,
    paperProfile_25_5,
    paperProfile_25_7,
    paperProfile_25_11,
    paperProfile_25_13,
    paperProfile_25_17,
    paperProfile_25_19,
    paperProfile_25_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc8,
    hIcc12,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_26_2 :
    sylowCycleProfile 26 2 =
      1 + Polynomial.C 13 * Polynomial.X + Polynomial.C 90 * Polynomial.X ^ 2 +
      Polynomial.C 418 * Polynomial.X ^ 3 + Polynomial.C 1459 * Polynomial.X ^ 4 +
      Polynomial.C 4023 * Polynomial.X ^ 5 + Polynomial.C 9052 * Polynomial.X ^ 6 +
      Polynomial.C 16780 * Polynomial.X ^ 7 + Polynomial.C 25943 * Polynomial.X ^ 8 +
      Polynomial.C 33259 * Polynomial.X ^ 9 + Polynomial.C 35242 * Polynomial.X ^ 10 +
      Polynomial.C 29234 * Polynomial.X ^ 11 + Polynomial.C 19029 * Polynomial.X ^ 12 +
      Polynomial.C 7089 * Polynomial.X ^ 13 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_26_3 :
    sylowCycleProfile 26 3 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 112 * Polynomial.X ^ 2 +
      Polynomial.C 484 * Polynomial.X ^ 3 + Polynomial.C 1480 * Polynomial.X ^ 4 +
      Polynomial.C 3232 * Polynomial.X ^ 5 + Polynomial.C 4996 * Polynomial.X ^ 6 +
      Polynomial.C 5200 * Polynomial.X ^ 7 + Polynomial.C 2704 * Polynomial.X ^ 8 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_26_5 :
    sylowCycleProfile 26 5 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 160 * Polynomial.X ^ 2 +
      Polynomial.C 640 * Polynomial.X ^ 3 + Polynomial.C 1280 * Polynomial.X ^ 4 +
      Polynomial.C 3524 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_26_7 :
    sylowCycleProfile 26 7 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 108 * Polynomial.X ^ 2 +
      Polynomial.C 216 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_26_11 :
    sylowCycleProfile 26 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_26_13 :
    sylowCycleProfile 26 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_26_17 :
    sylowCycleProfile 26 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_26_19 :
    sylowCycleProfile 26 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_26_23 :
    sylowCycleProfile 26 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_26_lt :
    paperSymmetricFiniteBudget 26 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc13 : Finset.Icc 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_26_2,
    paperProfile_26_3,
    paperProfile_26_5,
    paperProfile_26_7,
    paperProfile_26_11,
    paperProfile_26_13,
    paperProfile_26_17,
    paperProfile_26_19,
    paperProfile_26_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc8,
    hIcc13,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_26_lt :
    paperAlternatingFiniteBudget 26 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc13 : Finset.Icc 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_26_2,
    paperProfile_26_3,
    paperProfile_26_5,
    paperProfile_26_7,
    paperProfile_26_11,
    paperProfile_26_13,
    paperProfile_26_17,
    paperProfile_26_19,
    paperProfile_26_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc8,
    hIcc13,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_27_2 :
    sylowCycleProfile 27 2 =
      1 + Polynomial.C 13 * Polynomial.X + Polynomial.C 90 * Polynomial.X ^ 2 +
      Polynomial.C 418 * Polynomial.X ^ 3 + Polynomial.C 1459 * Polynomial.X ^ 4 +
      Polynomial.C 4023 * Polynomial.X ^ 5 + Polynomial.C 9052 * Polynomial.X ^ 6 +
      Polynomial.C 16780 * Polynomial.X ^ 7 + Polynomial.C 25943 * Polynomial.X ^ 8 +
      Polynomial.C 33259 * Polynomial.X ^ 9 + Polynomial.C 35242 * Polynomial.X ^ 10 +
      Polynomial.C 29234 * Polynomial.X ^ 11 + Polynomial.C 19029 * Polynomial.X ^ 12 +
      Polynomial.C 7089 * Polynomial.X ^ 13 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_27_3 :
    sylowCycleProfile 27 3 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 +
      Polynomial.C 726 * Polynomial.X ^ 3 + Polynomial.C 2664 * Polynomial.X ^ 4 +
      Polynomial.C 7272 * Polynomial.X ^ 5 + Polynomial.C 14988 * Polynomial.X ^ 6 +
      Polynomial.C 23400 * Polynomial.X ^ 7 + Polynomial.C 24336 * Polynomial.X ^ 8 +
      Polynomial.C 30698 * Polynomial.X ^ 9 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_27_5 :
    sylowCycleProfile 27 5 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 160 * Polynomial.X ^ 2 +
      Polynomial.C 640 * Polynomial.X ^ 3 + Polynomial.C 1280 * Polynomial.X ^ 4 +
      Polynomial.C 3524 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_27_7 :
    sylowCycleProfile 27 7 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 108 * Polynomial.X ^ 2 +
      Polynomial.C 216 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_27_11 :
    sylowCycleProfile 27 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_27_13 :
    sylowCycleProfile 27 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_27_17 :
    sylowCycleProfile 27 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_27_19 :
    sylowCycleProfile 27 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_27_23 :
    sylowCycleProfile 27 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_27_lt :
    paperSymmetricFiniteBudget 27 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  have hIcc13 : Finset.Icc 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_27_2,
    paperProfile_27_3,
    paperProfile_27_5,
    paperProfile_27_7,
    paperProfile_27_11,
    paperProfile_27_13,
    paperProfile_27_17,
    paperProfile_27_19,
    paperProfile_27_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc9,
    hIcc13,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_27_lt :
    paperAlternatingFiniteBudget 27 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  have hIcc13 : Finset.Icc 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_27_2,
    paperProfile_27_3,
    paperProfile_27_5,
    paperProfile_27_7,
    paperProfile_27_11,
    paperProfile_27_13,
    paperProfile_27_17,
    paperProfile_27_19,
    paperProfile_27_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc9,
    hIcc13,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_28_2 :
    sylowCycleProfile 28 2 =
      1 + Polynomial.C 14 * Polynomial.X + Polynomial.C 105 * Polynomial.X ^ 2 +
      Polynomial.C 532 * Polynomial.X ^ 3 + Polynomial.C 2033 * Polynomial.X ^ 4 +
      Polynomial.C 6162 * Polynomial.X ^ 5 + Polynomial.C 15313 * Polynomial.X ^ 6 +
      Polynomial.C 31640 * Polynomial.X ^ 7 + Polynomial.C 55019 * Polynomial.X ^ 8 +
      Polynomial.C 80466 * Polynomial.X ^ 9 + Polynomial.C 99123 * Polynomial.X ^ 10 +
      Polynomial.C 100372 * Polynomial.X ^ 11 + Polynomial.C 82851 * Polynomial.X ^ 12 +
      Polynomial.C 49998 * Polynomial.X ^ 13 + Polynomial.C 21267 * Polynomial.X ^ 14 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_28_3 :
    sylowCycleProfile 28 3 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 +
      Polynomial.C 726 * Polynomial.X ^ 3 + Polynomial.C 2664 * Polynomial.X ^ 4 +
      Polynomial.C 7272 * Polynomial.X ^ 5 + Polynomial.C 14988 * Polynomial.X ^ 6 +
      Polynomial.C 23400 * Polynomial.X ^ 7 + Polynomial.C 24336 * Polynomial.X ^ 8 +
      Polynomial.C 30698 * Polynomial.X ^ 9 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_28_5 :
    sylowCycleProfile 28 5 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 160 * Polynomial.X ^ 2 +
      Polynomial.C 640 * Polynomial.X ^ 3 + Polynomial.C 1280 * Polynomial.X ^ 4 +
      Polynomial.C 3524 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_28_7 :
    sylowCycleProfile 28 7 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 216 * Polynomial.X ^ 2 +
      Polynomial.C 864 * Polynomial.X ^ 3 + Polynomial.C 1296 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_28_11 :
    sylowCycleProfile 28 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_28_13 :
    sylowCycleProfile 28 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_28_17 :
    sylowCycleProfile 28 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_28_19 :
    sylowCycleProfile 28 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_28_23 :
    sylowCycleProfile 28 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_28_lt :
    paperSymmetricFiniteBudget 28 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  have hIcc14 : Finset.Icc 1 14 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_28_2,
    paperProfile_28_3,
    paperProfile_28_5,
    paperProfile_28_7,
    paperProfile_28_11,
    paperProfile_28_13,
    paperProfile_28_17,
    paperProfile_28_19,
    paperProfile_28_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc5,
    hIcc9,
    hIcc14,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_28_lt :
    paperAlternatingFiniteBudget 28 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  have hIcc14 : Finset.Icc 1 14 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_28_2,
    paperProfile_28_3,
    paperProfile_28_5,
    paperProfile_28_7,
    paperProfile_28_11,
    paperProfile_28_13,
    paperProfile_28_17,
    paperProfile_28_19,
    paperProfile_28_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc5,
    hIcc9,
    hIcc14,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_29_2 :
    sylowCycleProfile 29 2 =
      1 + Polynomial.C 14 * Polynomial.X + Polynomial.C 105 * Polynomial.X ^ 2 +
      Polynomial.C 532 * Polynomial.X ^ 3 + Polynomial.C 2033 * Polynomial.X ^ 4 +
      Polynomial.C 6162 * Polynomial.X ^ 5 + Polynomial.C 15313 * Polynomial.X ^ 6 +
      Polynomial.C 31640 * Polynomial.X ^ 7 + Polynomial.C 55019 * Polynomial.X ^ 8 +
      Polynomial.C 80466 * Polynomial.X ^ 9 + Polynomial.C 99123 * Polynomial.X ^ 10 +
      Polynomial.C 100372 * Polynomial.X ^ 11 + Polynomial.C 82851 * Polynomial.X ^ 12 +
      Polynomial.C 49998 * Polynomial.X ^ 13 + Polynomial.C 21267 * Polynomial.X ^ 14 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_29_3 :
    sylowCycleProfile 29 3 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 +
      Polynomial.C 726 * Polynomial.X ^ 3 + Polynomial.C 2664 * Polynomial.X ^ 4 +
      Polynomial.C 7272 * Polynomial.X ^ 5 + Polynomial.C 14988 * Polynomial.X ^ 6 +
      Polynomial.C 23400 * Polynomial.X ^ 7 + Polynomial.C 24336 * Polynomial.X ^ 8 +
      Polynomial.C 30698 * Polynomial.X ^ 9 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_29_5 :
    sylowCycleProfile 29 5 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 160 * Polynomial.X ^ 2 +
      Polynomial.C 640 * Polynomial.X ^ 3 + Polynomial.C 1280 * Polynomial.X ^ 4 +
      Polynomial.C 3524 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_29_7 :
    sylowCycleProfile 29 7 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 216 * Polynomial.X ^ 2 +
      Polynomial.C 864 * Polynomial.X ^ 3 + Polynomial.C 1296 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_29_11 :
    sylowCycleProfile 29 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_29_13 :
    sylowCycleProfile 29 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_29_17 :
    sylowCycleProfile 29 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_29_19 :
    sylowCycleProfile 29 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_29_23 :
    sylowCycleProfile 29 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_29_29 :
    sylowCycleProfile 29 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_29_lt :
    paperSymmetricFiniteBudget 29 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  have hIcc14 : Finset.Icc 1 14 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_29_2,
    paperProfile_29_3,
    paperProfile_29_5,
    paperProfile_29_7,
    paperProfile_29_11,
    paperProfile_29_13,
    paperProfile_29_17,
    paperProfile_29_19,
    paperProfile_29_23,
    paperProfile_29_29,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc5,
    hIcc9,
    hIcc14,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_29_lt :
    paperAlternatingFiniteBudget 29 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  have hIcc14 : Finset.Icc 1 14 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_29_2,
    paperProfile_29_3,
    paperProfile_29_5,
    paperProfile_29_7,
    paperProfile_29_11,
    paperProfile_29_13,
    paperProfile_29_17,
    paperProfile_29_19,
    paperProfile_29_23,
    paperProfile_29_29,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc5,
    hIcc9,
    hIcc14,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_30_2 :
    sylowCycleProfile 30 2 =
      1 + Polynomial.C 15 * Polynomial.X + Polynomial.C 119 * Polynomial.X ^ 2 +
      Polynomial.C 637 * Polynomial.X ^ 3 + Polynomial.C 2565 * Polynomial.X ^ 4 +
      Polynomial.C 8195 * Polynomial.X ^ 5 + Polynomial.C 21475 * Polynomial.X ^ 6 +
      Polynomial.C 46953 * Polynomial.X ^ 7 + Polynomial.C 86659 * Polynomial.X ^ 8 +
      Polynomial.C 135485 * Polynomial.X ^ 9 + Polynomial.C 179589 * Polynomial.X ^ 10 +
      Polynomial.C 199495 * Polynomial.X ^ 11 + Polynomial.C 183223 * Polynomial.X ^ 12 +
      Polynomial.C 132849 * Polynomial.X ^ 13 + Polynomial.C 71265 * Polynomial.X ^ 14 +
      Polynomial.C 21267 * Polynomial.X ^ 15 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_30_3 :
    sylowCycleProfile 30 3 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 180 * Polynomial.X ^ 2 +
      Polynomial.C 1014 * Polynomial.X ^ 3 + Polynomial.C 4116 * Polynomial.X ^ 4 +
      Polynomial.C 12600 * Polynomial.X ^ 5 + Polynomial.C 29532 * Polynomial.X ^ 6 +
      Polynomial.C 53376 * Polynomial.X ^ 7 + Polynomial.C 71136 * Polynomial.X ^ 8 +
      Polynomial.C 79370 * Polynomial.X ^ 9 + Polynomial.C 61396 * Polynomial.X ^ 10 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_30_5 :
    sylowCycleProfile 30 5 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 240 * Polynomial.X ^ 2 +
      Polynomial.C 1280 * Polynomial.X ^ 3 + Polynomial.C 3840 * Polynomial.X ^ 4 +
      Polynomial.C 8644 * Polynomial.X ^ 5 + Polynomial.C 14096 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_30_7 :
    sylowCycleProfile 30 7 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 216 * Polynomial.X ^ 2 +
      Polynomial.C 864 * Polynomial.X ^ 3 + Polynomial.C 1296 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_30_11 :
    sylowCycleProfile 30 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_30_13 :
    sylowCycleProfile 30 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_30_17 :
    sylowCycleProfile 30 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_30_19 :
    sylowCycleProfile 30 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_30_23 :
    sylowCycleProfile 30 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_30_29 :
    sylowCycleProfile 30 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_30_lt :
    paperSymmetricFiniteBudget 30 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  have hIcc15 : Finset.Icc 1 15 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_30_2,
    paperProfile_30_3,
    paperProfile_30_5,
    paperProfile_30_7,
    paperProfile_30_11,
    paperProfile_30_13,
    paperProfile_30_17,
    paperProfile_30_19,
    paperProfile_30_23,
    paperProfile_30_29,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    hIcc15,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_30_lt :
    paperAlternatingFiniteBudget 30 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  have hIcc15 : Finset.Icc 1 15 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_30_2,
    paperProfile_30_3,
    paperProfile_30_5,
    paperProfile_30_7,
    paperProfile_30_11,
    paperProfile_30_13,
    paperProfile_30_17,
    paperProfile_30_19,
    paperProfile_30_23,
    paperProfile_30_29,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    hIcc15,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_31_2 :
    sylowCycleProfile 31 2 =
      1 + Polynomial.C 15 * Polynomial.X + Polynomial.C 119 * Polynomial.X ^ 2 +
      Polynomial.C 637 * Polynomial.X ^ 3 + Polynomial.C 2565 * Polynomial.X ^ 4 +
      Polynomial.C 8195 * Polynomial.X ^ 5 + Polynomial.C 21475 * Polynomial.X ^ 6 +
      Polynomial.C 46953 * Polynomial.X ^ 7 + Polynomial.C 86659 * Polynomial.X ^ 8 +
      Polynomial.C 135485 * Polynomial.X ^ 9 + Polynomial.C 179589 * Polynomial.X ^ 10 +
      Polynomial.C 199495 * Polynomial.X ^ 11 + Polynomial.C 183223 * Polynomial.X ^ 12 +
      Polynomial.C 132849 * Polynomial.X ^ 13 + Polynomial.C 71265 * Polynomial.X ^ 14 +
      Polynomial.C 21267 * Polynomial.X ^ 15 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_31_3 :
    sylowCycleProfile 31 3 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 180 * Polynomial.X ^ 2 +
      Polynomial.C 1014 * Polynomial.X ^ 3 + Polynomial.C 4116 * Polynomial.X ^ 4 +
      Polynomial.C 12600 * Polynomial.X ^ 5 + Polynomial.C 29532 * Polynomial.X ^ 6 +
      Polynomial.C 53376 * Polynomial.X ^ 7 + Polynomial.C 71136 * Polynomial.X ^ 8 +
      Polynomial.C 79370 * Polynomial.X ^ 9 + Polynomial.C 61396 * Polynomial.X ^ 10 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_31_5 :
    sylowCycleProfile 31 5 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 240 * Polynomial.X ^ 2 +
      Polynomial.C 1280 * Polynomial.X ^ 3 + Polynomial.C 3840 * Polynomial.X ^ 4 +
      Polynomial.C 8644 * Polynomial.X ^ 5 + Polynomial.C 14096 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_31_7 :
    sylowCycleProfile 31 7 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 216 * Polynomial.X ^ 2 +
      Polynomial.C 864 * Polynomial.X ^ 3 + Polynomial.C 1296 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_31_11 :
    sylowCycleProfile 31 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_31_13 :
    sylowCycleProfile 31 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_31_17 :
    sylowCycleProfile 31 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_31_19 :
    sylowCycleProfile 31 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_31_23 :
    sylowCycleProfile 31 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_31_29 :
    sylowCycleProfile 31 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_31_31 :
    sylowCycleProfile 31 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_31_lt :
    paperSymmetricFiniteBudget 31 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  have hIcc15 : Finset.Icc 1 15 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_31_2,
    paperProfile_31_3,
    paperProfile_31_5,
    paperProfile_31_7,
    paperProfile_31_11,
    paperProfile_31_13,
    paperProfile_31_17,
    paperProfile_31_19,
    paperProfile_31_23,
    paperProfile_31_29,
    paperProfile_31_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    hIcc15,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_31_lt :
    paperAlternatingFiniteBudget 31 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  have hIcc15 : Finset.Icc 1 15 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_31_2,
    paperProfile_31_3,
    paperProfile_31_5,
    paperProfile_31_7,
    paperProfile_31_11,
    paperProfile_31_13,
    paperProfile_31_17,
    paperProfile_31_19,
    paperProfile_31_23,
    paperProfile_31_29,
    paperProfile_31_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    hIcc15,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_32_2 :
    sylowCycleProfile 32 2 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 136 * Polynomial.X ^ 2 +
      Polynomial.C 784 * Polynomial.X ^ 3 + Polynomial.C 3420 * Polynomial.X ^ 4 +
      Polynomial.C 11920 * Polynomial.X ^ 5 + Polynomial.C 34360 * Polynomial.X ^ 6 +
      Polynomial.C 83472 * Polynomial.X ^ 7 + Polynomial.C 173318 * Polynomial.X ^ 8 +
      Polynomial.C 309680 * Polynomial.X ^ 9 + Polynomial.C 478904 * Polynomial.X ^ 10 +
      Polynomial.C 638384 * Polynomial.X ^ 11 + Polynomial.C 732892 * Polynomial.X ^ 12 +
      Polynomial.C 708528 * Polynomial.X ^ 13 + Polynomial.C 570120 * Polynomial.X ^ 14 +
      Polynomial.C 340272 * Polynomial.X ^ 15 + Polynomial.C 206657 * Polynomial.X ^ 16 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_32_3 :
    sylowCycleProfile 32 3 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 180 * Polynomial.X ^ 2 +
      Polynomial.C 1014 * Polynomial.X ^ 3 + Polynomial.C 4116 * Polynomial.X ^ 4 +
      Polynomial.C 12600 * Polynomial.X ^ 5 + Polynomial.C 29532 * Polynomial.X ^ 6 +
      Polynomial.C 53376 * Polynomial.X ^ 7 + Polynomial.C 71136 * Polynomial.X ^ 8 +
      Polynomial.C 79370 * Polynomial.X ^ 9 + Polynomial.C 61396 * Polynomial.X ^ 10 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_32_5 :
    sylowCycleProfile 32 5 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 240 * Polynomial.X ^ 2 +
      Polynomial.C 1280 * Polynomial.X ^ 3 + Polynomial.C 3840 * Polynomial.X ^ 4 +
      Polynomial.C 8644 * Polynomial.X ^ 5 + Polynomial.C 14096 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_32_7 :
    sylowCycleProfile 32 7 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 216 * Polynomial.X ^ 2 +
      Polynomial.C 864 * Polynomial.X ^ 3 + Polynomial.C 1296 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_32_11 :
    sylowCycleProfile 32 11 =
      1 + Polynomial.C 20 * Polynomial.X + Polynomial.C 100 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_32_13 :
    sylowCycleProfile 32 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_32_17 :
    sylowCycleProfile 32 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_32_19 :
    sylowCycleProfile 32 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_32_23 :
    sylowCycleProfile 32 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_32_29 :
    sylowCycleProfile 32 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_32_31 :
    sylowCycleProfile 32 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_32_lt :
    paperSymmetricFiniteBudget 32 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  have hIcc16 : Finset.Icc 1 16 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_32_2,
    paperProfile_32_3,
    paperProfile_32_5,
    paperProfile_32_7,
    paperProfile_32_11,
    paperProfile_32_13,
    paperProfile_32_17,
    paperProfile_32_19,
    paperProfile_32_23,
    paperProfile_32_29,
    paperProfile_32_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    hIcc16,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_32_lt :
    paperAlternatingFiniteBudget 32 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  have hIcc16 : Finset.Icc 1 16 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_32_2,
    paperProfile_32_3,
    paperProfile_32_5,
    paperProfile_32_7,
    paperProfile_32_11,
    paperProfile_32_13,
    paperProfile_32_17,
    paperProfile_32_19,
    paperProfile_32_23,
    paperProfile_32_29,
    paperProfile_32_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    hIcc16,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_33_2 :
    sylowCycleProfile 33 2 =
      1 + Polynomial.C 16 * Polynomial.X + Polynomial.C 136 * Polynomial.X ^ 2 +
      Polynomial.C 784 * Polynomial.X ^ 3 + Polynomial.C 3420 * Polynomial.X ^ 4 +
      Polynomial.C 11920 * Polynomial.X ^ 5 + Polynomial.C 34360 * Polynomial.X ^ 6 +
      Polynomial.C 83472 * Polynomial.X ^ 7 + Polynomial.C 173318 * Polynomial.X ^ 8 +
      Polynomial.C 309680 * Polynomial.X ^ 9 + Polynomial.C 478904 * Polynomial.X ^ 10 +
      Polynomial.C 638384 * Polynomial.X ^ 11 + Polynomial.C 732892 * Polynomial.X ^ 12 +
      Polynomial.C 708528 * Polynomial.X ^ 13 + Polynomial.C 570120 * Polynomial.X ^ 14 +
      Polynomial.C 340272 * Polynomial.X ^ 15 + Polynomial.C 206657 * Polynomial.X ^ 16 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_33_3 :
    sylowCycleProfile 33 3 =
      1 + Polynomial.C 22 * Polynomial.X + Polynomial.C 220 * Polynomial.X ^ 2 +
      Polynomial.C 1374 * Polynomial.X ^ 3 + Polynomial.C 6144 * Polynomial.X ^ 4 +
      Polynomial.C 20832 * Polynomial.X ^ 5 + Polynomial.C 54732 * Polynomial.X ^ 6 +
      Polynomial.C 112440 * Polynomial.X ^ 7 + Polynomial.C 177888 * Polynomial.X ^ 8 +
      Polynomial.C 221642 * Polynomial.X ^ 9 + Polynomial.C 220136 * Polynomial.X ^ 10 +
      Polynomial.C 122792 * Polynomial.X ^ 11 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_33_5 :
    sylowCycleProfile 33 5 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 240 * Polynomial.X ^ 2 +
      Polynomial.C 1280 * Polynomial.X ^ 3 + Polynomial.C 3840 * Polynomial.X ^ 4 +
      Polynomial.C 8644 * Polynomial.X ^ 5 + Polynomial.C 14096 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_33_7 :
    sylowCycleProfile 33 7 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 216 * Polynomial.X ^ 2 +
      Polynomial.C 864 * Polynomial.X ^ 3 + Polynomial.C 1296 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_33_11 :
    sylowCycleProfile 33 11 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 300 * Polynomial.X ^ 2 +
      Polynomial.C 1000 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_33_13 :
    sylowCycleProfile 33 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_33_17 :
    sylowCycleProfile 33 17 = 1 + Polynomial.C 16 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_33_19 :
    sylowCycleProfile 33 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_33_23 :
    sylowCycleProfile 33 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_33_29 :
    sylowCycleProfile 33 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_33_31 :
    sylowCycleProfile 33 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_33_lt :
    paperSymmetricFiniteBudget 33 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  have hIcc16 : Finset.Icc 1 16 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_33_2,
    paperProfile_33_3,
    paperProfile_33_5,
    paperProfile_33_7,
    paperProfile_33_11,
    paperProfile_33_13,
    paperProfile_33_17,
    paperProfile_33_19,
    paperProfile_33_23,
    paperProfile_33_29,
    paperProfile_33_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc6,
    hIcc11,
    hIcc16,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_33_lt :
    paperAlternatingFiniteBudget 33 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  have hIcc16 : Finset.Icc 1 16 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_33_2,
    paperProfile_33_3,
    paperProfile_33_5,
    paperProfile_33_7,
    paperProfile_33_11,
    paperProfile_33_13,
    paperProfile_33_17,
    paperProfile_33_19,
    paperProfile_33_23,
    paperProfile_33_29,
    paperProfile_33_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc6,
    hIcc11,
    hIcc16,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_34_2 :
    sylowCycleProfile 34 2 =
      1 + Polynomial.C 17 * Polynomial.X + Polynomial.C 152 * Polynomial.X ^ 2 +
      Polynomial.C 920 * Polynomial.X ^ 3 + Polynomial.C 4204 * Polynomial.X ^ 4 +
      Polynomial.C 15340 * Polynomial.X ^ 5 + Polynomial.C 46280 * Polynomial.X ^ 6 +
      Polynomial.C 117832 * Polynomial.X ^ 7 + Polynomial.C 256790 * Polynomial.X ^ 8 +
      Polynomial.C 482998 * Polynomial.X ^ 9 + Polynomial.C 788584 * Polynomial.X ^ 10 +
      Polynomial.C 1117288 * Polynomial.X ^ 11 + Polynomial.C 1371276 * Polynomial.X ^ 12 +
      Polynomial.C 1441420 * Polynomial.X ^ 13 + Polynomial.C 1278648 * Polynomial.X ^ 14 +
      Polynomial.C 910392 * Polynomial.X ^ 15 + Polynomial.C 546929 * Polynomial.X ^ 16 +
      Polynomial.C 206657 * Polynomial.X ^ 17 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_34_3 :
    sylowCycleProfile 34 3 =
      1 + Polynomial.C 22 * Polynomial.X + Polynomial.C 220 * Polynomial.X ^ 2 +
      Polynomial.C 1374 * Polynomial.X ^ 3 + Polynomial.C 6144 * Polynomial.X ^ 4 +
      Polynomial.C 20832 * Polynomial.X ^ 5 + Polynomial.C 54732 * Polynomial.X ^ 6 +
      Polynomial.C 112440 * Polynomial.X ^ 7 + Polynomial.C 177888 * Polynomial.X ^ 8 +
      Polynomial.C 221642 * Polynomial.X ^ 9 + Polynomial.C 220136 * Polynomial.X ^ 10 +
      Polynomial.C 122792 * Polynomial.X ^ 11 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_34_5 :
    sylowCycleProfile 34 5 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 240 * Polynomial.X ^ 2 +
      Polynomial.C 1280 * Polynomial.X ^ 3 + Polynomial.C 3840 * Polynomial.X ^ 4 +
      Polynomial.C 8644 * Polynomial.X ^ 5 + Polynomial.C 14096 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_34_7 :
    sylowCycleProfile 34 7 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 216 * Polynomial.X ^ 2 +
      Polynomial.C 864 * Polynomial.X ^ 3 + Polynomial.C 1296 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_34_11 :
    sylowCycleProfile 34 11 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 300 * Polynomial.X ^ 2 +
      Polynomial.C 1000 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_34_13 :
    sylowCycleProfile 34 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_34_17 :
    sylowCycleProfile 34 17 =
      1 + Polynomial.C 32 * Polynomial.X + Polynomial.C 256 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_34_19 :
    sylowCycleProfile 34 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_34_23 :
    sylowCycleProfile 34 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_34_29 :
    sylowCycleProfile 34 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_34_31 :
    sylowCycleProfile 34 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_34_lt :
    paperSymmetricFiniteBudget 34 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  have hIcc17 : Finset.Icc 1 17 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_34_2,
    paperProfile_34_3,
    paperProfile_34_5,
    paperProfile_34_7,
    paperProfile_34_11,
    paperProfile_34_13,
    paperProfile_34_17,
    paperProfile_34_19,
    paperProfile_34_23,
    paperProfile_34_29,
    paperProfile_34_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc6,
    hIcc11,
    hIcc17,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_34_lt :
    paperAlternatingFiniteBudget 34 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  have hIcc17 : Finset.Icc 1 17 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_34_2,
    paperProfile_34_3,
    paperProfile_34_5,
    paperProfile_34_7,
    paperProfile_34_11,
    paperProfile_34_13,
    paperProfile_34_17,
    paperProfile_34_19,
    paperProfile_34_23,
    paperProfile_34_29,
    paperProfile_34_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc6,
    hIcc11,
    hIcc17,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_35_2 :
    sylowCycleProfile 35 2 =
      1 + Polynomial.C 17 * Polynomial.X + Polynomial.C 152 * Polynomial.X ^ 2 +
      Polynomial.C 920 * Polynomial.X ^ 3 + Polynomial.C 4204 * Polynomial.X ^ 4 +
      Polynomial.C 15340 * Polynomial.X ^ 5 + Polynomial.C 46280 * Polynomial.X ^ 6 +
      Polynomial.C 117832 * Polynomial.X ^ 7 + Polynomial.C 256790 * Polynomial.X ^ 8 +
      Polynomial.C 482998 * Polynomial.X ^ 9 + Polynomial.C 788584 * Polynomial.X ^ 10 +
      Polynomial.C 1117288 * Polynomial.X ^ 11 + Polynomial.C 1371276 * Polynomial.X ^ 12 +
      Polynomial.C 1441420 * Polynomial.X ^ 13 + Polynomial.C 1278648 * Polynomial.X ^ 14 +
      Polynomial.C 910392 * Polynomial.X ^ 15 + Polynomial.C 546929 * Polynomial.X ^ 16 +
      Polynomial.C 206657 * Polynomial.X ^ 17 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_35_3 :
    sylowCycleProfile 35 3 =
      1 + Polynomial.C 22 * Polynomial.X + Polynomial.C 220 * Polynomial.X ^ 2 +
      Polynomial.C 1374 * Polynomial.X ^ 3 + Polynomial.C 6144 * Polynomial.X ^ 4 +
      Polynomial.C 20832 * Polynomial.X ^ 5 + Polynomial.C 54732 * Polynomial.X ^ 6 +
      Polynomial.C 112440 * Polynomial.X ^ 7 + Polynomial.C 177888 * Polynomial.X ^ 8 +
      Polynomial.C 221642 * Polynomial.X ^ 9 + Polynomial.C 220136 * Polynomial.X ^ 10 +
      Polynomial.C 122792 * Polynomial.X ^ 11 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_35_5 :
    sylowCycleProfile 35 5 =
      1 + Polynomial.C 28 * Polynomial.X + Polynomial.C 336 * Polynomial.X ^ 2 +
      Polynomial.C 2240 * Polynomial.X ^ 3 + Polynomial.C 8960 * Polynomial.X ^ 4 +
      Polynomial.C 24004 * Polynomial.X ^ 5 + Polynomial.C 48672 * Polynomial.X ^ 6 +
      Polynomial.C 56384 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_35_7 :
    sylowCycleProfile 35 7 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 360 * Polynomial.X ^ 2 +
      Polynomial.C 2160 * Polynomial.X ^ 3 + Polynomial.C 6480 * Polynomial.X ^ 4 +
      Polynomial.C 7776 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_35_11 :
    sylowCycleProfile 35 11 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 300 * Polynomial.X ^ 2 +
      Polynomial.C 1000 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_35_13 :
    sylowCycleProfile 35 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_35_17 :
    sylowCycleProfile 35 17 =
      1 + Polynomial.C 32 * Polynomial.X + Polynomial.C 256 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_35_19 :
    sylowCycleProfile 35 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_35_23 :
    sylowCycleProfile 35 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_35_29 :
    sylowCycleProfile 35 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_35_31 :
    sylowCycleProfile 35 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_35_lt :
    paperSymmetricFiniteBudget 35 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  have hIcc17 : Finset.Icc 1 17 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_35_2,
    paperProfile_35_3,
    paperProfile_35_5,
    paperProfile_35_7,
    paperProfile_35_11,
    paperProfile_35_13,
    paperProfile_35_17,
    paperProfile_35_19,
    paperProfile_35_23,
    paperProfile_35_29,
    paperProfile_35_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc11,
    hIcc17,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_35_lt :
    paperAlternatingFiniteBudget 35 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  have hIcc17 : Finset.Icc 1 17 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_35_2,
    paperProfile_35_3,
    paperProfile_35_5,
    paperProfile_35_7,
    paperProfile_35_11,
    paperProfile_35_13,
    paperProfile_35_17,
    paperProfile_35_19,
    paperProfile_35_23,
    paperProfile_35_29,
    paperProfile_35_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc11,
    hIcc17,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_36_2 :
    sylowCycleProfile 36 2 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 171 * Polynomial.X ^ 2 +
      Polynomial.C 1104 * Polynomial.X ^ 3 + Polynomial.C 5396 * Polynomial.X ^ 4 +
      Polynomial.C 21112 * Polynomial.X ^ 5 + Polynomial.C 68460 * Polynomial.X ^ 6 +
      Polynomial.C 187952 * Polynomial.X ^ 7 + Polynomial.C 443342 * Polynomial.X ^ 8 +
      Polynomial.C 906732 * Polynomial.X ^ 9 + Polynomial.C 1618218 * Polynomial.X ^ 10 +
      Polynomial.C 2525232 * Polynomial.X ^ 11 + Polynomial.C 3446372 * Polynomial.X ^ 12 +
      Polynomial.C 4089464 * Polynomial.X ^ 13 + Polynomial.C 4185852 * Polynomial.X ^ 14 +
      Polynomial.C 3606096 * Polynomial.X ^ 15 + Polynomial.C 2597561 * Polynomial.X ^ 16 +
      Polynomial.C 1434130 * Polynomial.X ^ 17 + Polynomial.C 619971 * Polynomial.X ^ 18 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_36_3 :
    sylowCycleProfile 36 3 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 264 * Polynomial.X ^ 2 +
      Polynomial.C 1832 * Polynomial.X ^ 3 + Polynomial.C 9216 * Polynomial.X ^ 4 +
      Polynomial.C 35712 * Polynomial.X ^ 5 + Polynomial.C 109464 * Polynomial.X ^ 6 +
      Polynomial.C 269856 * Polynomial.X ^ 7 + Polynomial.C 533664 * Polynomial.X ^ 8 +
      Polynomial.C 847202 * Polynomial.X ^ 9 + Polynomial.C 1084620 * Polynomial.X ^ 10 +
      Polynomial.C 1001112 * Polynomial.X ^ 11 + Polynomial.C 798148 * Polynomial.X ^ 12 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_36_5 :
    sylowCycleProfile 36 5 =
      1 + Polynomial.C 28 * Polynomial.X + Polynomial.C 336 * Polynomial.X ^ 2 +
      Polynomial.C 2240 * Polynomial.X ^ 3 + Polynomial.C 8960 * Polynomial.X ^ 4 +
      Polynomial.C 24004 * Polynomial.X ^ 5 + Polynomial.C 48672 * Polynomial.X ^ 6 +
      Polynomial.C 56384 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_36_7 :
    sylowCycleProfile 36 7 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 360 * Polynomial.X ^ 2 +
      Polynomial.C 2160 * Polynomial.X ^ 3 + Polynomial.C 6480 * Polynomial.X ^ 4 +
      Polynomial.C 7776 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_36_11 :
    sylowCycleProfile 36 11 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 300 * Polynomial.X ^ 2 +
      Polynomial.C 1000 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_36_13 :
    sylowCycleProfile 36 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_36_17 :
    sylowCycleProfile 36 17 =
      1 + Polynomial.C 32 * Polynomial.X + Polynomial.C 256 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_36_19 :
    sylowCycleProfile 36 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_36_23 :
    sylowCycleProfile 36 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_36_29 :
    sylowCycleProfile 36 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_36_31 :
    sylowCycleProfile 36 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_36_lt :
    paperSymmetricFiniteBudget 36 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  have hIcc18 : Finset.Icc 1 18 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_36_2,
    paperProfile_36_3,
    paperProfile_36_5,
    paperProfile_36_7,
    paperProfile_36_11,
    paperProfile_36_13,
    paperProfile_36_17,
    paperProfile_36_19,
    paperProfile_36_23,
    paperProfile_36_29,
    paperProfile_36_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc12,
    hIcc18,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_36_lt :
    paperAlternatingFiniteBudget 36 < (1 : ℝ) / 4 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  have hIcc18 : Finset.Icc 1 18 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_36_2,
    paperProfile_36_3,
    paperProfile_36_5,
    paperProfile_36_7,
    paperProfile_36_11,
    paperProfile_36_13,
    paperProfile_36_17,
    paperProfile_36_19,
    paperProfile_36_23,
    paperProfile_36_29,
    paperProfile_36_31,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc12,
    hIcc18,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_37_2 :
    sylowCycleProfile 37 2 =
      1 + Polynomial.C 18 * Polynomial.X + Polynomial.C 171 * Polynomial.X ^ 2 +
      Polynomial.C 1104 * Polynomial.X ^ 3 + Polynomial.C 5396 * Polynomial.X ^ 4 +
      Polynomial.C 21112 * Polynomial.X ^ 5 + Polynomial.C 68460 * Polynomial.X ^ 6 +
      Polynomial.C 187952 * Polynomial.X ^ 7 + Polynomial.C 443342 * Polynomial.X ^ 8 +
      Polynomial.C 906732 * Polynomial.X ^ 9 + Polynomial.C 1618218 * Polynomial.X ^ 10 +
      Polynomial.C 2525232 * Polynomial.X ^ 11 + Polynomial.C 3446372 * Polynomial.X ^ 12 +
      Polynomial.C 4089464 * Polynomial.X ^ 13 + Polynomial.C 4185852 * Polynomial.X ^ 14 +
      Polynomial.C 3606096 * Polynomial.X ^ 15 + Polynomial.C 2597561 * Polynomial.X ^ 16 +
      Polynomial.C 1434130 * Polynomial.X ^ 17 + Polynomial.C 619971 * Polynomial.X ^ 18 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_37_3 :
    sylowCycleProfile 37 3 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 264 * Polynomial.X ^ 2 +
      Polynomial.C 1832 * Polynomial.X ^ 3 + Polynomial.C 9216 * Polynomial.X ^ 4 +
      Polynomial.C 35712 * Polynomial.X ^ 5 + Polynomial.C 109464 * Polynomial.X ^ 6 +
      Polynomial.C 269856 * Polynomial.X ^ 7 + Polynomial.C 533664 * Polynomial.X ^ 8 +
      Polynomial.C 847202 * Polynomial.X ^ 9 + Polynomial.C 1084620 * Polynomial.X ^ 10 +
      Polynomial.C 1001112 * Polynomial.X ^ 11 + Polynomial.C 798148 * Polynomial.X ^ 12 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_37_5 :
    sylowCycleProfile 37 5 =
      1 + Polynomial.C 28 * Polynomial.X + Polynomial.C 336 * Polynomial.X ^ 2 +
      Polynomial.C 2240 * Polynomial.X ^ 3 + Polynomial.C 8960 * Polynomial.X ^ 4 +
      Polynomial.C 24004 * Polynomial.X ^ 5 + Polynomial.C 48672 * Polynomial.X ^ 6 +
      Polynomial.C 56384 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_37_7 :
    sylowCycleProfile 37 7 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 360 * Polynomial.X ^ 2 +
      Polynomial.C 2160 * Polynomial.X ^ 3 + Polynomial.C 6480 * Polynomial.X ^ 4 +
      Polynomial.C 7776 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_37_11 :
    sylowCycleProfile 37 11 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 300 * Polynomial.X ^ 2 +
      Polynomial.C 1000 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_37_13 :
    sylowCycleProfile 37 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_37_17 :
    sylowCycleProfile 37 17 =
      1 + Polynomial.C 32 * Polynomial.X + Polynomial.C 256 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_37_19 :
    sylowCycleProfile 37 19 = 1 + Polynomial.C 18 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_37_23 :
    sylowCycleProfile 37 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_37_29 :
    sylowCycleProfile 37 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_37_31 :
    sylowCycleProfile 37 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_37_37 :
    sylowCycleProfile 37 37 = 1 + Polynomial.C 36 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_37_lt :
    paperSymmetricFiniteBudget 37 < 1 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  have hIcc18 : Finset.Icc 1 18 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_37_2,
    paperProfile_37_3,
    paperProfile_37_5,
    paperProfile_37_7,
    paperProfile_37_11,
    paperProfile_37_13,
    paperProfile_37_17,
    paperProfile_37_19,
    paperProfile_37_23,
    paperProfile_37_29,
    paperProfile_37_31,
    paperProfile_37_37,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc12,
    hIcc18,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_37_lt :
    paperAlternatingFiniteBudget 37 < (1 : ℝ) / 4 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  have hIcc18 : Finset.Icc 1 18 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_37_2,
    paperProfile_37_3,
    paperProfile_37_5,
    paperProfile_37_7,
    paperProfile_37_11,
    paperProfile_37_13,
    paperProfile_37_17,
    paperProfile_37_19,
    paperProfile_37_23,
    paperProfile_37_29,
    paperProfile_37_31,
    paperProfile_37_37,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc12,
    hIcc18,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_38_2 :
    sylowCycleProfile 38 2 =
      1 + Polynomial.C 19 * Polynomial.X + Polynomial.C 189 * Polynomial.X ^ 2 +
      Polynomial.C 1275 * Polynomial.X ^ 3 + Polynomial.C 6500 * Polynomial.X ^ 4 +
      Polynomial.C 26508 * Polynomial.X ^ 5 + Polynomial.C 89572 * Polynomial.X ^ 6 +
      Polynomial.C 256412 * Polynomial.X ^ 7 + Polynomial.C 631294 * Polynomial.X ^ 8 +
      Polynomial.C 1350074 * Polynomial.X ^ 9 + Polynomial.C 2524950 * Polynomial.X ^ 10 +
      Polynomial.C 4143450 * Polynomial.X ^ 11 + Polynomial.C 5971604 * Polynomial.X ^ 12 +
      Polynomial.C 7535836 * Polynomial.X ^ 13 + Polynomial.C 8275316 * Polynomial.X ^ 14 +
      Polynomial.C 7791948 * Polynomial.X ^ 15 + Polynomial.C 6203657 * Polynomial.X ^ 16 +
      Polynomial.C 4031691 * Polynomial.X ^ 17 + Polynomial.C 2054101 * Polynomial.X ^ 18 +
      Polynomial.C 619971 * Polynomial.X ^ 19 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_3 :
    sylowCycleProfile 38 3 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 264 * Polynomial.X ^ 2 +
      Polynomial.C 1832 * Polynomial.X ^ 3 + Polynomial.C 9216 * Polynomial.X ^ 4 +
      Polynomial.C 35712 * Polynomial.X ^ 5 + Polynomial.C 109464 * Polynomial.X ^ 6 +
      Polynomial.C 269856 * Polynomial.X ^ 7 + Polynomial.C 533664 * Polynomial.X ^ 8 +
      Polynomial.C 847202 * Polynomial.X ^ 9 + Polynomial.C 1084620 * Polynomial.X ^ 10 +
      Polynomial.C 1001112 * Polynomial.X ^ 11 + Polynomial.C 798148 * Polynomial.X ^ 12 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_5 :
    sylowCycleProfile 38 5 =
      1 + Polynomial.C 28 * Polynomial.X + Polynomial.C 336 * Polynomial.X ^ 2 +
      Polynomial.C 2240 * Polynomial.X ^ 3 + Polynomial.C 8960 * Polynomial.X ^ 4 +
      Polynomial.C 24004 * Polynomial.X ^ 5 + Polynomial.C 48672 * Polynomial.X ^ 6 +
      Polynomial.C 56384 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_7 :
    sylowCycleProfile 38 7 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 360 * Polynomial.X ^ 2 +
      Polynomial.C 2160 * Polynomial.X ^ 3 + Polynomial.C 6480 * Polynomial.X ^ 4 +
      Polynomial.C 7776 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_11 :
    sylowCycleProfile 38 11 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 300 * Polynomial.X ^ 2 +
      Polynomial.C 1000 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_13 :
    sylowCycleProfile 38 13 =
      1 + Polynomial.C 24 * Polynomial.X + Polynomial.C 144 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_17 :
    sylowCycleProfile 38 17 =
      1 + Polynomial.C 32 * Polynomial.X + Polynomial.C 256 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_19 :
    sylowCycleProfile 38 19 =
      1 + Polynomial.C 36 * Polynomial.X + Polynomial.C 324 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_38_23 :
    sylowCycleProfile 38 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_38_29 :
    sylowCycleProfile 38 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_38_31 :
    sylowCycleProfile 38 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_38_37 :
    sylowCycleProfile 38 37 = 1 + Polynomial.C 36 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_38_lt :
    paperSymmetricFiniteBudget 38 < 1 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  have hIcc19 : Finset.Icc 1 19 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_38_2,
    paperProfile_38_3,
    paperProfile_38_5,
    paperProfile_38_7,
    paperProfile_38_11,
    paperProfile_38_13,
    paperProfile_38_17,
    paperProfile_38_19,
    paperProfile_38_23,
    paperProfile_38_29,
    paperProfile_38_31,
    paperProfile_38_37,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc12,
    hIcc19,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_38_lt :
    paperAlternatingFiniteBudget 38 < (1 : ℝ) / 4 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  have hIcc19 : Finset.Icc 1 19 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_38_2,
    paperProfile_38_3,
    paperProfile_38_5,
    paperProfile_38_7,
    paperProfile_38_11,
    paperProfile_38_13,
    paperProfile_38_17,
    paperProfile_38_19,
    paperProfile_38_23,
    paperProfile_38_29,
    paperProfile_38_31,
    paperProfile_38_37,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc12,
    hIcc19,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperProfile_39_2 :
    sylowCycleProfile 39 2 =
      1 + Polynomial.C 19 * Polynomial.X + Polynomial.C 189 * Polynomial.X ^ 2 +
      Polynomial.C 1275 * Polynomial.X ^ 3 + Polynomial.C 6500 * Polynomial.X ^ 4 +
      Polynomial.C 26508 * Polynomial.X ^ 5 + Polynomial.C 89572 * Polynomial.X ^ 6 +
      Polynomial.C 256412 * Polynomial.X ^ 7 + Polynomial.C 631294 * Polynomial.X ^ 8 +
      Polynomial.C 1350074 * Polynomial.X ^ 9 + Polynomial.C 2524950 * Polynomial.X ^ 10 +
      Polynomial.C 4143450 * Polynomial.X ^ 11 + Polynomial.C 5971604 * Polynomial.X ^ 12 +
      Polynomial.C 7535836 * Polynomial.X ^ 13 + Polynomial.C 8275316 * Polynomial.X ^ 14 +
      Polynomial.C 7791948 * Polynomial.X ^ 15 + Polynomial.C 6203657 * Polynomial.X ^ 16 +
      Polynomial.C 4031691 * Polynomial.X ^ 17 + Polynomial.C 2054101 * Polynomial.X ^ 18 +
      Polynomial.C 619971 * Polynomial.X ^ 19 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_3 :
    sylowCycleProfile 39 3 =
      1 + Polynomial.C 26 * Polynomial.X + Polynomial.C 312 * Polynomial.X ^ 2 +
      Polynomial.C 2360 * Polynomial.X ^ 3 + Polynomial.C 12880 * Polynomial.X ^ 4 +
      Polynomial.C 54144 * Polynomial.X ^ 5 + Polynomial.C 180888 * Polynomial.X ^ 6 +
      Polynomial.C 488784 * Polynomial.X ^ 7 + Polynomial.C 1073376 * Polynomial.X ^ 8 +
      Polynomial.C 1914530 * Polynomial.X ^ 9 + Polynomial.C 2779024 * Polynomial.X ^ 10 +
      Polynomial.C 3170352 * Polynomial.X ^ 11 + Polynomial.C 2800372 * Polynomial.X ^ 12 +
      Polynomial.C 1596296 * Polynomial.X ^ 13 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_5 :
    sylowCycleProfile 39 5 =
      1 + Polynomial.C 28 * Polynomial.X + Polynomial.C 336 * Polynomial.X ^ 2 +
      Polynomial.C 2240 * Polynomial.X ^ 3 + Polynomial.C 8960 * Polynomial.X ^ 4 +
      Polynomial.C 24004 * Polynomial.X ^ 5 + Polynomial.C 48672 * Polynomial.X ^ 6 +
      Polynomial.C 56384 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_7 :
    sylowCycleProfile 39 7 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 360 * Polynomial.X ^ 2 +
      Polynomial.C 2160 * Polynomial.X ^ 3 + Polynomial.C 6480 * Polynomial.X ^ 4 +
      Polynomial.C 7776 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_11 :
    sylowCycleProfile 39 11 =
      1 + Polynomial.C 30 * Polynomial.X + Polynomial.C 300 * Polynomial.X ^ 2 +
      Polynomial.C 1000 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_13 :
    sylowCycleProfile 39 13 =
      1 + Polynomial.C 36 * Polynomial.X + Polynomial.C 432 * Polynomial.X ^ 2 +
      Polynomial.C 1728 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_17 :
    sylowCycleProfile 39 17 =
      1 + Polynomial.C 32 * Polynomial.X + Polynomial.C 256 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_19 :
    sylowCycleProfile 39 19 =
      1 + Polynomial.C 36 * Polynomial.X + Polynomial.C 324 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_39_23 :
    sylowCycleProfile 39 23 = 1 + Polynomial.C 22 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_39_29 :
    sylowCycleProfile 39 29 = 1 + Polynomial.C 28 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_39_31 :
    sylowCycleProfile 39 31 = 1 + Polynomial.C 30 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_39_37 :
    sylowCycleProfile 39 37 = 1 + Polynomial.C 36 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricFiniteBudget_39_lt :
    paperSymmetricFiniteBudget 39 < 1 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc13 : Finset.Icc 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  have hIcc19 : Finset.Icc 1 19 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} := by decide
  norm_num [paperSymmetricFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_39_2,
    paperProfile_39_3,
    paperProfile_39_5,
    paperProfile_39_7,
    paperProfile_39_11,
    paperProfile_39_13,
    paperProfile_39_17,
    paperProfile_39_19,
    paperProfile_39_23,
    paperProfile_39_29,
    paperProfile_39_31,
    paperProfile_39_37,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc13,
    hIcc19,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingFiniteBudget_39_lt :
    paperAlternatingFiniteBudget 39 < (1 : ℝ) / 4 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc13 : Finset.Icc 1 13 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by decide
  have hIcc19 : Finset.Icc 1 19 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_39_2,
    paperProfile_39_3,
    paperProfile_39_5,
    paperProfile_39_7,
    paperProfile_39_11,
    paperProfile_39_13,
    paperProfile_39_17,
    paperProfile_39_19,
    paperProfile_39_23,
    paperProfile_39_29,
    paperProfile_39_31,
    paperProfile_39_37,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    hIcc13,
    hIcc19,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

/-! ## Passing exact finite budgets to arbitrary prime families -/

private theorem paperSmallPrime_mem {p : ℕ} (hp : p.Prime) (hsmall : p < 40) :
    p ∈ paperSmallPrimes := by
  have checked : ∀ q ∈ Finset.range 40, q.Prime → q ∈ paperSmallPrimes := by
    decide
  exact checked p (Finset.mem_range.mpr hsmall) hp

private theorem paper_sum_prime_rows_le
    {I : Type*} (s : Finset I) (p : I → ℕ) (n : ℕ) (hn : n < 40)
    (f : ℕ → ℝ) (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s)
    (hnonneg : ∀ q, 0 ≤ f q) (hzero : ∀ q, n < q → f q = 0) :
    (∑ i ∈ s, f (p i)) ≤ ∑ q ∈ paperSmallPrimes, f q := by
  classical
  have hcut :
      (∑ i ∈ s.filter (fun i ↦ p i ≤ n), f (p i)) = ∑ i ∈ s, f (p i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    apply hzero
    exact Nat.lt_of_not_ge (fun hle ↦
      hnot (Finset.mem_filter.mpr ⟨hi, hle⟩))
  rw [← hcut]
  apply Finset.sum_le_sum_of_injOn p
  · intro i hi j hj hij
    exact hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨his, hin⟩ := Finset.mem_filter.mp hi
    exact paperSmallPrime_mem (hp i his) (hin.trans_lt hn)
  · intro i _hi
    exact le_rfl
  · intro q _hq _hnot
    exact hnonneg q

private theorem paper_symmetric_cost_nonneg (n p : ℕ) :
    0 ≤ symmetricSylowProfileQuadraticCost n p := by
  unfold symmetricSylowProfileQuadraticCost
  apply Finset.sum_nonneg
  intro j _hj
  positivity

private theorem paper_symmetric_cost_zero {n p : ℕ} (h : n < p) :
    symmetricSylowProfileQuadraticCost n p = 0 := by
  simp [symmetricSylowProfileQuadraticCost, Nat.div_eq_of_lt h]

private theorem paper_alternating_cost_nonneg (n p : ℕ) :
    0 ≤ alternatingSylowProfileQuadraticCost n p := by
  by_cases htwo : p = 2
  · rw [alternatingSylowProfileQuadraticCost, ite_eq_left htwo]
    apply Finset.sum_nonneg
    intro j _hj
    split_ifs <;> positivity
  · rw [alternatingSylowProfileQuadraticCost, ite_eq_right htwo]
    exact paper_symmetric_cost_nonneg n p

private theorem paper_alternating_cost_zero {n p : ℕ} (h : n < p) :
    alternatingSylowProfileQuadraticCost n p = 0 := by
  by_cases htwo : p = 2
  · subst p
    simp [alternatingSylowProfileQuadraticCost, Nat.div_eq_of_lt h]
  · rw [alternatingSylowProfileQuadraticCost, ite_eq_right htwo]
    exact paper_symmetric_cost_zero h

private theorem paperSymmetricFiniteBudget_lt {n : ℕ}
    (hn : n = 11 ∨ n = 13 ∨ n = 15 ∨ (17 ≤ n ∧ n < 40)) :
    paperSymmetricFiniteBudget n < 1 := by
  rcases hn with rfl | rfl | rfl | ⟨hlo, hhi⟩
  · exact paperSymmetricFiniteBudget_11_lt
  · exact paperSymmetricFiniteBudget_13_lt
  · exact paperSymmetricFiniteBudget_15_lt
  · interval_cases n
    · exact paperSymmetricFiniteBudget_17_lt
    · exact paperSymmetricFiniteBudget_18_lt
    · exact paperSymmetricFiniteBudget_19_lt
    · exact paperSymmetricFiniteBudget_20_lt
    · exact paperSymmetricFiniteBudget_21_lt
    · exact paperSymmetricFiniteBudget_22_lt
    · exact paperSymmetricFiniteBudget_23_lt
    · exact paperSymmetricFiniteBudget_24_lt
    · exact paperSymmetricFiniteBudget_25_lt
    · exact paperSymmetricFiniteBudget_26_lt
    · exact paperSymmetricFiniteBudget_27_lt
    · exact paperSymmetricFiniteBudget_28_lt
    · exact paperSymmetricFiniteBudget_29_lt
    · exact paperSymmetricFiniteBudget_30_lt
    · exact paperSymmetricFiniteBudget_31_lt
    · exact paperSymmetricFiniteBudget_32_lt
    · exact paperSymmetricFiniteBudget_33_lt
    · exact paperSymmetricFiniteBudget_34_lt
    · exact paperSymmetricFiniteBudget_35_lt
    · exact paperSymmetricFiniteBudget_36_lt
    · exact paperSymmetricFiniteBudget_37_lt
    · exact paperSymmetricFiniteBudget_38_lt
    · exact paperSymmetricFiniteBudget_39_lt

private theorem paperAlternatingFiniteBudget_lt {n : ℕ}
    (hn : n = 23 ∨ (25 ≤ n ∧ n < 40)) :
    paperAlternatingFiniteBudget n < (1 : ℝ) / 4 := by
  rcases hn with rfl | ⟨hlo, hhi⟩
  · exact paperAlternatingFiniteBudget_23_lt
  · interval_cases n
    · exact paperAlternatingFiniteBudget_25_lt
    · exact paperAlternatingFiniteBudget_26_lt
    · exact paperAlternatingFiniteBudget_27_lt
    · exact paperAlternatingFiniteBudget_28_lt
    · exact paperAlternatingFiniteBudget_29_lt
    · exact paperAlternatingFiniteBudget_30_lt
    · exact paperAlternatingFiniteBudget_31_lt
    · exact paperAlternatingFiniteBudget_32_lt
    · exact paperAlternatingFiniteBudget_33_lt
    · exact paperAlternatingFiniteBudget_34_lt
    · exact paperAlternatingFiniteBudget_35_lt
    · exact paperAlternatingFiniteBudget_36_lt
    · exact paperAlternatingFiniteBudget_37_lt
    · exact paperAlternatingFiniteBudget_38_lt
    · exact paperAlternatingFiniteBudget_39_lt

/-- The exact finite symmetric budgets apply to every injectively
prime-labelled family, including arbitrary subsets of prime rows. -/
theorem sum_symmetricSylowProfileQuadraticCost_lt_one_finite_degrees
    {I : Type*} (s : Finset I) (p : I → ℕ) (n : ℕ)
    (hn : n = 11 ∨ n = 13 ∨ n = 15 ∨ (17 ≤ n ∧ n < 40))
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    (∑ i ∈ s, symmetricSylowProfileQuadraticCost n (p i)) < 1 := by
  have hn40 : n < 40 := by omega
  exact (paper_sum_prime_rows_le s p n hn40
    (symmetricSylowProfileQuadraticCost n) hp hinj
    (paper_symmetric_cost_nonneg n) (fun _ h ↦ paper_symmetric_cost_zero h)).trans_lt
    (paperSymmetricFiniteBudget_lt hn)

/-- The finite alternating budgets leave the factor-four reserve needed
by the existing index-two comparison theorem. -/
theorem sum_alternatingSylowProfileQuadraticCost_lt_one_div_four_finite_degrees
    {I : Type*} {n : ℕ} (s : Finset I) (p : I → ℕ)
    (hn : n = 23 ∨ (25 ≤ n ∧ n < 40))
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    (∑ i ∈ s, alternatingSylowProfileQuadraticCost n (p i)) < (1 : ℝ) / 4 := by
  have hn40 : n < 40 := by omega
  exact (paper_sum_prime_rows_le s p n hn40
    (alternatingSylowProfileQuadraticCost n) hp hinj
    (paper_alternating_cost_nonneg n) (fun _ h ↦ paper_alternating_cost_zero h)).trans_lt
    (paperAlternatingFiniteBudget_lt hn)

/-! ## Additional half-budgets and cyclic-subgroup budgets -/

private theorem paperProfile_7_2 :
    sylowCycleProfile 7 2 =
      1 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 * Polynomial.X ^ 2 +
      Polynomial.C 3 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_7_3 :
    sylowCycleProfile 7 3 =
      1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 4 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_7_5 :
    sylowCycleProfile 7 5 = 1 + Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_7_7 :
    sylowCycleProfile 7 7 = 1 + Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_14_2 :
    sylowCycleProfile 14 2 =
      1 + Polynomial.C 7 * Polynomial.X + Polynomial.C 27 * Polynomial.X ^ 2 +
      Polynomial.C 65 * Polynomial.X ^ 3 + Polynomial.C 115 * Polynomial.X ^ 4 +
      Polynomial.C 141 * Polynomial.X ^ 5 + Polynomial.C 121 * Polynomial.X ^ 6 +
      Polynomial.C 51 * Polynomial.X ^ 7 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_14_3 :
    sylowCycleProfile 14 3 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 24 * Polynomial.X ^ 2 +
      Polynomial.C 50 * Polynomial.X ^ 3 + Polynomial.C 52 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_14_5 :
    sylowCycleProfile 14 5 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_14_7 :
    sylowCycleProfile 14 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_14_11 :
    sylowCycleProfile 14 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_14_13 :
    sylowCycleProfile 14 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_16_2 :
    sylowCycleProfile 16 2 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 +
      Polynomial.C 104 * Polynomial.X ^ 3 + Polynomial.C 230 * Polynomial.X ^ 4 +
      Polynomial.C 376 * Polynomial.X ^ 5 + Polynomial.C 484 * Polynomial.X ^ 6 +
      Polynomial.C 408 * Polynomial.X ^ 7 + Polynomial.C 417 * Polynomial.X ^ 8 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_16_3 :
    sylowCycleProfile 16 3 =
      1 + Polynomial.C 10 * Polynomial.X + Polynomial.C 40 * Polynomial.X ^ 2 +
      Polynomial.C 98 * Polynomial.X ^ 3 + Polynomial.C 152 * Polynomial.X ^ 4 +
      Polynomial.C 104 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_16_5 :
    sylowCycleProfile 16 5 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 48 * Polynomial.X ^ 2 +
      Polynomial.C 64 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_16_7 :
    sylowCycleProfile 16 7 =
      1 + Polynomial.C 12 * Polynomial.X + Polynomial.C 36 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem paperProfile_16_11 :
    sylowCycleProfile 16 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem paperProfile_16_13 :
    sylowCycleProfile 16 13 = 1 + Polynomial.C 12 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_11_lt :
    paperAlternatingFiniteBudget 11 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_11_2,
    paperProfile_11_3,
    paperProfile_11_5,
    paperProfile_11_7,
    paperProfile_11_11,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_13_lt :
    paperAlternatingFiniteBudget 13 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_13_2,
    paperProfile_13_3,
    paperProfile_13_5,
    paperProfile_13_7,
    paperProfile_13_11,
    paperProfile_13_13,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_14_lt :
    paperAlternatingFiniteBudget 14 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_14_2,
    paperProfile_14_3,
    paperProfile_14_5,
    paperProfile_14_7,
    paperProfile_14_11,
    paperProfile_14_13,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc7,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_15_lt :
    paperAlternatingFiniteBudget 15 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_15_2,
    paperProfile_15_3,
    paperProfile_15_5,
    paperProfile_15_7,
    paperProfile_15_11,
    paperProfile_15_13,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc5,
    hIcc7,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_16_lt :
    paperAlternatingFiniteBudget 16 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_16_2,
    paperProfile_16_3,
    paperProfile_16_5,
    paperProfile_16_7,
    paperProfile_16_11,
    paperProfile_16_13,
    hIcc0,
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
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_17_lt :
    paperAlternatingFiniteBudget 17 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_17_2,
    paperProfile_17_3,
    paperProfile_17_5,
    paperProfile_17_7,
    paperProfile_17_11,
    paperProfile_17_13,
    paperProfile_17_17,
    hIcc0,
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
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_18_lt :
    paperAlternatingFiniteBudget 18 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_18_2,
    paperProfile_18_3,
    paperProfile_18_5,
    paperProfile_18_7,
    paperProfile_18_11,
    paperProfile_18_13,
    paperProfile_18_17,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc6,
    hIcc9,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_19_lt :
    paperAlternatingFiniteBudget 19 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc9 : Finset.Icc 1 9 = {1, 2, 3, 4, 5, 6, 7, 8, 9} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_19_2,
    paperProfile_19_3,
    paperProfile_19_5,
    paperProfile_19_7,
    paperProfile_19_11,
    paperProfile_19_13,
    paperProfile_19_17,
    paperProfile_19_19,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc6,
    hIcc9,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_20_lt :
    paperAlternatingFiniteBudget 20 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_20_2,
    paperProfile_20_3,
    paperProfile_20_5,
    paperProfile_20_7,
    paperProfile_20_11,
    paperProfile_20_13,
    paperProfile_20_17,
    paperProfile_20_19,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc4,
    hIcc6,
    hIcc10,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_21_lt :
    paperAlternatingFiniteBudget 21 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc10 : Finset.Icc 1 10 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_21_2,
    paperProfile_21_3,
    paperProfile_21_5,
    paperProfile_21_7,
    paperProfile_21_11,
    paperProfile_21_13,
    paperProfile_21_17,
    paperProfile_21_19,
    hIcc0,
    hIcc1,
    hIcc3,
    hIcc4,
    hIcc7,
    hIcc10,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_22_lt :
    paperAlternatingFiniteBudget 22 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc7 : Finset.Icc 1 7 = {1, 2, 3, 4, 5, 6, 7} := by decide
  have hIcc11 : Finset.Icc 1 11 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_22_2,
    paperProfile_22_3,
    paperProfile_22_5,
    paperProfile_22_7,
    paperProfile_22_11,
    paperProfile_22_13,
    paperProfile_22_17,
    paperProfile_22_19,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc7,
    hIcc11,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingHalfBudget_24_lt :
    paperAlternatingFiniteBudget 24 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc8 : Finset.Icc 1 8 = {1, 2, 3, 4, 5, 6, 7, 8} := by decide
  have hIcc12 : Finset.Icc 1 12 = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12} := by decide
  norm_num [paperAlternatingFiniteBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_24_2,
    paperProfile_24_3,
    paperProfile_24_5,
    paperProfile_24_7,
    paperProfile_24_11,
    paperProfile_24_13,
    paperProfile_24_17,
    paperProfile_24_19,
    paperProfile_24_23,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    hIcc4,
    hIcc8,
    hIcc12,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem paperAlternatingHalfBudget_lt {n : ℕ}
    (hn : n = 11 ∨ (13 ≤ n ∧ n < 40)) :
    paperAlternatingFiniteBudget n < (1 : ℝ) / 2 := by
  rcases hn with rfl | ⟨hlo, hhi⟩
  · exact paperAlternatingHalfBudget_11_lt
  · by_cases hlarge : 25 ≤ n
    · exact (paperAlternatingFiniteBudget_lt (Or.inr ⟨hlarge, hhi⟩)).trans (by norm_num)
    · have hhi' : n ≤ 24 := by omega
      interval_cases n
      · exact paperAlternatingHalfBudget_13_lt
      · exact paperAlternatingHalfBudget_14_lt
      · exact paperAlternatingHalfBudget_15_lt
      · exact paperAlternatingHalfBudget_16_lt
      · exact paperAlternatingHalfBudget_17_lt
      · exact paperAlternatingHalfBudget_18_lt
      · exact paperAlternatingHalfBudget_19_lt
      · exact paperAlternatingHalfBudget_20_lt
      · exact paperAlternatingHalfBudget_21_lt
      · exact paperAlternatingHalfBudget_22_lt
      · exact paperAlternatingFiniteBudget_23_lt.trans (by norm_num)
      · exact paperAlternatingHalfBudget_24_lt

/-- Exact half-budgets for the improved index-two transfer. -/
theorem sum_alternatingSylowProfileQuadraticCost_lt_one_div_two_finite_degrees
    {I : Type*} {n : ℕ} (s : Finset I) (p : I → ℕ)
    (hn : n = 11 ∨ (13 ≤ n ∧ n < 40))
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    (∑ i ∈ s, alternatingSylowProfileQuadraticCost n (p i)) < (1 : ℝ) / 2 := by
  have hn40 : n < 40 := by omega
  exact (paper_sum_prime_rows_le s p n hn40
    (alternatingSylowProfileQuadraticCost n) hp hinj
    (paper_alternating_cost_nonneg n) (fun _ h ↦ paper_alternating_cost_zero h)).trans_lt
    (paperAlternatingHalfBudget_lt hn)

private def paperSymmetricCyclicBudget (n : ℕ) : ℝ :=
  ∑ p ∈ paperSmallPrimes,
    symmetricSylowProfileQuadraticCost n p / ((p - 1 : ℕ) : ℝ)

private def paperAlternatingCyclicBudget (n : ℕ) : ℝ :=
  ∑ p ∈ paperSmallPrimes,
    alternatingSylowProfileQuadraticCost n p / ((p - 1 : ℕ) : ℝ)

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperSymmetricCyclicBudget_seven_lt :
    paperSymmetricCyclicBudget 7 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  norm_num [paperSymmetricCyclicBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    paperProfile_7_2,
    paperProfile_7_3,
    paperProfile_7_5,
    paperProfile_7_7,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

set_option maxHeartbeats 2000000 in
-- Exact factorial and polynomial arithmetic exceeds the default elaboration budget.
private theorem paperAlternatingCyclicBudget_seven_lt :
    paperAlternatingCyclicBudget 7 < (1 : ℝ) / 2 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  norm_num [paperAlternatingCyclicBudget,
    paperSmallPrimes,
    symmetricSylowProfileQuadraticCost,
    alternatingSylowProfileQuadraticCost,
    paperProfile_7_2,
    paperProfile_7_3,
    paperProfile_7_5,
    paperProfile_7_7,
    hIcc0,
    hIcc1,
    hIcc2,
    hIcc3,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

/-- The cyclic-subgroup refinement gives a strict degree-seven budget. -/
theorem sum_symmetricSylowProfileCyclicCost_seven_lt_one
    {I : Type*} (s : Finset I) (p : I → ℕ)
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    (∑ i ∈ s, symmetricSylowProfileQuadraticCost 7 (p i) /
      ((p i - 1 : ℕ) : ℝ)) < 1 := by
  apply (paper_sum_prime_rows_le s p 7 (by norm_num)
    (fun q ↦ symmetricSylowProfileQuadraticCost 7 q / ((q - 1 : ℕ) : ℝ))
    hp hinj ?_ ?_).trans_lt paperSymmetricCyclicBudget_seven_lt
  · intro q
    exact div_nonneg (paper_symmetric_cost_nonneg 7 q) (Nat.cast_nonneg _)
  · intro q hq
    rw [paper_symmetric_cost_zero hq, zero_div]

/-- The cyclic-subgroup refinement gives a strict degree-seven budget. -/
theorem sum_alternatingSylowProfileCyclicCost_seven_lt_one_div_two
    {I : Type*} (s : Finset I) (p : I → ℕ)
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    (∑ i ∈ s, alternatingSylowProfileQuadraticCost 7 (p i) /
      ((p i - 1 : ℕ) : ℝ)) < (1 : ℝ) / 2 := by
  apply (paper_sum_prime_rows_le s p 7 (by norm_num)
    (fun q ↦ alternatingSylowProfileQuadraticCost 7 q / ((q - 1 : ℕ) : ℝ))
    hp hinj ?_ ?_).trans_lt paperAlternatingCyclicBudget_seven_lt
  · intro q
    exact div_nonneg (paper_alternating_cost_nonneg 7 q) (Nat.cast_nonneg _)
  · intro q hq
    rw [paper_alternating_cost_zero hq, zero_div]

end LisiSabatini
