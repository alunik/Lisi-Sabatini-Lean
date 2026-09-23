module

public import LisiSabatini.AlternatingSylowCycleProfile

/-!
# The five remaining small alternating cyclic budgets

These exact rational certificates close degrees5,6,9,10,12 once the
normal-subgroup cost equality and cyclic prime-order witness theorem
are applied. They are separate from the large finite-degree certificate
module, so checking these additional cases does not rebuild that module.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

private def smallAlternatingPrimes : Finset ℕ := {2, 3, 5, 7, 11}

private def smallAlternatingCyclicBudget (n : ℕ) : ℝ :=
  ∑ p ∈ smallAlternatingPrimes,
    alternatingSylowProfileQuadraticCost n p / ((p - 1 : ℕ) : ℝ)

private theorem smallAlternatingProfile_5_2 :
    sylowCycleProfile 5 2 =
      1 + Polynomial.C 2 * Polynomial.X + Polynomial.C 3 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_5_3 :
    sylowCycleProfile 5 3 = 1 + Polynomial.C 2 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingProfile_5_5 :
    sylowCycleProfile 5 5 = 1 + Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingCyclicBudget_5_lt :
    smallAlternatingCyclicBudget 5 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  norm_num [smallAlternatingCyclicBudget,
    smallAlternatingPrimes,
    alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost,
    smallAlternatingProfile_5_2,
    smallAlternatingProfile_5_3,
    smallAlternatingProfile_5_5,
    hIcc0,
    hIcc1,
    hIcc2,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem smallAlternatingProfile_6_2 :
    sylowCycleProfile 6 2 =
      1 + Polynomial.C 3 * Polynomial.X + Polynomial.C 5 * Polynomial.X ^ 2 +
      Polynomial.C 3 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_6_3 :
    sylowCycleProfile 6 3 =
      1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 4 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_6_5 :
    sylowCycleProfile 6 5 = 1 + Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingCyclicBudget_6_lt :
    smallAlternatingCyclicBudget 6 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  norm_num [smallAlternatingCyclicBudget,
    smallAlternatingPrimes,
    alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost,
    smallAlternatingProfile_6_2,
    smallAlternatingProfile_6_3,
    smallAlternatingProfile_6_5,
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

private theorem smallAlternatingProfile_9_2 :
    sylowCycleProfile 9 2 =
      1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 10 * Polynomial.X ^ 2 +
      Polynomial.C 12 * Polynomial.X ^ 3 + Polynomial.C 17 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_9_3 :
    sylowCycleProfile 9 3 =
      1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 12 * Polynomial.X ^ 2 +
      Polynomial.C 26 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_9_5 :
    sylowCycleProfile 9 5 = 1 + Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingProfile_9_7 :
    sylowCycleProfile 9 7 = 1 + Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingCyclicBudget_9_lt :
    smallAlternatingCyclicBudget 9 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  norm_num [smallAlternatingCyclicBudget,
    smallAlternatingPrimes,
    alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost,
    smallAlternatingProfile_9_2,
    smallAlternatingProfile_9_3,
    smallAlternatingProfile_9_5,
    smallAlternatingProfile_9_7,
    hIcc0,
    hIcc1,
    hIcc3,
    hIcc4,
    Polynomial.coeff_add,
    Polynomial.coeff_C_mul,
    Polynomial.coeff_one,
    Polynomial.coeff_X,
    Polynomial.coeff_X_pow,
    Nat.even_iff,
    primeCycleClassCard,
    Nat.factorial]

private theorem smallAlternatingProfile_10_2 :
    sylowCycleProfile 10 2 =
      1 + Polynomial.C 5 * Polynomial.X + Polynomial.C 14 * Polynomial.X ^ 2 +
      Polynomial.C 22 * Polynomial.X ^ 3 + Polynomial.C 29 * Polynomial.X ^ 4 +
      Polynomial.C 17 * Polynomial.X ^ 5 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_10_3 :
    sylowCycleProfile 10 3 =
      1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 12 * Polynomial.X ^ 2 +
      Polynomial.C 26 * Polynomial.X ^ 3 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_10_5 :
    sylowCycleProfile 10 5 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_10_7 :
    sylowCycleProfile 10 7 = 1 + Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingCyclicBudget_10_lt :
    smallAlternatingCyclicBudget 10 < 1 := by
  have hIcc0 : Finset.Icc 1 0 = ∅ := by decide
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc3 : Finset.Icc 1 3 = {1, 2, 3} := by decide
  have hIcc5 : Finset.Icc 1 5 = {1, 2, 3, 4, 5} := by decide
  norm_num [smallAlternatingCyclicBudget,
    smallAlternatingPrimes,
    alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost,
    smallAlternatingProfile_10_2,
    smallAlternatingProfile_10_3,
    smallAlternatingProfile_10_5,
    smallAlternatingProfile_10_7,
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

private theorem smallAlternatingProfile_12_2 :
    sylowCycleProfile 12 2 =
      1 + Polynomial.C 6 * Polynomial.X + Polynomial.C 21 * Polynomial.X ^ 2 +
      Polynomial.C 44 * Polynomial.X ^ 3 + Polynomial.C 71 * Polynomial.X ^ 4 +
      Polynomial.C 70 * Polynomial.X ^ 5 + Polynomial.C 51 * Polynomial.X ^ 6 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_12_3 :
    sylowCycleProfile 12 3 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 24 * Polynomial.X ^ 2 +
      Polynomial.C 50 * Polynomial.X ^ 3 + Polynomial.C 52 * Polynomial.X ^ 4 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_12_5 :
    sylowCycleProfile 12 5 =
      1 + Polynomial.C 8 * Polynomial.X + Polynomial.C 16 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem smallAlternatingProfile_12_7 :
    sylowCycleProfile 12 7 = 1 + Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingProfile_12_11 :
    sylowCycleProfile 12 11 = 1 + Polynomial.C 10 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem smallAlternatingCyclicBudget_12_lt :
    smallAlternatingCyclicBudget 12 < 1 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  have hIcc4 : Finset.Icc 1 4 = {1, 2, 3, 4} := by decide
  have hIcc6 : Finset.Icc 1 6 = {1, 2, 3, 4, 5, 6} := by decide
  norm_num [smallAlternatingCyclicBudget,
    smallAlternatingPrimes,
    alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost,
    smallAlternatingProfile_12_2,
    smallAlternatingProfile_12_3,
    smallAlternatingProfile_12_5,
    smallAlternatingProfile_12_7,
    smallAlternatingProfile_12_11,
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

private theorem smallAlternatingCyclicBudget_lt {n : ℕ}
    (hn : n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 12) :
    smallAlternatingCyclicBudget n < 1 := by
  rcases hn with rfl | rfl | rfl | rfl | rfl
  · exact smallAlternatingCyclicBudget_5_lt
  · exact smallAlternatingCyclicBudget_6_lt
  · exact smallAlternatingCyclicBudget_9_lt
  · exact smallAlternatingCyclicBudget_10_lt
  · exact smallAlternatingCyclicBudget_12_lt

private theorem smallAlternatingCost_nonneg (n p : ℕ) :
    0 ≤ alternatingSylowProfileQuadraticCost n p := by
  unfold alternatingSylowProfileQuadraticCost
  split_ifs
  · apply Finset.sum_nonneg
    intro j _hj
    split_ifs <;> positivity
  · unfold symmetricSylowProfileQuadraticCost
    apply Finset.sum_nonneg
    intro j _hj
    positivity

private theorem smallAlternatingCost_zero {n p : ℕ} (h : n < p) :
    alternatingSylowProfileQuadraticCost n p = 0 := by
  by_cases htwo : p = 2
  · subst p
    simp [alternatingSylowProfileQuadraticCost, Nat.div_eq_of_lt h]
  · simp [alternatingSylowProfileQuadraticCost, htwo,
      symmetricSylowProfileQuadraticCost, Nat.div_eq_of_lt h]

/-- The five small-degree cyclic budgets cover arbitrary injective
prime families, not just the full canonical list. -/
theorem sum_alternatingSylowProfileCyclicCost_small_degrees_lt_one
    {I : Type*} (s : Finset I) (p : I → ℕ) (n : ℕ)
    (hn : n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 12)
    (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    (∑ i ∈ s, alternatingSylowProfileQuadraticCost n (p i) /
      ((p i - 1 : ℕ) : ℝ)) < 1 := by
  classical
  have hn13 : n < 13 := by omega
  have checked : ∀ q ∈ Finset.range 13, q.Prime → q ∈ smallAlternatingPrimes := by
    decide
  let f : ℕ → ℝ := fun q ↦
    alternatingSylowProfileQuadraticCost n q / ((q - 1 : ℕ) : ℝ)
  have hcut :
      (∑ i ∈ s.filter (fun i ↦ p i ≤ n), f (p i)) = ∑ i ∈ s, f (p i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hlarge : n < p i := Nat.lt_of_not_ge (fun hle ↦
      hnot (Finset.mem_filter.mpr ⟨hi, hle⟩))
    simp [f, smallAlternatingCost_zero hlarge]
  change (∑ i ∈ s, f (p i)) < 1
  rw [← hcut]
  apply lt_of_le_of_lt ?_ (smallAlternatingCyclicBudget_lt hn)
  change (∑ i ∈ s.filter (fun i ↦ p i ≤ n), f (p i)) ≤
    ∑ q ∈ smallAlternatingPrimes, f q
  apply Finset.sum_le_sum_of_injOn p
  · intro i hi j hj hij
    exact hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨his, hin⟩ := Finset.mem_filter.mp hi
    exact checked (p i) (Finset.mem_range.mpr (hin.trans_lt hn13)) (hp i his)
  · intro i _hi
    exact le_rfl
  · intro q _hq _hnot
    exact div_nonneg (smallAlternatingCost_nonneg n q) (Nat.cast_nonneg _)

end LisiSabatini
