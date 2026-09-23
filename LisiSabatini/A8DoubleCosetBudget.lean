module

public import LisiSabatini.AlternatingSylowCycleProfile

/-!
# Exact arithmetic for the degree-eight double-coset budget

The odd-prime profile costs, combined with a separate two-subgroup
double-coset contribution of `251 / 315`, give a total strictly below one.
All profile values below are proved from the polynomial recurrence.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

private theorem a8SylowProfile_three :
    sylowCycleProfile 8 3 =
      1 + Polynomial.C 4 * Polynomial.X + Polynomial.C 4 * Polynomial.X ^ 2 := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]
  ring

private theorem a8SylowProfile_five :
    sylowCycleProfile 8 5 = 1 + Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem a8SylowProfile_seven :
    sylowCycleProfile 8 7 = 1 + Polynomial.C 6 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

/-- The exact degree-eight quadratic profile cost at the prime three. -/
theorem alternatingSylowProfileQuadraticCost_eight_three :
    alternatingSylowProfileQuadraticCost 8 3 = (11 : ℝ) / 70 := by
  have hIcc2 : Finset.Icc 1 2 = {1, 2} := by decide
  norm_num [alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost, a8SylowProfile_three, hIcc2,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_one,
    Polynomial.coeff_X, Polynomial.coeff_X_pow, primeCycleClassCard, Nat.factorial]

/-- The exact degree-eight quadratic profile cost at the prime five. -/
theorem alternatingSylowProfileQuadraticCost_eight_five :
    alternatingSylowProfileQuadraticCost 8 5 = (1 : ℝ) / 84 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  norm_num [alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost, a8SylowProfile_five, hIcc1,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_one,
    Polynomial.coeff_X, primeCycleClassCard, Nat.factorial]

/-- The exact degree-eight quadratic profile cost at the prime seven. -/
theorem alternatingSylowProfileQuadraticCost_eight_seven :
    alternatingSylowProfileQuadraticCost 8 7 = (1 : ℝ) / 160 := by
  have hIcc1 : Finset.Icc 1 1 = {1} := by decide
  norm_num [alternatingSylowProfileQuadraticCost,
    symmetricSylowProfileQuadraticCost, a8SylowProfile_seven, hIcc1,
    Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_one,
    Polynomial.coeff_X, primeCycleClassCard, Nat.factorial]

/-- The odd-prime profile contribution in degree eight. -/
theorem alternatingSylowProfileQuadraticCost_eight_odd_sum :
    alternatingSylowProfileQuadraticCost 8 3 +
      alternatingSylowProfileQuadraticCost 8 5 +
      alternatingSylowProfileQuadraticCost 8 7 = (589 : ℝ) / 3360 := by
  rw [alternatingSylowProfileQuadraticCost_eight_three,
    alternatingSylowProfileQuadraticCost_eight_five,
    alternatingSylowProfileQuadraticCost_eight_seven]
  norm_num

/-- Exact arithmetic after substituting the degree-eight double-coset
two-subgroup contribution. -/
theorem a8DoubleCosetBudget_eq :
    (251 : ℝ) / 315 + alternatingSylowProfileQuadraticCost 8 3 +
      alternatingSylowProfileQuadraticCost 8 5 +
      alternatingSylowProfileQuadraticCost 8 7 = (9799 : ℝ) / 10080 := by
  rw [alternatingSylowProfileQuadraticCost_eight_three,
    alternatingSylowProfileQuadraticCost_eight_five,
    alternatingSylowProfileQuadraticCost_eight_seven]
  norm_num

/-- The degree-eight double-coset budget leaves a positive margin. -/
theorem a8DoubleCosetBudget_lt_one :
    (251 : ℝ) / 315 + alternatingSylowProfileQuadraticCost 8 3 +
      alternatingSylowProfileQuadraticCost 8 5 +
      alternatingSylowProfileQuadraticCost 8 7 < 1 := by
  rw [a8DoubleCosetBudget_eq]
  norm_num

private theorem a8ProfileCost_nonneg (p : ℕ) :
    0 ≤ alternatingSylowProfileQuadraticCost 8 p := by
  unfold alternatingSylowProfileQuadraticCost
  split_ifs
  · apply Finset.sum_nonneg
    intro j _hj
    split_ifs <;> positivity
  · unfold symmetricSylowProfileQuadraticCost
    apply Finset.sum_nonneg
    intro j _hj
    positivity

private theorem a8ProfileCost_zero {p : ℕ} (hp : 8 < p) :
    alternatingSylowProfileQuadraticCost 8 p = 0 := by
  have htwo : p ≠ 2 := by omega
  simp [alternatingSylowProfileQuadraticCost, htwo,
    symmetricSylowProfileQuadraticCost, Nat.div_eq_of_lt hp]

/-- Every injective finite family of odd primes has degree-eight profile
sum at most the sum for three, five, and seven. -/
theorem sum_alternatingSylowProfileQuadraticCost_eight_odd_le
    {I : Type*} (s : Finset I) (p : I → ℕ)
    (hp : ∀ i ∈ s, (p i).Prime) (hne : ∀ i ∈ s, p i ≠ 2)
    (hinj : Set.InjOn p s) :
    (∑ i ∈ s, alternatingSylowProfileQuadraticCost 8 (p i)) ≤
      (589 : ℝ) / 3360 := by
  classical
  have checked : ∀ q ∈ Finset.range 9, q.Prime → q ≠ 2 →
      q ∈ ({3, 5, 7} : Finset ℕ) := by decide
  let f : ℕ → ℝ := alternatingSylowProfileQuadraticCost 8
  have hcut :
      (∑ i ∈ s.filter (fun i ↦ p i ≤ 8), f (p i)) = ∑ i ∈ s, f (p i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hlarge : 8 < p i := Nat.lt_of_not_ge (fun hle ↦
      hnot (Finset.mem_filter.mpr ⟨hi, hle⟩))
    exact a8ProfileCost_zero hlarge
  have hbound : (∑ i ∈ s, f (p i)) ≤ ∑ q ∈ ({3, 5, 7} : Finset ℕ), f q := by
    rw [← hcut]
    apply Finset.sum_le_sum_of_injOn p
    · intro i hi j hj hij
      exact hinj (Finset.mem_filter.mp hi).1 (Finset.mem_filter.mp hj).1 hij
    · intro q hq
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨his, hin⟩ := Finset.mem_filter.mp hi
      exact checked (p i) (Finset.mem_range.mpr (by omega)) (hp i his) (hne i his)
    · intro i _hi
      exact le_rfl
    · intro q _hq _hnot
      exact a8ProfileCost_nonneg q
  calc
    (∑ i ∈ s, alternatingSylowProfileQuadraticCost 8 (p i)) ≤
        ∑ q ∈ ({3, 5, 7} : Finset ℕ), f q := hbound
    _ = (589 : ℝ) / 3360 := by
      norm_num [f, alternatingSylowProfileQuadraticCost_eight_three,
        alternatingSylowProfileQuadraticCost_eight_five,
        alternatingSylowProfileQuadraticCost_eight_seven]

/-- The double-coset contribution and every injective odd-prime profile
family together have total budget strictly less than one. -/
theorem a8DoubleCosetBudget_restricted_lt_one
    {I : Type*} (s : Finset I) (p : I → ℕ)
    (hp : ∀ i ∈ s, (p i).Prime) (hne : ∀ i ∈ s, p i ≠ 2)
    (hinj : Set.InjOn p s) :
    (251 : ℝ) / 315 +
      (∑ i ∈ s, alternatingSylowProfileQuadraticCost 8 (p i)) < 1 := by
  have hsum := sum_alternatingSylowProfileQuadraticCost_eight_odd_le s p hp hne hinj
  linarith

end LisiSabatini
