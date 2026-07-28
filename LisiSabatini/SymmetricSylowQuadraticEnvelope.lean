module

public import LisiSabatini.AlternatingSylowQuadraticEnvelope

/-!
# A global quadratic envelope for symmetric Sylow rows

For odd primes, the symmetric and alternating cycle-profile costs agree,
so the alternating-group envelope already supplies the required estimate.
The only new row is `p = 2`.  Here the full negative-binomial cost (including
the odd-transposition rows) decreases from degree forty onward and its exact
degree-forty value is strictly below `3 / 4`.

Together with the strict `1 / 4` budget for the alternating profiles, this
gives a strict unit budget for every injective prime-labelled family of
symmetric Sylow profiles.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

/-! ## The full binary negative-binomial envelope -/

/-- At the binary row, the new top term of the next block fits into
three quarters of the old top term once the old block has size at least
ten. -/
theorem four_mul_negativeBinomialQuadraticNewTopTerm_le_three_oldTop_two
    {m : ℕ} (hm : 10 ≤ m) :
    4 * sylowCycleNegativeBinomialQuadraticTerm
        2 (m + 1) (m + 1) ≤
      3 * sylowCycleNegativeBinomialQuadraticTerm 2 m m := by
  let bn :=
    sylowCycleNegativeBinomialMajorant 2 (m + 1) (m + 1)
  let bo := sylowCycleNegativeBinomialMajorant 2 m m
  let cn := primeCycleClassCard (2 * (m + 1)) 2 (m + 1)
  let co := primeCycleClassCard (2 * m) 2 m
  let k := 2 * (2 * m + 1)
  let v := 2 * m + 1
  have hbn :
      bn * (m + 1) = bo * k := by
    simpa only [bn, bo, k] using
      sylowCycleNegativeBinomialMajorant_newTop_ratio
        (p := 2) (m := m) (by omega : 0 < m)
  have hcn :
      cn = co * v := by
    simpa only [cn, co, v, Nat.ascFactorial_succ,
      Nat.ascFactorial_zero, Nat.mul_one] using
      primeCycleClassCard_newTop_ratio
        (p := 2) (m := m) (by norm_num) (by omega)
  have hbase :
      16 * v ≤ 3 * (m + 1) ^ 2 := by
    have hlinear : 2 * m + 1 ≤ 2 * (m + 1) := by omega
    have hthirtyTwo : 32 ≤ 3 * (m + 1) := by omega
    calc
      16 * v = 16 * (2 * m + 1) := by rfl
      _ ≤ 16 * (2 * (m + 1)) :=
        Nat.mul_le_mul_left 16 hlinear
      _ = 32 * (m + 1) := by ring
      _ ≤ (3 * (m + 1)) * (m + 1) :=
        Nat.mul_le_mul_right (m + 1) hthirtyTwo
      _ = 3 * (m + 1) ^ 2 := by ring
  have hratio :
      4 * k ^ 2 ≤ 3 * (m + 1) ^ 2 * v := by
    calc
      4 * k ^ 2 = (16 * v) * v := by
        simp only [k, v]
        ring
      _ ≤ (3 * (m + 1) ^ 2) * v :=
        Nat.mul_le_mul_right v hbase
      _ = 3 * (m + 1) ^ 2 * v := by ring
  have hscaled :
      (m + 1) ^ 2 * (4 * bn ^ 2 * co) ≤
        (m + 1) ^ 2 * (3 * bo ^ 2 * cn) := by
    calc
      (m + 1) ^ 2 * (4 * bn ^ 2 * co) =
          bo ^ 2 * co * (4 * k ^ 2) := by
        calc
          (m + 1) ^ 2 * (4 * bn ^ 2 * co) =
              4 * (bn * (m + 1)) ^ 2 * co := by ring
          _ = 4 * (bo * k) ^ 2 * co := by rw [hbn]
          _ = bo ^ 2 * co * (4 * k ^ 2) := by ring
      _ ≤ bo ^ 2 * co * (3 * (m + 1) ^ 2 * v) :=
        Nat.mul_le_mul_left _ hratio
      _ = (m + 1) ^ 2 * (3 * bo ^ 2 * cn) := by
        rw [hcn]
        ring
  have hcross :
      4 * bn ^ 2 * co ≤ 3 * bo ^ 2 * cn :=
    Nat.le_of_mul_le_mul_left hscaled (by positivity)
  have hcnPos : (0 : ℝ) < cn := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m + 1) (le_rfl)
  have hcoPos : (0 : ℝ) < co := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m) (le_rfl)
  change
    4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) ≤
      3 * ((bo : ℝ) ^ 2 / (co : ℝ))
  rw [show
      4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) =
        (4 * (bn : ℝ) ^ 2) / (cn : ℝ) by ring,
    show
      3 * ((bo : ℝ) ^ 2 / (co : ℝ)) =
        (3 * (bo : ℝ) ^ 2) / (co : ℝ) by ring,
    div_le_div_iff₀ hcnPos hcoPos]
  exact_mod_cast hcross

/-- Successive complete binary negative-binomial blocks decrease once the
old block has size at least ten. -/
theorem sylowCycleNegativeBinomialQuadraticCost_succBlock_le_two
    {m : ℕ} (hm : 10 ≤ m) :
    sylowCycleNegativeBinomialQuadraticCost (2 * (m + 1)) 2 ≤
      sylowCycleNegativeBinomialQuadraticCost (2 * m) 2 :=
  sylowCycleNegativeBinomialQuadraticCost_succBlock_le_of_top_pack
    (by norm_num) (by omega)
    (four_mul_negativeBinomialQuadraticSameTopTerm_le_oldTop_two
      (by omega))
    (four_mul_negativeBinomialQuadraticNewTopTerm_le_three_oldTop_two
      hm)

/-- Every complete binary block from block twenty onward is bounded by
the degree-forty block. -/
theorem sylowCycleNegativeBinomialQuadraticCost_two_mul_le_forty
    {m : ℕ} (hm : 20 ≤ m) :
    sylowCycleNegativeBinomialQuadraticCost (2 * m) 2 ≤
      sylowCycleNegativeBinomialQuadraticCost 40 2 := by
  induction m, hm using Nat.le_induction with
  | base =>
      norm_num
  | succ m hm ih =>
      exact
        (sylowCycleNegativeBinomialQuadraticCost_succBlock_le_two
          (by omega)).trans ih

/-! ## Exact degree-forty anchor -/

/-- The full (not parity-restricted) binary negative-binomial cost at
degree forty is strictly below `3 / 4`. -/
theorem sylowCycleNegativeBinomialQuadraticCost_two_forty_lt :
    sylowCycleNegativeBinomialQuadraticCost 40 2 <
      (3 : ℝ) / 4 := by
  have hIcc : Finset.Icc 1 20 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        11, 12, 13, 14, 15, 16, 17, 18, 19, 20} := by
    decide
  rw [sylowCycleNegativeBinomialQuadraticCost, hIcc]
  norm_num [sylowCycleNegativeBinomialMajorant,
    Nat.multichoose, primeCycleClassCard, Nat.factorial]

/-- From degree forty onward, the symmetric binary Sylow profile costs
strictly less than `3 / 4`. -/
theorem symmetricSylowProfileQuadraticCost_two_lt_three_div_four
    {n : ℕ} (hn : 40 ≤ n) :
    symmetricSylowProfileQuadraticCost n 2 <
      (3 : ℝ) / 4 := by
  have hm20 : 20 ≤ n / 2 := by
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
      (by omega)
  calc
    symmetricSylowProfileQuadraticCost n 2 ≤
        sylowCycleNegativeBinomialQuadraticCost n 2 :=
      symmetricSylowProfileQuadraticCost_le_negativeBinomial
        Nat.prime_two
    _ ≤
        sylowCycleNegativeBinomialQuadraticCost
          (2 * (n / 2)) 2 :=
      sylowCycleNegativeBinomialQuadraticCost_le_blockStart
        (by norm_num)
    _ ≤ sylowCycleNegativeBinomialQuadraticCost 40 2 :=
      sylowCycleNegativeBinomialQuadraticCost_two_mul_le_forty hm20
    _ < (3 : ℝ) / 4 :=
      sylowCycleNegativeBinomialQuadraticCost_two_forty_lt

/-! ## The unit budget for arbitrary injective prime families -/

/-- For `n ≥ 40`, every injective prime-labelled family of symmetric Sylow
cycle profiles has total normalized quadratic cost strictly below one. -/
theorem sum_symmetricSylowProfileQuadraticCost_lt_one
    {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (n : ℕ) (hn : 40 ≤ n)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p s) :
    (∑ i ∈ s,
      symmetricSylowProfileQuadraticCost n (p i)) < 1 := by
  have halt :
      (∑ i ∈ s,
        alternatingSylowProfileQuadraticCost n (p i)) <
          1 / 4 :=
    sum_alternatingSylowProfileQuadraticCost_lt_one_div_four
      s p n hn hp hinj
  have hrow :
      ∀ i ∈ s,
        symmetricSylowProfileQuadraticCost n (p i) ≤
          alternatingSylowProfileQuadraticCost n (p i) +
            if p i = 2 then (3 : ℝ) / 4 else 0 := by
    intro i hi
    by_cases htwo : p i = 2
    · rw [htwo]
      simp only [if_pos]
      have hbinary :=
        symmetricSylowProfileQuadraticCost_two_lt_three_div_four hn
      have haltNonneg :
          0 ≤ alternatingSylowProfileQuadraticCost n 2 := by
        rw [alternatingSylowProfileQuadraticCost, if_pos rfl]
        apply Finset.sum_nonneg
        intro j hj
        split_ifs
        · exact div_nonneg (sq_nonneg _) (by positivity)
        · exact le_rfl
      linarith
    · rw [alternatingSylowProfileQuadraticCost, if_neg htwo]
      simp [htwo]
  have hindicator :
      (∑ i ∈ s,
        if p i = 2 then (3 : ℝ) / 4 else 0) ≤
          (3 : ℝ) / 4 := by
    calc
      (∑ i ∈ s,
          if p i = 2 then (3 : ℝ) / 4 else 0) =
          ∑ q ∈ s.image p,
            if q = 2 then (3 : ℝ) / 4 else 0 := by
        rw [Finset.sum_image hinj]
      _ ≤ (3 : ℝ) / 4 := by
        simp only [Finset.sum_ite_eq']
        split_ifs <;> norm_num
  calc
    (∑ i ∈ s,
        symmetricSylowProfileQuadraticCost n (p i)) ≤
        ∑ i ∈ s,
          (alternatingSylowProfileQuadraticCost n (p i) +
            if p i = 2 then (3 : ℝ) / 4 else 0) :=
      Finset.sum_le_sum fun i hi ↦ hrow i hi
    _ =
        (∑ i ∈ s,
          alternatingSylowProfileQuadraticCost n (p i)) +
        ∑ i ∈ s,
          if p i = 2 then (3 : ℝ) / 4 else 0 := by
      rw [Finset.sum_add_distrib]
    _ < (1 : ℝ) / 4 + 3 / 4 :=
      add_lt_add_of_lt_of_le halt hindicator
    _ = 1 := by norm_num

end LisiSabatini
