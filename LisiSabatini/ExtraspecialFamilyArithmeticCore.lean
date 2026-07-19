import LisiSabatini.ExtraspecialArithmetic

/-!
# Arithmetic core for the odd-order extraspecial half-space estimate

This module contains exactly the arithmetic lemmas used by
`ExtraspecialFamilyHalfBudget`: the uniform one-row order estimates, the
exponential cofactor estimate, and the distinct-prime multiplicity bound.
-/

namespace LisiSabatini

universe uI

/-! ## Uniform exponential estimates -/

/-- The elementary exponential estimate used when the extraspecial prime is
`3`. -/
theorem two_mul_succ_add_one_le_three_pow_succ (k : ℕ) :
    2 * (k + 1) + 1 ≤ 3 ^ (k + 1) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 3 ^ (k + 1) :=
        Nat.one_le_pow _ _ (by norm_num)
      omega

/-- Every positive integer `n` is at most `p ^ (n - 1)` once `p ≥ 2`. -/
theorem le_pow_pred_of_two_le
    (p n : ℕ) (hp : 2 ≤ p) (hn : 0 < n) :
    n ≤ p ^ (n - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hshift : ∀ j : ℕ, j + 1 ≤ p ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        have hscale : p * (j + 1) ≤ p * p ^ j :=
          Nat.mul_le_mul_left p ih
        have hstep : j + 2 ≤ p * (j + 1) := by
          have := Nat.mul_le_mul_right (j + 1) hp
          omega
        calc
          j + 2 ≤ p * (j + 1) := hstep
          _ ≤ p * p ^ j := hscale
          _ = p ^ j * p := by ring
  simpa using hshift k

/-- Cubic growth is below `3 ^ p` for `p ≥ 5`. -/
theorem cube_le_three_pow (p : ℕ) (hp : 5 ≤ p) :
    p ^ 3 ≤ 3 ^ p := by
  let k := p - 5
  have hpEq : p = k + 5 := by
    dsimp [k]
    omega
  rw [hpEq]
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k + 1 + 5 = (k + 5) + 1 by omega, pow_succ]
      have hk : 5 ≤ k + 5 := by omega
      have hthreeSq : 3 * (k + 5) ^ 2 ≤ (k + 5) ^ 3 := by
        calc
          3 * (k + 5) ^ 2 ≤ (k + 5) * (k + 5) ^ 2 :=
            Nat.mul_le_mul_right ((k + 5) ^ 2) (by omega)
          _ = (k + 5) ^ 3 := by ring
      have hrest : 3 * (k + 5) + 1 ≤ (k + 5) ^ 3 := by
        nlinarith
      have hnext : (k + 5 + 1) ^ 3 ≤ 3 * (k + 5) ^ 3 := by
        nlinarith
      exact hnext.trans (by
        simpa [pow_succ, mul_comm] using Nat.mul_le_mul_left 3 ih)

/-- Uniformly in odd primes, the extraspecial order is at most the field
cardinality raised to the prime-power multiplicity. -/
theorem extraspecial_order_le_field_pow_primePower
    {r p n : ℕ}
    (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hrTwo : r ≠ 2) (hpTwo : p ≠ 2)
    (hn : 0 < n) :
    p ^ (2 * n + 1) ≤ r ^ (p ^ n) := by
  have hrThree : 3 ≤ r := by
    obtain ⟨k, hk⟩ := hr.odd_of_ne_two hrTwo
    have := hr.two_le
    omega
  by_cases hpThree : p = 3
  · subst p
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hexp := two_mul_succ_add_one_le_three_pow_succ k
    exact (Nat.pow_le_pow_right (by norm_num) hexp).trans
      (Nat.pow_le_pow_left hrThree _)
  · have hpOdd := hp.odd_of_ne_two hpTwo
    have hpFive : 5 ≤ p := by
      obtain ⟨k, hk⟩ := hpOdd
      have := hp.two_le
      omega
    have hexpLinear : 2 * n + 1 ≤ 3 * n := by omega
    have hfirst : p ^ (2 * n + 1) ≤ p ^ (3 * n) :=
      Nat.pow_le_pow_right hp.pos hexpLinear
    have hcube : p ^ 3 ≤ 3 ^ p := cube_le_three_pow p hpFive
    have hnPow : n ≤ p ^ (n - 1) :=
      le_pow_pred_of_two_le p n hp.two_le hn
    have hpn : p * n ≤ p ^ n := by
      calc
        p * n ≤ p * p ^ (n - 1) := Nat.mul_le_mul_left p hnPow
        _ = p ^ n := by
          nth_rewrite 2 [← Nat.sub_add_cancel hn]
          rw [pow_add, pow_one]
          ring
    calc
      p ^ (2 * n + 1) ≤ p ^ (3 * n) := hfirst
      _ = (p ^ 3) ^ n := by rw [pow_mul]
      _ ≤ (3 ^ p) ^ n := Nat.pow_le_pow_left hcube _
      _ = 3 ^ (p * n) := by rw [pow_mul]
      _ ≤ 3 ^ (p ^ n) := Nat.pow_le_pow_right (by norm_num) hpn
      _ ≤ r ^ (p ^ n) := Nat.pow_le_pow_left hrThree _

/-- The coefficient needed to absorb twice the ambient dimension into the
multi-row exponential cofactor. -/
theorem six_mul_add_four_lt_three_pow_of_three_le
    (m : ℕ) (hm : 3 ≤ m) :
    6 * m + 4 < 3 ^ m := by
  let k := m - 3
  have hmEq : m = k + 3 := by
    dsimp [k]
    omega
  rw [hmEq]
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 by omega, pow_succ]
      have hpow : 1 ≤ 3 ^ (k + 3) :=
        Nat.one_le_pow _ _ (by norm_num)
      omega

/-! ## One-row order domination -/

/-- The extraspecial group order is dominated by the `(p - 2)`-nd power of
the fixed-space scale.  The explicit last hypothesis isolates the unique
small case `p = 3`, `n = 1`; all other cases follow from the standard row
arithmetic. -/
theorem extraspecial_order_lt_fixedScale_pow_sub_two
    {r p n a b d : ℕ}
    (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hrTwo : r ≠ 2) (hpTwo : p ≠ 2) (hrp : r ≠ p)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hdiv : p ∣ r ^ a - 1)
    (hd : d = a * p ^ n * b)
    (hthree : p = 3 → n = 1 → 27 < r ^ (d / 3)) :
    p ^ (2 * n + 1) < (r ^ (d / p)) ^ (p - 2) := by
  subst d
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let e := a * p ^ k * b
  let x := r ^ e
  have hdExp : a * p ^ (k + 1) * b = e * p := by
    dsimp [e]
    rw [pow_succ]
    ring
  have hquot : (a * p ^ (k + 1) * b) / p = e := by
    rw [hdExp]
    exact Nat.mul_div_cancel e hp.pos
  have hbase : 2 * p + 1 ≤ r ^ a :=
    two_mul_prime_add_one_le_pow_of_dvd_sub_one
      hr hp hrTwo hpTwo ha hdiv
  have hxEq : x = (r ^ a) ^ (p ^ k * b) := by
    dsimp [x, e]
    rw [show a * p ^ k * b = a * (p ^ k * b) by ring, pow_mul]
  have hxLower : (2 * p + 1) ^ (p ^ k * b) ≤ x := by
    rw [hxEq]
    exact Nat.pow_le_pow_left hbase _
  rw [hquot]
  change p ^ (2 * (k + 1) + 1) < x ^ (p - 2)
  by_cases hpThree : p = 3
  · subst p
    cases k with
    | zero =>
        have hsmall := hthree rfl rfl
        norm_num at hsmall
        have hab : (a * 3 * b) / 3 = a * b := by
          rw [show a * 3 * b = (a * b) * 3 by ring]
          exact Nat.mul_div_cancel (a * b) (by norm_num)
        rw [hab] at hsmall
        simpa [x, e] using hsmall
    | succ k =>
        have hmin :
            3 ^ (2 * (k + 2) + 1) < 7 ^ (3 ^ (k + 1) * b) :=
          three_extraspecial_order_lt_minimalBlock (by omega) hb
        have hscale : 7 ^ (3 ^ (k + 1) * b) ≤ x := by
          simpa using hxLower
        simpa using hmin.trans_le hscale
  · have hpOdd := hp.odd_of_ne_two hpTwo
    have hpFive : 5 ≤ p := by
      obtain ⟨j, hj⟩ := hpOdd
      have hpTwoLe := hp.two_le
      omega
    have hmin :
        p ^ (2 * (k + 1) + 1) <
          ((2 * p + 1) ^ (p ^ k * b)) ^ (p - 2) :=
      extraspecial_order_lt_minimalBlock_pow_sub_two
        hpFive (by omega) hb
    exact hmin.trans_le (Nat.pow_le_pow_left hxLower _)

/-! ## Distinct rows force large common multiplicity -/

/-- In a family with at least two distinct odd prime labels, every
prime-power multiplicity is at most one third of the common dimension. -/
theorem three_mul_extraspecial_primePower_le_dimension
    {I : Type uI} [Fintype I]
    {d : ℕ} (p n a b : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hinj : Function.Injective p)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i)
    (hd : ∀ i, d = a i * p i ^ n i * b i)
    (hcard : 2 ≤ Fintype.card I) (i : I) :
    3 * p i ^ n i ≤ d := by
  obtain ⟨j, hji⟩ :=
    Fintype.exists_ne_of_one_lt_card (by omega) i
  have hpne : p i ≠ p j := by
    intro heq
    exact hji (hinj heq).symm
  have hpowDvd : ∀ t : I, p t ^ n t ∣ d := by
    intro t
    refine ⟨a t * b t, ?_⟩
    rw [hd t]
    ring
  have hpjDvd : p j ∣ d :=
    (dvd_pow_self (p j) (hn j).ne').trans (hpowDvd j)
  have hcop : Nat.Coprime (p i ^ n i) (p j) :=
    ((Nat.coprime_primes (hp i) (hp j)).2 hpne).pow_left _
  have hmulDvd : p i ^ n i * p j ∣ d :=
    hcop.mul_dvd_of_dvd_of_dvd (hpowDvd i) hpjDvd
  have hdpos : 0 < d := by
    rw [hd i]
    exact Nat.mul_pos
      (Nat.mul_pos (ha i) (pow_pos (hp i).pos _)) (hb i)
  have hmulLe : p i ^ n i * p j ≤ d :=
    Nat.le_of_dvd hdpos hmulDvd
  have hpjThree : 3 ≤ p j := by
    obtain ⟨k, hk⟩ := (hp j).odd_of_ne_two (hpTwo j)
    have := (hp j).two_le
    omega
  calc
    3 * p i ^ n i = p i ^ n i * 3 := by ring
    _ ≤ p i ^ n i * p j := Nat.mul_le_mul_left _ hpjThree
    _ ≤ d := hmulLe

end LisiSabatini
