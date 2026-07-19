import Mathlib

/-!
# Arithmetic for an odd extraspecial basic component

Suppose an odd `p`-group of order `p ^ (2 * n + 1)` acts in cross
characteristic `r`, and every noncentral element has a fixed space of
dimension at most `d / p`.  The elementary union estimate for its nonregular
locus is then

`(p ^ (2 * n + 1) - 1) * r ^ (d / p)`.

This file proves that this estimate, together with one forbidden orbit of
size at most `p ^ (2 * n + 1)`, is strictly smaller than `r ^ d` under the
standard extraspecial divisibility and multiplicity hypotheses.  The sharp
elementary observation is that, for odd `p` and odd `r`, divisibility
`p ∣ r ^ a - 1` forces `2 * p + 1 ≤ r ^ a`.
-/

namespace LisiSabatini

/-! ## Elementary comparison lemmas -/

/-- If an order bound `q` is smaller than `x ^ (k + 1)`, then the union of
`q - 1` sets of size at most `x`, together with one set of size at most `q`,
is smaller than `x ^ (k + 3)`. -/
theorem extraspecial_union_bound_of_order_lt
    {q x k : ℕ} (hx : 2 ≤ x) (hq : q < x ^ (k + 1)) :
    (q - 1) * x + q < x ^ (k + 3) := by
  have hxpos : 0 < x := by omega
  have hqsub : q - 1 < x ^ (k + 1) := by omega
  have hfirst :
      (q - 1) * x < x ^ (k + 1) * x :=
    Nat.mul_lt_mul_of_pos_right hqsub hxpos
  have hsum :
      (q - 1) * x + q < x ^ (k + 1) * x + x ^ (k + 1) :=
    Nat.add_lt_add hfirst hq
  have hquad : x + 1 < x ^ 2 := by
    nlinarith
  calc
    (q - 1) * x + q < x ^ (k + 1) * x + x ^ (k + 1) := hsum
    _ = x ^ (k + 1) * (x + 1) := by ring
    _ < x ^ (k + 1) * x ^ 2 :=
      Nat.mul_lt_mul_of_pos_left hquad (pow_pos hxpos _)
    _ = x ^ (k + 3) := by
      rw [← pow_add]

/-- A positive even multiple of an odd prime is at least twice that prime.
Consequently an odd prime power congruent to one modulo an odd prime is at
least `2 * p + 1`. -/
theorem two_mul_prime_add_one_le_pow_of_dvd_sub_one
    {r p a : ℕ}
    (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hrTwo : r ≠ 2) (hpTwo : p ≠ 2)
    (ha : 0 < a) (hdiv : p ∣ r ^ a - 1) :
    2 * p + 1 ≤ r ^ a := by
  have hraOne : 1 ≤ r ^ a := Nat.one_le_pow _ _ hr.pos
  obtain ⟨c, hc⟩ := hdiv
  have heq : r ^ a = p * c + 1 := by
    omega
  have hprodEven : Even (p * c) := by
    rw [← hc]
    exact Nat.Odd.sub_odd (hr.odd_of_ne_two hrTwo).pow odd_one
  have hcEven : Even c := by
    rcases Nat.even_or_odd c with hcEven | hcOdd
    · exact hcEven
    · exact False.elim
        ((Nat.not_even_iff_odd.mpr
          ((hp.odd_of_ne_two hpTwo).mul hcOdd)) hprodEven)
  have hcpos : 0 < c := by
    by_contra hc0
    have hcEq : c = 0 := by omega
    rw [hcEq, mul_zero, zero_add] at heq
    have hraGt : 1 < r ^ a := by
      exact one_lt_pow₀ hr.one_lt ha.ne'
    omega
  obtain ⟨c', hc'⟩ := hcEven
  have hcTwo : 2 ≤ c := by
    rw [hc'] at hcpos ⊢
    omega
  have hmul : 2 * p ≤ p * c := by
    have := Nat.mul_le_mul_left p hcTwo
    omega
  omega

/-- The exponent `2 * (k + 1) + 1` is dominated by the extraspecial
multiplicity exponent `p ^ k * b * (p - 2)` once `p ≥ 5`. -/
theorem extraspecial_exponent_le
    (p k b : ℕ) (hp : 5 ≤ p) (hb : 0 < b) :
    2 * (k + 1) + 1 ≤ p ^ k * b * (p - 2) := by
  have hcore : ∀ j : ℕ, 2 * (j + 1) + 1 ≤ p ^ j * (p - 2) := by
    intro j
    induction j with
    | zero => simp; omega
    | succ j ih =>
        rw [pow_succ]
        have hscale :
            p * (2 * (j + 1) + 1) ≤
              p * (p ^ j * (p - 2)) :=
          Nat.mul_le_mul_left p ih
        have hstep :
            2 * (j + 2) + 1 ≤ p * (2 * (j + 1) + 1) := by
          have := Nat.mul_le_mul_right (2 * (j + 1) + 1) hp
          omega
        calc
          2 * (j + 2) + 1 ≤ p * (2 * (j + 1) + 1) := hstep
          _ ≤ p * (p ^ j * (p - 2)) := hscale
          _ = p ^ j * p * (p - 2) := by ring
  have hbOne : 1 ≤ b := hb
  have hmul : p ^ k * (p - 2) ≤ p ^ k * b * (p - 2) := by
    have hpb : p ^ k ≤ p ^ k * b := by
      simpa only [mul_one] using Nat.mul_le_mul_left (p ^ k) hbOne
    exact Nat.mul_le_mul_right (p - 2) hpb
  exact (hcore k).trans hmul

/-- The small-base exponential estimate needed for the `p = 3`, `n ≥ 3`
branch. -/
theorem two_mul_add_seven_le_nine_mul_three_pow (k : ℕ) :
    2 * k + 7 ≤ 9 * 3 ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have hpow : 1 ≤ 3 ^ k := Nat.one_le_pow _ _ (by norm_num)
      omega

/-! ## Extraspecial order versus field size -/

/-- For `p ≥ 5`, the extraspecial order is smaller than the `(p - 2)`-nd
power of the minimal admissible field-size block. -/
theorem extraspecial_order_lt_minimalBlock_pow_sub_two
    {p n b : ℕ}
    (hp : 5 ≤ p) (hn : 0 < n) (hb : 0 < b) :
    p ^ (2 * n + 1) <
      ((2 * p + 1) ^ (p ^ (n - 1) * b)) ^ (p - 2) := by
  have hexp := extraspecial_exponent_le p (n - 1) b hp hb
  have hnEq : n - 1 + 1 = n := by omega
  have hpowExp :
      p ^ (2 * n + 1) ≤
        p ^ (p ^ (n - 1) * b * (p - 2)) :=
    Nat.pow_le_pow_right (by omega) (by simpa [hnEq] using hexp)
  have hfinalExp : 0 < p ^ (n - 1) * b * (p - 2) := by
    exact Nat.mul_pos
      (Nat.mul_pos (pow_pos (by omega : 0 < p) _) hb) (by omega)
  have hbase : p < 2 * p + 1 := by omega
  have hbasePow :
      p ^ (p ^ (n - 1) * b * (p - 2)) <
        (2 * p + 1) ^ (p ^ (n - 1) * b * (p - 2)) :=
    Nat.pow_lt_pow_left hbase hfinalExp.ne'
  calc
    p ^ (2 * n + 1) ≤
        p ^ (p ^ (n - 1) * b * (p - 2)) := hpowExp
    _ < (2 * p + 1) ^ (p ^ (n - 1) * b * (p - 2)) :=
      hbasePow
    _ = ((2 * p + 1) ^ (p ^ (n - 1) * b)) ^ (p - 2) := by
      rw [pow_mul]

/-- In the characteristic-order prime `p = 3` branch beyond the first
multiplicity, the extraspecial order is already smaller than the minimal
admissible block itself. -/
theorem three_extraspecial_order_lt_minimalBlock
    {n b : ℕ} (hn : 2 ≤ n) (hb : 0 < b) :
    3 ^ (2 * n + 1) < 7 ^ (3 ^ (n - 1) * b) := by
  rcases eq_or_lt_of_le hn with rfl | hnThree
  · have hbOne : 1 ≤ b := hb
    have hexp : 3 ≤ 3 * b := by omega
    calc
      3 ^ (2 * 2 + 1) < 7 ^ 3 := by norm_num
      _ ≤ 7 ^ (3 ^ (2 - 1) * b) := by
        exact Nat.pow_le_pow_right (by norm_num) (by norm_num at hexp ⊢; exact hexp)
  · have hnSub : 2 ≤ n - 1 := by omega
    let k := n - 3
    have hk : n - 1 = k + 2 := by
      dsimp [k]
      omega
    have hexp : 2 * n + 1 ≤ 3 ^ (n - 1) := by
      calc
        2 * n + 1 = 2 * k + 7 := by
          dsimp [k]
          omega
        _ ≤ 9 * 3 ^ k := two_mul_add_seven_le_nine_mul_three_pow k
        _ = 3 ^ (n - 1) := by
          rw [hk, pow_add]
          norm_num
          ring
    have hthree :
        3 ^ (2 * n + 1) ≤ 3 ^ (3 ^ (n - 1)) :=
      Nat.pow_le_pow_right (by norm_num) hexp
    have hpositive : 0 < 3 ^ (n - 1) := by positivity
    have hseven :
        3 ^ (3 ^ (n - 1)) < 7 ^ (3 ^ (n - 1)) :=
      Nat.pow_lt_pow_left (by norm_num) hpositive.ne'
    have hbOne : 1 ≤ b := hb
    have hexpB : 3 ^ (n - 1) ≤ 3 ^ (n - 1) * b := by
      simpa only [mul_one] using
        Nat.mul_le_mul_left (3 ^ (n - 1)) hbOne
    exact hthree.trans_lt (hseven.trans_le
      (Nat.pow_le_pow_right (by norm_num) hexpB))

/-! ## Main union-bound theorem -/

/-- **Odd extraspecial union-bound inequality.**

Let `r` and `p` be distinct odd primes.  If `p ∣ r ^ a - 1` and the
module dimension has the extraspecial multiplicity
`d = a * p ^ n * b`, with all three parameters positive, then the union of
the `p ^ (2*n+1) - 1` possible nontrivial fixed-space contributions and one
forbidden orbit is strictly smaller than the whole module. -/
theorem extraspecial_union_bound
    {r p n a b d : ℕ}
    (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hrTwo : r ≠ 2) (hpTwo : p ≠ 2) (hrp : r ≠ p)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hdiv : p ∣ r ^ a - 1)
    (hd : d = a * p ^ n * b) :
    (p ^ (2 * n + 1) - 1) * r ^ (d / p) + p ^ (2 * n + 1) <
      r ^ d := by
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
  have htop : r ^ (a * p ^ (k + 1) * b) = x ^ p := by
    rw [hdExp, pow_mul]
  have hbase : 2 * p + 1 ≤ r ^ a :=
    two_mul_prime_add_one_le_pow_of_dvd_sub_one
      hr hp hrTwo hpTwo ha hdiv
  have hxEq : x = (r ^ a) ^ (p ^ k * b) := by
    dsimp [x, e]
    rw [show a * p ^ k * b = a * (p ^ k * b) by ring, pow_mul]
  have hxLower : (2 * p + 1) ^ (p ^ k * b) ≤ x := by
    rw [hxEq]
    exact Nat.pow_le_pow_left hbase _
  have hmPos : 0 < p ^ k * b :=
    Nat.mul_pos (pow_pos hp.pos _) hb
  have hblock : 2 * p + 1 ≤ (2 * p + 1) ^ (p ^ k * b) := by
    calc
      2 * p + 1 = (2 * p + 1) ^ 1 := by simp
      _ ≤ (2 * p + 1) ^ (p ^ k * b) :=
        Nat.pow_le_pow_right (by omega) hmPos
  have hx : 2 ≤ x := by
    have htwoBlock : 2 ≤ 2 * p + 1 := by
      have := hp.two_le
      omega
    exact htwoBlock.trans (hblock.trans hxLower)
  have hmain :
      (p ^ (2 * (k + 1) + 1) - 1) * x +
          p ^ (2 * (k + 1) + 1) < x ^ p := by
    by_cases hpThree : p = 3
    · subst p
      cases k with
      | zero =>
          have hxSeven : 7 ≤ x := by
            have hbOne : 1 ≤ b := hb
            have hsevenPow : 7 ≤ 7 ^ b := by
              calc
                7 = 7 ^ 1 := by norm_num
                _ ≤ 7 ^ b := Nat.pow_le_pow_right (by norm_num) hbOne
            norm_num at hxLower
            exact hsevenPow.trans hxLower
          norm_num
          have h26 : 26 ≤ 4 * x := by omega
          have hfirst : 26 * x ≤ (4 * x) * x :=
            Nat.mul_le_mul_right x h26
          have hfour : 4 * x ≤ x * x := by
            exact Nat.mul_le_mul_right x (by omega)
          have hsecond : 27 < x * x := by
            exact (by omega : 27 < 4 * x) |>.trans_le hfour
          have hsum : 26 * x + 27 < (4 * x) * x + x * x :=
            Nat.add_lt_add_of_le_of_lt hfirst hsecond
          have hfive : 5 * (x * x) < x * (x * x) :=
            Nat.mul_lt_mul_of_pos_right (by omega) (by positivity)
          nlinarith
      | succ k =>
          have hnTwo : 2 ≤ k + 2 := by omega
          have horderMin :
              3 ^ (2 * (k + 2) + 1) < 7 ^ (3 ^ (k + 1) * b) :=
            three_extraspecial_order_lt_minimalBlock hnTwo hb
          have horder : 3 ^ (2 * (k + 2) + 1) < x := by
            exact horderMin.trans_le (by simpa using hxLower)
          simpa only [zero_add, pow_one] using
            (extraspecial_union_bound_of_order_lt
              (q := 3 ^ (2 * (k + 2) + 1)) (x := x) (k := 0)
              hx (by simpa using horder))
    · have hpOdd := hp.odd_of_ne_two hpTwo
      have hpFive : 5 ≤ p := by
        obtain ⟨j, hj⟩ := hpOdd
        have hpTwoLe := hp.two_le
        omega
      have horderMin :
          p ^ (2 * (k + 1) + 1) <
            ((2 * p + 1) ^ (p ^ k * b)) ^ (p - 2) :=
        extraspecial_order_lt_minimalBlock_pow_sub_two
          hpFive (by omega) hb
      have horder :
          p ^ (2 * (k + 1) + 1) < x ^ (p - 2) :=
        horderMin.trans_le (Nat.pow_le_pow_left hxLower _)
      have hgeneric :=
        extraspecial_union_bound_of_order_lt
          (q := p ^ (2 * (k + 1) + 1)) (x := x) (k := p - 3)
          hx (by simpa [show p - 3 + 1 = p - 2 by omega] using horder)
      simpa [show p - 3 + 3 = p by omega] using hgeneric
  simpa only [hquot, x, htop] using hmain

end LisiSabatini
