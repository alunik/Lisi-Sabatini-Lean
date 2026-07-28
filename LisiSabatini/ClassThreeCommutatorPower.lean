module

public import LisiSabatini.ClassTwoCommutator
public import Mathlib.Data.Nat.Choose.Basic

/-!
# A class-three commutator power identity

For mathlib's convention

`⁅x, y⁆ = x * y * x⁻¹ * y⁻¹`,

the class-three collection formula is

`⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n * ⁅x, ⁅x, y⁆⁆ ^ (n.choose 2)`.

The elementwise theorem below uses only the two commutation relations needed
by the collection argument: the triple commutator commutes with `x` and with
`⁅x, y⁆`.  A second theorem packages the usual, stronger hypothesis that the
triple commutator is central.

For an odd exponent `p`, `p ∣ p.choose 2`; hence a triple commutator killed by
`p` contributes no correction term.  The final corollaries expose this form
for the Hall index-prime lifting argument.
-/

@[expose] public section

namespace LisiSabatini

open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

/-- Iterating the conjugation relation
`x * c * x⁻¹ = ⁅x, c⁆ * c` when `x` commutes with `⁅x, c⁆`.

This is the collection step behind the class-three power formula. -/
theorem conjugate_commutatorElement_by_pow (x c : G)
    (hcomm : Commute x ⁅x, c⁆) :
    ∀ n : ℕ, x ^ n * c * (x ^ n)⁻¹ = ⁅x, c⁆ ^ n * c := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      have hconj : x * c * x⁻¹ = ⁅x, c⁆ * c := by
        simp only [commutatorElement_def]
        group
      have hfixed : x ^ n * ⁅x, c⁆ * (x ^ n)⁻¹ = ⁅x, c⁆ := by
        have hncomm : Commute (x ^ n) ⁅x, c⁆ := hcomm.pow_left n
        rw [hncomm.eq]
        group
      calc
        x ^ (n + 1) * c * (x ^ (n + 1))⁻¹ =
            x ^ n * (x * c * x⁻¹) * (x ^ n)⁻¹ := by
              rw [pow_succ, mul_inv_rev]
              group
        _ = x ^ n * (⁅x, c⁆ * c) * (x ^ n)⁻¹ := by rw [hconj]
        _ = (x ^ n * ⁅x, c⁆ * (x ^ n)⁻¹) *
              (x ^ n * c * (x ^ n)⁻¹) := by group
        _ = ⁅x, c⁆ * (⁅x, c⁆ ^ n * c) := by rw [hfixed, ih]
        _ = ⁅x, c⁆ ^ (n + 1) * c := by
          rw [pow_succ']
          simp only [mul_assoc]

/-- The elementwise class-three commutator collection formula under the
minimal local commutation assumptions used by the proof.

The first hypothesis says that the triple commutator is fixed by conjugation
by `x`; the second permits collection of its powers past powers of
`⁅x, y⁆`. -/
theorem commutatorElement_pow_left_of_commute_triple (x y : G)
    (hx : Commute x ⁅x, ⁅x, y⁆⁆)
    (hxy : Commute ⁅x, y⁆ ⁅x, ⁅x, y⁆⁆) :
    ∀ n : ℕ,
      ⁅x ^ n, y⁆ =
        ⁅x, y⁆ ^ n * ⁅x, ⁅x, y⁆⁆ ^ (n.choose 2) := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left,
        conjugate_commutatorElement_by_pow x ⁅x, y⁆ hx, ih]
      calc
        ⁅x, ⁅x, y⁆⁆ ^ n * ⁅x, y⁆ *
              (⁅x, y⁆ ^ n * ⁅x, ⁅x, y⁆⁆ ^ n.choose 2) =
            ⁅x, y⁆ * (⁅x, ⁅x, y⁆⁆ ^ n * ⁅x, y⁆ ^ n) *
              ⁅x, ⁅x, y⁆⁆ ^ n.choose 2 := by
                rw [(hxy.symm.pow_left n).eq]
                group
        _ = ⁅x, y⁆ * (⁅x, y⁆ ^ n * ⁅x, ⁅x, y⁆⁆ ^ n) *
              ⁅x, ⁅x, y⁆⁆ ^ n.choose 2 := by
                rw [(hxy.symm.pow_pow n n).eq]
        _ = ⁅x, y⁆ ^ (n + 1) *
              ⁅x, ⁅x, y⁆⁆ ^ (n + n.choose 2) := by
                rw [pow_succ', pow_add]
                group
        _ = ⁅x, y⁆ ^ (n + 1) *
              ⁅x, ⁅x, y⁆⁆ ^ ((n + 1).choose 2) := by
                rw [Nat.choose_succ_succ, Nat.choose_one_right,
                  Nat.add_comm]

/-- The class-three commutator collection formula from the standard
centrality hypothesis on the triple commutator. -/
theorem commutatorElement_pow_left_of_triple_mem_center (x y : G)
    (htriple : ⁅x, ⁅x, y⁆⁆ ∈ Subgroup.center G) (n : ℕ) :
    ⁅x ^ n, y⁆ =
      ⁅x, y⁆ ^ n * ⁅x, ⁅x, y⁆⁆ ^ (n.choose 2) := by
  apply commutatorElement_pow_left_of_commute_triple x y
  · exact Subgroup.mem_center_iff.mp htriple x
  · exact Subgroup.mem_center_iff.mp htriple ⁅x, y⁆

/-- For every odd natural number `p`, the binomial correction exponent
`p.choose 2` is divisible by `p`. -/
theorem dvd_choose_two_of_odd {p : ℕ} (hpOdd : Odd p) :
    p ∣ p.choose 2 := by
  rcases hpOdd with ⟨k, rfl⟩
  rw [Nat.choose_two_right]
  simp [Nat.mul_div_assoc]

/-- Odd-exponent specialization under the minimal local commutation
hypotheses.  If the triple commutator has exponent dividing `p`, its
binomial correction vanishes. -/
theorem commutatorElement_pow_left_eq_pow_of_odd
    (x y : G) {p : ℕ} (hpOdd : Odd p)
    (hx : Commute x ⁅x, ⁅x, y⁆⁆)
    (hxy : Commute ⁅x, y⁆ ⁅x, ⁅x, y⁆⁆)
    (hpow : ⁅x, ⁅x, y⁆⁆ ^ p = 1) :
    ⁅x ^ p, y⁆ = ⁅x, y⁆ ^ p := by
  rw [commutatorElement_pow_left_of_commute_triple x y hx hxy]
  obtain ⟨k, hk⟩ := dvd_choose_two_of_odd hpOdd
  rw [hk, pow_mul, hpow, one_pow, mul_one]

/-- Central-triple form of the odd-exponent specialization used in the Hall
lifting argument. -/
theorem commutatorElement_pow_left_eq_pow_of_triple_mem_center_of_odd
    (x y : G) {p : ℕ} (hpOdd : Odd p)
    (htriple : ⁅x, ⁅x, y⁆⁆ ∈ Subgroup.center G)
    (hpow : ⁅x, ⁅x, y⁆⁆ ^ p = 1) :
    ⁅x ^ p, y⁆ = ⁅x, y⁆ ^ p := by
  apply commutatorElement_pow_left_eq_pow_of_odd x y hpOdd
  · exact Subgroup.mem_center_iff.mp htriple x
  · exact Subgroup.mem_center_iff.mp htriple ⁅x, y⁆
  · exact hpow

end Group

end LisiSabatini
