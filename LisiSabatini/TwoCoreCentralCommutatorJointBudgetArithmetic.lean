import LisiSabatini.TwoCoreDistinguishedJointBudgetArithmetic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Linarith

/-!
# Joint-budget residual for the central-commutator branch

If `Q = |P/Z(P)|` and `Z = |Z(P)|`, the elementary central-coset count
gives at most `2(Q-1)` active involutions, while
`|P| = QZ`.  A fixed-point-free cyclic center gives `Z ≤ q-1`.

The remaining comparison is therefore the transparent inequality
`8Q < q+6`.  Since the operator comparison gives `Q ≤ d²`, it is enough
to prove `8d² < r^d+6`.  This file isolates that exact theorem-level
residual rather than conflating it with half-density.
-/

namespace LisiSabatini

/-- The quotient-center size comparison closes the exact joint envelope
for the central-commutator shape. -/
theorem centralCommutator_jointEnvelopeBudget_of_quotientCenter
    {q quotientCenter centerOrder : ℕ}
    (hq : 1 < q)
    (hcenter : centerOrder ≤ q - 1)
    (hsize : 8 * quotientCenter < q + 6) :
    DistinguishedTwoCoreJointEnvelopeBudget
      q (2 * (quotientCenter - 1))
        (quotientCenter * centerOrder) := by
  have hactive :
      2 * (2 * (quotientCenter - 1)) ≤ q + 2 := by
    omega
  have hgap :
      4 * quotientCenter <
        q + 2 - 2 * (2 * (quotientCenter - 1)) := by
    omega
  have hqPred : 0 < q - 1 := by omega
  have hresidual :
      4 * (quotientCenter * centerOrder) <
        (q - 1) *
          (q + 2 - 2 * (2 * (quotientCenter - 1))) := by
    calc
      4 * (quotientCenter * centerOrder) ≤
          4 * (quotientCenter * (q - 1)) :=
        Nat.mul_le_mul_left 4
          (Nat.mul_le_mul_left quotientCenter hcenter)
      _ = (q - 1) * (4 * quotientCenter) := by ring
      _ < (q - 1) *
          (q + 2 - 2 * (2 * (quotientCenter - 1))) :=
        Nat.mul_lt_mul_of_pos_left hgap hqPred
  exact
    distinguishedTwo_jointEnvelopeBudget_of_residual
      hactive hresidual

/-- The ambient endomorphism-dimension bound reduces the central branch
to the numerical comparison `8*d² < q+6`. -/
theorem centralCommutator_jointEnvelopeBudget_of_dimension
    {q d quotientCenter centerOrder : ℕ}
    (hq : 1 < q)
    (hquotient : quotientCenter ≤ d * d)
    (hcenter : centerOrder ≤ q - 1)
    (hdimension : 8 * d * d < q + 6) :
    DistinguishedTwoCoreJointEnvelopeBudget
      q (2 * (quotientCenter - 1))
        (quotientCenter * centerOrder) := by
  apply centralCommutator_jointEnvelopeBudget_of_quotientCenter
    hq hcenter
  calc
    8 * quotientCenter ≤ 8 * (d * d) :=
      Nat.mul_le_mul_left 8 hquotient
    _ = 8 * d * d := by ring
    _ < q + 6 := hdimension

/-- From dimension six onward, the odd-characteristic module outgrows
the quotient-center envelope. -/
private theorem eight_mul_sq_le_three_pow
    (d : ℕ) (hd : 6 ≤ d) :
    8 * d * d ≤ 3 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      calc
        8 * (n + 1) * (n + 1) ≤
            3 * (8 * n * n) := by
          nlinarith
        _ ≤ 3 * 3 ^ n :=
          Nat.mul_le_mul_left 3 ih
        _ = 3 ^ n * 3 := by ring

/-- The dimension comparison is automatic outside exactly three small
odd-characteristic modules: `F₃²`, `F₅²`, and `F₃⁴`. -/
theorem eight_mul_dimension_sq_lt_field_pow_add_six
    {r d : ℕ} [Fact r.Prime]
    (hrTwo : r ≠ 2)
    (hd : 0 < d)
    (hdeven : Even d)
    (hsmall :
      (r ≠ 3 ∨ d ≠ 2) ∧
      (r ≠ 5 ∨ d ≠ 2) ∧
      (r ≠ 3 ∨ d ≠ 4)) :
    8 * d * d < r ^ d + 6 := by
  have hrThree : 3 ≤ r := by
    have hrTwoLe := (Fact.out : r.Prime).two_le
    omega
  by_cases hdTwo : d = 2
  · subst d
    have hrNeThree : r ≠ 3 := hsmall.1.resolve_right (by norm_num)
    have hrNeFive : r ≠ 5 := hsmall.2.1.resolve_right (by norm_num)
    have hrSeven : 7 ≤ r := by
      obtain ⟨k, hk⟩ :=
        (Fact.out : r.Prime).odd_of_ne_two hrTwo
      omega
    rw [pow_two]
    nlinarith
  · by_cases hdFour : d = 4
    · subst d
      have hrNeThree : r ≠ 3 :=
        hsmall.2.2.resolve_right (by norm_num)
      have hrFive : 5 ≤ r := by
        obtain ⟨k, hk⟩ :=
          (Fact.out : r.Prime).odd_of_ne_two hrTwo
        omega
      norm_num
      have : 5 ^ 4 ≤ r ^ 4 :=
        Nat.pow_le_pow_left hrFive 4
      norm_num at this ⊢
      omega
    · have hdSix : 6 ≤ d := by
        obtain ⟨m, hm⟩ := hdeven
        omega
      calc
        8 * d * d ≤ 3 ^ d :=
          eight_mul_sq_le_three_pow d hdSix
        _ ≤ r ^ d :=
          Nat.pow_le_pow_left hrThree d
        _ < r ^ d + 6 :=
          Nat.lt_add_of_pos_right (by norm_num)

end LisiSabatini
