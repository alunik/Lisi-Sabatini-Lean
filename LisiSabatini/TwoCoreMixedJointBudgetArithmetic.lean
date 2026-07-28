import LisiSabatini.TwoCoreDistinguishedJointBudgetArithmetic
import Mathlib.Tactic.Linarith

/-!
# Joint-budget arithmetic for a mixed symplectic-type two-core

Write `N` for the rotation order of the maximal-class head, `e` for the
extraspecial degree, and `R` for the head-field cardinality.  The mixed
structure supplies `N + 1 ≤ R`, `R^e ≤ q`, an active envelope at most
`N e²`, and the elementary factor-map order bound
`|P| ≤ 4 N e²`.

The exponential inequality `2e² < R^(e-1)` leaves enough *simultaneous*
slack for both the active rectangle envelope and two full core orbits.
This is stronger than applying half-density and the order estimate
separately.
-/

namespace LisiSabatini

/-- The elementary exponential estimate used in the mixed joint budget. -/
private theorem two_mul_add_two_sq_lt_nine_pow_add_one_joint
    (m : ℕ) :
    2 * (m + 2) * (m + 2) < 9 ^ (m + 1) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      calc
        2 * (m + 1 + 2) * (m + 1 + 2) ≤
            9 * (2 * (m + 2) * (m + 2)) := by
          nlinarith
        _ < 9 * 9 ^ (m + 1) :=
          Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 9 ^ (m + 1 + 1) := by
          rw [pow_succ]
          ring

/-- Uniform exponential estimate over every base at least nine. -/
theorem two_mul_sq_lt_pow_pred_of_nine_le
    (R e : ℕ) (hR : 9 ≤ R) (he : 2 ≤ e) :
    2 * e * e < R ^ (e - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le he
  calc
    2 * (2 + m) * (2 + m) =
        2 * (m + 2) * (m + 2) := by ring
    _ < 9 ^ (m + 1) :=
      two_mul_add_two_sq_lt_nine_pow_add_one_joint m
    _ ≤ R ^ (m + 1) :=
      Nat.pow_le_pow_left hR (m + 1)
    _ = R ^ (2 + m - 1) := by
      congr 1
      omega

/-- Abstract mixed-shape joint inequality.

`activeBound` and `coreOrderBound` may be strict overestimates.  In the
group-theoretic application they are respectively the dihedral head
envelope and the factor-map product-cardinality bound. -/
theorem mixed_jointEnvelopeBudget_of_headFieldGrowth
    {N R e q activeBound coreOrderBound : ℕ}
    (hN : 8 ≤ N)
    (hR : N + 1 ≤ R)
    (he : 2 ≤ e)
    (hq : R ^ e ≤ q)
    (hactive : activeBound ≤ N * e * e)
    (hcore : coreOrderBound ≤ 4 * N * e * e) :
    DistinguishedTwoCoreJointEnvelopeBudget
      q activeBound coreOrderBound := by
  let X := R ^ (e - 1)
  have hRNine : 9 ≤ R := by omega
  have hsmall : 2 * e * e < X := by
    simpa only [X] using
      two_mul_sq_lt_pow_pred_of_nine_le R e hRNine he
  have hNpos : 0 < N := by omega
  have hRpos : 0 < R := by omega
  have hePred : 1 ≤ e - 1 := by omega
  have hpow : R ^ e = R * X := by
    dsimp only [X]
    calc
      R ^ e = R ^ ((e - 1) + 1) := by
        congr 1
        omega
      _ = R ^ (e - 1) * R := by rw [pow_succ]
      _ = R * R ^ (e - 1) := Nat.mul_comm _ _
  have hactiveStrict :
      2 * activeBound < N * X := by
    calc
      2 * activeBound ≤ 2 * (N * e * e) :=
        Nat.mul_le_mul_left 2 hactive
      _ = N * (2 * e * e) := by ring
      _ < N * X :=
        Nat.mul_lt_mul_of_pos_left hsmall hNpos
  have hactiveGap :
      2 * activeBound + X < q := by
    calc
      2 * activeBound + X < N * X + X :=
        Nat.add_lt_add_right hactiveStrict X
      _ = (N + 1) * X := by ring
      _ ≤ R * X :=
        Nat.mul_le_mul_right X hR
      _ = R ^ e := hpow.symm
      _ ≤ q := hq
  have hactiveLe : 2 * activeBound ≤ q + 2 := by
    omega
  have hgap :
      X + 3 ≤ q + 2 - 2 * activeBound := by
    omega
  have hRleX : R ≤ X := by
    calc
      R = R ^ 1 := by simp
      _ ≤ R ^ (e - 1) :=
        Nat.pow_le_pow_right hRpos hePred
      _ = X := rfl
  have hqPred :
      8 * N ≤ q - 1 := by
    have hsix : 6 * N ≤ N * N :=
      Nat.mul_le_mul_right N (by omega)
    have hbase :
        8 * N + 1 ≤ (N + 1) * (N + 1) := by
      calc
        8 * N + 1 = 6 * N + (2 * N + 1) := by ring
        _ ≤ N * N + (2 * N + 1) :=
          Nat.add_le_add_right hsix (2 * N + 1)
        _ = (N + 1) * (N + 1) := by ring
    have hqLower : 8 * N + 1 ≤ q := by
      calc
        8 * N + 1 ≤ (N + 1) * (N + 1) := hbase
        _ ≤ R * R :=
          Nat.mul_le_mul hR hR
        _ ≤ R * X :=
          Nat.mul_le_mul_left R hRleX
        _ = R ^ e := hpow.symm
        _ ≤ q := hq
    exact
      Nat.le_sub_one_of_lt
        ((Nat.lt_succ_self (8 * N)).trans_le hqLower)
  have hresidual :
      4 * coreOrderBound <
        (q - 1) * (q + 2 - 2 * activeBound) := by
    calc
      4 * coreOrderBound ≤ 4 * (4 * N * e * e) :=
        Nat.mul_le_mul_left 4 hcore
      _ = (8 * N) * (2 * e * e) := by ring
      _ < (8 * N) * (X + 3) :=
        Nat.mul_lt_mul_of_pos_left
          (hsmall.trans
            (Nat.lt_add_of_pos_right (by norm_num : 0 < 3)))
          (by positivity)
      _ ≤ (q - 1) * (q + 2 - 2 * activeBound) :=
        Nat.mul_le_mul hqPred hgap
  exact
    distinguishedTwo_jointEnvelopeBudget_of_residual
      hactiveLe hresidual

end LisiSabatini
