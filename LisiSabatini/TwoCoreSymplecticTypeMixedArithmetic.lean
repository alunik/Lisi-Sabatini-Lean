import LisiSabatini.TwoCoreSymplecticTypeMixedCount

/-!
# Arithmetic for mixed symplectic-type two-cores

This file closes the purely numerical part of the mixed
extraspecial--maximal-class branch.  If `e` is the extraspecial degree,
`N` the rotation order of the maximal-class head, and a head field of
degree `a` satisfies

* `N ∣ r^a - 1`,
* `e*a ≤ d`, and
* `2*e ≤ d`,

then Berger's exact active-involution envelope is at most half of the
nonzero vectors:

`2 * activeEnvelope ≤ r^d - 1`.

Thus the remaining mixed gaps are structural/representation-theoretic,
not arithmetic.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- The elementary exponential estimate behind the mixed envelope. -/
private theorem two_mul_add_two_sq_lt_nine_pow_add_one
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
          omega

/-- Uniform form over every base at least nine. -/
private theorem two_mul_sq_lt_pow_pred
    (R e : ℕ) (hR : 9 ≤ R) (he : 2 ≤ e) :
    2 * e * e < R ^ (e - 1) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le he
  calc
    2 * (2 + m) * (2 + m) =
        2 * (m + 2) * (m + 2) := by ring
    _ < 9 ^ (m + 1) :=
      two_mul_add_two_sq_lt_nine_pow_add_one m
    _ ≤ R ^ (m + 1) :=
      Nat.pow_le_pow_left hR (m + 1)
    _ = R ^ (2 + m - 1) := by
      congr 1
      omega

/-- Every one of the three exact formulas is bounded by the dihedral
upper envelope before its final subtraction. -/
private theorem two_mul_activeEnvelope_le_dihedralEnvelope
    {H : Type*} [Group H] [Finite H]
    (head : BergerMaximalClassHead H) (e : ℕ) :
    2 * head.activeEnvelope e ≤
      2 * ((head.rotationOrder / 2 + 2) * (e * e) +
        (head.rotationOrder / 2) * e) := by
  cases head <;>
    simp only [BergerMaximalClassHead.activeEnvelope,
      BergerMaximalClassHead.rotationOrder] <;>
    omega

/-- The sign-independent counting envelope is also bounded by the
dihedral upper envelope. -/
private theorem two_mul_countingEnvelope_le_dihedralEnvelope
    {H : Type*} [Group H] [Finite H]
    (head : BergerMaximalClassHead H) (e : ℕ) :
    2 * head.countingEnvelope e ≤
      2 * ((head.rotationOrder / 2 + 2) * (e * e) +
        (head.rotationOrder / 2) * e) := by
  cases head <;>
    simp only [BergerMaximalClassHead.countingEnvelope,
      BergerMaximalClassHead.rotationOrder] <;>
    omega

/-- The head-field degree data control the common dihedral upper
envelope used by both the exact and sign-independent counts. -/
theorem two_mul_dihedralEnvelope_le_nonzero_of_headFieldData
    {r d : ℕ} [Fact r.Prime]
    {P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    [Finite P]
    (hrTwo : r ≠ 2)
    (data : BergerMixedCentralProductData P)
    (e : ℕ) (he : 2 ≤ e)
    (H : MixedCentralProductHeadFieldData data e) :
    2 * ((data.head.rotationOrder / 2 + 2) * (e * e) +
      (data.head.rotationOrder / 2) * e) ≤ r ^ d - 1 := by
  let N := data.head.rotationOrder
  let R := r ^ H.fieldDegree
  have hrThree : 3 ≤ r := by
    have hrTwoLe := (Fact.out : r.Prime).two_le
    omega
  have hRThree : 3 ≤ R := by
    dsimp only [R]
    calc
      3 ≤ r := hrThree
      _ = r ^ 1 := by simp
      _ ≤ r ^ H.fieldDegree :=
        Nat.pow_le_pow_right
          (Fact.out : r.Prime).pos H.fieldDegree_pos
  have hRpredPos : 0 < R - 1 := by omega
  have hNle : N ≤ R - 1 := by
    exact Nat.le_of_dvd hRpredPos H.rotationOrder_dvd
  have hNEight : 8 ≤ N :=
    data.head.eight_le_rotationOrder
  have hRNine : 9 ≤ R := by omega
  have htwiceHalf : 2 * (N / 2) ≤ N := by omega
  have hhalf :
      2 * (N / 2) ≤ R - 1 :=
    htwiceHalf.trans hNle
  have hhalfR :
      2 * (N / 2) + 1 ≤ R := by omega
  have hhalfFour :
      4 ≤ N / 2 := by omega
  let t := N / 2
  let E := e * e
  have htFour : 4 ≤ t := by
    simpa only [t] using hhalfFour
  have htFactor :
      t ≤ (t - 1) * e := by
    calc
      t ≤ 2 * (t - 1) := by omega
      _ ≤ e * (t - 1) :=
        Nat.mul_le_mul_right (t - 1) he
      _ = (t - 1) * e := Nat.mul_comm _ _
  have hte :
      t * e ≤ (t - 1) * E := by
    dsimp only [E]
    calc
      t * e ≤ ((t - 1) * e) * e :=
        Nat.mul_le_mul_right e htFactor
      _ = (t - 1) * (e * e) := by ring
  have halgebra :
      (t + 2) * E + (t - 1) * E =
        (2 * t + 1) * E := by
    rw [← add_mul]
    congr 1
    omega
  have hbase :
      (t + 2) * E + t * e ≤ R * E := by
    calc
      (t + 2) * E + t * e ≤
          (t + 2) * E + (t - 1) * E :=
        Nat.add_le_add_left hte _
      _ = (2 * t + 1) * E := halgebra
      _ ≤ R * E :=
        Nat.mul_le_mul_right E (by
          simpa only [t] using hhalfR)
  have hcoefficient :
      2 * ((N / 2 + 2) * (e * e) +
          (N / 2) * e) ≤
        2 * R * e * e := by
    have htwice := Nat.mul_le_mul_left 2 hbase
    simpa only [t, E, mul_assoc] using htwice
  have hsmall :
      2 * e * e < R ^ (e - 1) :=
    two_mul_sq_lt_pow_pred R e hRNine he
  have hRpos : 0 < R := by omega
  have hRstrict :
      2 * R * e * e < R ^ e := by
    calc
      2 * R * e * e = R * (2 * e * e) := by ring
      _ < R * R ^ (e - 1) :=
        Nat.mul_lt_mul_of_pos_left hsmall hRpos
      _ = R ^ e := by
        rw [mul_comm, ← pow_succ]
        congr 1
        omega
  have hRpow :
      R ^ e ≤ r ^ d := by
    calc
      R ^ e = r ^ (H.fieldDegree * e) := by
        simp [R, pow_mul]
      _ ≤ r ^ d :=
        Nat.pow_le_pow_right
          (Fact.out : r.Prime).pos (by
            rw [mul_comm]
            exact H.constituentDimension_le)
  have hstrict :
      2 * ((N / 2 + 2) * (e * e) +
        (N / 2) * e) < r ^ d := by
    calc
      2 * ((N / 2 + 2) * (e * e) +
          (N / 2) * e) ≤ 2 * R * e * e := hcoefficient
      _ < R ^ e := hRstrict
      _ ≤ r ^ d := hRpow
  simpa only [N] using Nat.le_sub_one_of_lt hstrict

/-- The head-field degree data imply the sharp exact-envelope
half-density comparison. -/
theorem two_mul_mixedActiveEnvelope_le_nonzero_of_headFieldData
    {r d : ℕ} [Fact r.Prime]
    {P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    [Finite P]
    (hrTwo : r ≠ 2)
    (data : BergerMixedCentralProductData P)
    (e : ℕ) (he : 2 ≤ e)
    (H : MixedCentralProductHeadFieldData data e) :
    2 * data.head.activeEnvelope e ≤ r ^ d - 1 := by
  exact
    (two_mul_activeEnvelope_le_dihedralEnvelope data.head e).trans
      (two_mul_dihedralEnvelope_le_nonzero_of_headFieldData
        hrTwo data e he H)

/-- The same arithmetic controls the sign-independent counting
envelope used by the intrinsic central-product proof. -/
theorem two_mul_countingEnvelope_le_nonzero_of_headFieldData
    {r d : ℕ} [Fact r.Prime]
    {P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    [Finite P]
    (hrTwo : r ≠ 2)
    (data : BergerMixedCentralProductData P)
    (e : ℕ) (he : 2 ≤ e)
    (H : MixedCentralProductHeadFieldData data e) :
    2 * data.head.countingEnvelope e ≤ r ^ d - 1 := by
  exact
    (two_mul_countingEnvelope_le_dihedralEnvelope data.head e).trans
      (two_mul_dihedralEnvelope_le_nonzero_of_headFieldData
        hrTwo data e he H)

/-- The two named mixed inputs assemble directly into the active-element
half-density bound used by the odd-characteristic argument. -/
theorem two_mul_card_activePrimeOrderElements_le_nonzero_of_mixedStatements
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (data : BergerMixedCentralProductData P)
    (e : ℕ) (he : 2 ≤ e)
    (hcard : Nat.card data.extraspecialPart = 2 * e * e)
    (C : CenterFixedPointFreeAction r d P)
    (hhomogeneous :
      Representation.IsHomogeneous (linearSubgroupRepresentation P))
    (hcount : MixedCentralProductActiveCountStatement)
    (hfield : MixedCentralProductHeadFieldDegreeStatement) :
    2 * (activePrimeOrderElements 2 P).card ≤ r ^ d - 1 := by
  have hactive :
      (activePrimeOrderElements 2 P).card ≤
        data.head.activeEnvelope e :=
    hcount P data e he hcard C
  obtain ⟨headFieldData⟩ :=
    hfield P data e hP hrTwo hd he hcard hhomogeneous
  exact (Nat.mul_le_mul_left 2 hactive).trans
    (two_mul_mixedActiveEnvelope_le_nonzero_of_headFieldData
      hrTwo data e he headFieldData)

end LisiSabatini
