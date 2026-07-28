module

public import LisiSabatini.OddCharacteristicTwoCoreTwoOrbitReserve
public import LisiSabatini.TwoCoreMixedJointBudgetArithmetic

/-!
# The full distinguished-two budget for a mixed two-core

This file combines the mixed central-product count, the head-field
growth theorem, and the exact distinguished-two residual arithmetic.
The factor map gives the deliberately coarse but sufficient order bound
`|P| ≤ 4 N e²`; no cardinality formula for an internal central product is
needed.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uI

namespace BergerMaximalClassHead

/-- Every maximal-class head has twice its rotation order. -/
theorem natCard_eq_two_mul_rotationOrder
    {H : Type*} [Group H] [Finite H]
    (head : BergerMaximalClassHead H) :
    Nat.card H = 2 * head.rotationOrder := by
  cases head with
  | dihedral k hk e =>
      calc
        Nat.card H = Nat.card (DihedralGroup (4 * k)) :=
          Nat.card_congr e.toEquiv
        _ = 2 * (4 * k) := DihedralGroup.nat_card
        _ = 2 *
            (BergerMaximalClassHead.dihedral k hk e).rotationOrder := by
          rfl
  | semidihedral k hk presentation =>
      letI : NeZero (8 * k) :=
        ⟨mul_ne_zero (by norm_num) hk.ne'⟩
      letI : NeZero (k * 8) :=
        ⟨mul_ne_zero hk.ne' (by norm_num)⟩
      calc
        Nat.card H =
            Nat.card (ZMod (8 * k) ⊕ ZMod (8 * k)) :=
          Nat.card_congr presentation.normalForm.symm
        _ = 2 * (8 * k) := by
          simp only [Nat.card_sum, Nat.card_zmod]
          ring
        _ = 2 *
            (BergerMaximalClassHead.semidihedral
              k hk presentation).rotationOrder := by
          rfl
  | generalizedQuaternion n hn e =>
      letI : NeZero n := ⟨by omega⟩
      calc
        Nat.card H = Nat.card (QuaternionGroup n) :=
          Nat.card_congr e.toEquiv
        _ = 4 * n := by
          rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
        _ = 2 *
            (BergerMaximalClassHead.generalizedQuaternion
              n hn e).rotationOrder := by
          simp only [rotationOrder]
          ring

/-- The sign-independent mixed active envelope is at most `N e²`. -/
theorem countingEnvelope_le_rotationOrder_mul_sq
    {H : Type*} [Group H] [Finite H]
    (head : BergerMaximalClassHead H)
    (e : ℕ) (he : 2 ≤ e) :
    head.countingEnvelope e ≤ head.rotationOrder * e * e := by
  cases head with
  | dihedral k hk equiv =>
      simp only [countingEnvelope, rotationOrder]
      have hkdiv : 4 * k / 2 = 2 * k := by omega
      rw [hkdiv]
      have hkTo :
          k ≤ (k - 1) * e := by
        calc
          k ≤ 2 * (k - 1) := by omega
          _ ≤ e * (k - 1) :=
            Nat.mul_le_mul_right (k - 1) he
          _ = (k - 1) * e := Nat.mul_comm _ _
      have htail :
          2 * k * e ≤ 2 * (k - 1) * (e * e) := by
        have h := Nat.mul_le_mul_left (2 * e) hkTo
        simpa only [mul_assoc, mul_comm, mul_left_comm] using h
      calc
        (2 * k + 2) * (e * e) + 2 * k * e ≤
            (2 * k + 2) * (e * e) +
              2 * (k - 1) * (e * e) :=
          Nat.add_le_add_left htail _
        _ = 4 * k * e * e := by
          have hcoeff :
              (2 * k + 2) + 2 * (k - 1) = 4 * k := by
            omega
          calc
            (2 * k + 2) * (e * e) +
                  2 * (k - 1) * (e * e) =
                ((2 * k + 2) + 2 * (k - 1)) * (e * e) := by
              ring
            _ = (4 * k) * (e * e) := by rw [hcoeff]
            _ = 4 * k * e * e := by ring
  | semidihedral k hk presentation =>
      simp only [countingEnvelope, rotationOrder]
      have hkdiv : 8 * k / 2 = 4 * k := by omega
      rw [hkdiv]
      have hcoeff : 4 * k + 2 ≤ 8 * k := by omega
      simpa only [mul_assoc] using
        (Nat.mul_le_mul_right (e * e) hcoeff)
  | generalizedQuaternion n hn equiv =>
      simp only [countingEnvelope, rotationOrder]
      have hndiv : 2 * n / 2 = n := by omega
      rw [hndiv]
      have hnTo :
          n ≤ (n - 2) * e := by
        calc
          n ≤ 2 * (n - 2) := by omega
          _ ≤ e * (n - 2) :=
            Nat.mul_le_mul_right (n - 2) he
          _ = (n - 2) * e := Nat.mul_comm _ _
      have htail :
          n * e ≤ (n - 2) * (e * e) := by
        have h := Nat.mul_le_mul_left e hnTo
        simpa only [mul_assoc, mul_comm, mul_left_comm] using h
      calc
        (n + 2) * (e * e) + n * e ≤
            (n + 2) * (e * e) +
              (n - 2) * (e * e) :=
          Nat.add_le_add_left htail _
        _ = 2 * n * e * e := by
          have hcoeff :
              (n + 2) + (n - 2) = 2 * n := by
            omega
          calc
            (n + 2) * (e * e) +
                  (n - 2) * (e * e) =
                ((n + 2) + (n - 2)) * (e * e) := by
              ring
            _ = (2 * n) * (e * e) := by rw [hcoeff]
            _ = 2 * n * e * e := by ring

end BergerMaximalClassHead

namespace BergerMixedCentralProductData

/-- The chosen factorization injects the ambient mixed product into the
Cartesian product of its two factors. -/
private theorem factor_injective
    {P : Type*} [Group P] [Finite P]
    (data : BergerMixedCentralProductData P) :
    Function.Injective data.factor := by
  intro x y hxy
  calc
    x = (data.factor x).1.1 * (data.factor x).2.1 :=
      (data.factor_mul x).symm
    _ = (data.factor y).1.1 * (data.factor y).2.1 := by
      rw [hxy]
    _ = y := data.factor_mul y

/-- Coarse product-cardinality bound for a mixed central product. -/
theorem natCard_le_four_mul_rotationOrder_mul_sq
    {P : Type*} [Group P] [Finite P]
    (data : BergerMixedCentralProductData P)
    (e : ℕ)
    (hcard : Nat.card data.extraspecialPart = 2 * e * e) :
    Nat.card P ≤ 4 * data.head.rotationOrder * e * e := by
  calc
    Nat.card P ≤
        Nat.card (data.extraspecialPart × data.headPart) :=
      Nat.card_le_card_of_injective data.factor data.factor_injective
    _ = Nat.card data.extraspecialPart *
          Nat.card data.headPart := Nat.card_prod _ _
    _ = (2 * e * e) * (2 * data.head.rotationOrder) := by
      rw [hcard, data.head.natCard_eq_two_mul_rotationOrder]
    _ = 4 * data.head.rotationOrder * e * e := by ring

end BergerMixedCentralProductData

variable {r d : ℕ} [Fact r.Prime] [NeZero r]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}

local instance fintypeConcreteLinearSubgroupForMixedJointBudget
    (s f : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin f → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P (finite_linearSubgroup_of_finite P)

abbrev mixedJointMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
  (pCore q K).map K.subtype

private abbrev diagonalMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r)
        ((Fin d → ZMod r) × (Fin d → ZMod r))) :=
  (mixedJointMappedCore (K := K) q).map
    (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))

omit [NeZero r] in
private theorem ncard_nonregular_diagonalMappedCore_eq_affineBadSet
    (q : ℕ) :
    (nonregularVectors
      (diagonalMappedCore (K := K) q)).ncard =
      (affineTwoBaseBadSet
        (mixedJointMappedCore (K := K) q) 0 0).ncard := by
  congr 1
  ext z
  simpa using
    (mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
      (mixedJointMappedCore (K := K) q) 0 0 z).symm

private theorem sum_eq_sum_twoIndex_add_oddIndex
    {I : Type uI} [Fintype I] (p : I → ℕ) (f : I → ℕ) :
    (∑ i, f i) =
      (∑ i : {i : I // p i = 2}, f i.1) +
        ∑ i : {i : I // p i ≠ 2}, f i.1 := by
  classical
  simpa using
    (Fintype.sum_subtype_add_sum_subtype
      (fun i ↦ p i = 2) f).symm

/-- A mixed Hall--Berger core satisfies the complete sharp two-orbit
reserve, not merely half-density. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_mixedCentralProduct_of_degree
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (data : BergerMixedCentralProductData
      (mixedJointMappedCore (K := K) 2))
    (e : ℕ) (he : 2 ≤ e)
    (hcard :
      Nat.card data.extraspecialPart = 2 * e * e) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  let P := mixedJointMappedCore (K := K) 2
  let D := fun q ↦ diagonalMappedCore (K := K) q
  let q := r ^ d
  let N := data.head.rotationOrder
  let F := mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  have hhom :
      Representation.IsHomogeneous
        (linearSubgroupRepresentation P) := by
    simpa only [P] using
      mappedPCore_linearRepresentation_isHomogeneous
        (q := 2) hqp
  let H :=
    (data.headFieldData P e F.pGroup hrTwo hd he hcard hhom).some
  let R := r ^ H.fieldDegree
  let A := data.head.countingEnvelope e
  have hhalf :
      TwoCoreSymplecticTypeHalfDensityData K :=
    twoCoreSymplecticTypeHalfDensityData_of_mixedCentralProduct
      hrTwo hd hqp data
  refine ⟨hhalf, ?_⟩
  intro I _ p hp hinj hcross i₂ hi₂
  classical
  let row : I → ℕ := fun i ↦
    (nonregularVectors (D (p i))).ncard
  let B := (nonregularVectors (D 2)).ncard
  let C := Nat.card (D 2)
  let O := {i : I // p i ≠ 2}
  let pO : O → ℕ := fun i ↦ p i.1
  have hactive :
      (activePrimeOrderElements 2 P).card ≤ A := by
    exact
      data.active_card_le_countingEnvelope_of_extraspecialOrder
        P e hcard
  have hfixed :
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤ q := by
    exact hhalf.2
  have hbad :
      B ≤ 1 + A * (q - 1) := by
    dsimp only [B, D]
    rw [ncard_nonregular_diagonalMappedCore_eq_affineBadSet]
    exact
      ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
        P F.pGroup A q hactive hfixed
  have hcardD :
      C ≤ 4 * N * e * e := by
    have hmap :
        Nat.card (D 2) = Nat.card P :=
      Subgroup.card_map_of_injective
        (K := P)
          (diagonalGeneralLinearHom_injective
            (ZMod r) (Fin d → ZMod r))
    dsimp only [C]
    rw [hmap]
    exact data.natCard_le_four_mul_rotationOrder_mul_sq e hcard
  have hRpredPos : 0 < R - 1 := by
    have hRthree : 3 ≤ R := by
      dsimp only [R]
      have hrThree : 3 ≤ r := by
        have hrTwoLe := (Fact.out : r.Prime).two_le
        omega
      calc
        3 ≤ r := hrThree
        _ = r ^ 1 := by simp
        _ ≤ r ^ H.fieldDegree :=
          Nat.pow_le_pow_right
            (Fact.out : r.Prime).pos H.fieldDegree_pos
    omega
  have hNR : N + 1 ≤ R := by
    have hNle : N ≤ R - 1 :=
      Nat.le_of_dvd hRpredPos H.rotationOrder_dvd
    omega
  have hRq : R ^ e ≤ q := by
    dsimp only [R, q]
    calc
      (r ^ H.fieldDegree) ^ e =
          r ^ (H.fieldDegree * e) := by rw [pow_mul]
      _ ≤ r ^ d :=
        Nat.pow_le_pow_right
          (Fact.out : r.Prime).pos (by
            rw [mul_comm]
            exact H.constituentDimension_le)
  have hAle : A ≤ N * e * e := by
    exact data.head.countingEnvelope_le_rotationOrder_mul_sq e he
  have hbudget :
      DistinguishedTwoCoreJointEnvelopeBudget q A C :=
    mixed_jointEnvelopeBudget_of_headFieldGrowth
      data.head.eight_le_rotationOrder hNR he hRq hAle hcardD
  have hodd :
      2 * (∑ i : O, row i.1) ≤ q * (q - 1) := by
    have h :=
      OddPrimeDiagonalReserve.two_mul_sum_diagonal_bad_le_fieldCard_mul_pred_of_quasiprimitive
        (K := K) hrTwo hd
        (p := pO)
        (fun i ↦ hp i.1)
        (fun i ↦ i.2)
        (fun i ↦ hcross i.1)
        (fun _i _j hij ↦ Subtype.ext (hinj hij))
        hqp
    simpa [row, D, pO, q, diagonalMappedCore, mixedJointMappedCore] using h
  have htwoSum :
      (∑ i : {i : I // p i = 2}, row i.1) = B := by
    have hterm :
        ∀ i : {i : I // p i = 2}, row i.1 = B := by
      intro i
      simp [row, B, i.2]
    have hcardLe :
        Fintype.card {i : I // p i = 2} ≤ 1 := by
      letI : Subsingleton {i : I // p i = 2} :=
        ⟨fun i j ↦ Subtype.ext
          (hinj (i.2.trans j.2.symm))⟩
      exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
    have hcardPos :
        0 < Fintype.card {i : I // p i = 2} :=
      Fintype.card_pos_iff.mpr ⟨⟨i₂, hi₂⟩⟩
    calc
      (∑ i : {i : I // p i = 2}, row i.1) =
          Fintype.card {i : I // p i = 2} * B := by
        simp_rw [hterm]
        simp
      _ = B := by
        have hcardEq :
            Fintype.card {i : I // p i = 2} = 1 := by
          omega
        rw [hcardEq, one_mul]
  have hsplit :
      (∑ i, row i) = B + ∑ i : O, row i.1 := by
    rw [sum_eq_sum_twoIndex_add_oddIndex p row, htwoSum]
  have hjoint :
      B + (∑ i : O, row i.1) + 2 * C < q * q :=
    distinguishedTwo_joint_lt_of_envelopeBudget
      hodd hbad hbudget
  change (∑ i, row i) + 2 * C < r ^ (2 * d)
  rw [hsplit]
  have htop : r ^ (2 * d) = q * q := by
    dsimp only [q]
    rw [← pow_add]
    congr 1
    omega
  rw [htop]
  exact hjoint

/-- The extraspecial degree is intrinsic, so a mixed central-product
description alone supplies the full exact reserve. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_mixedCentralProduct
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (data : BergerMixedCentralProductData
      (mixedJointMappedCore (K := K) 2)) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  obtain ⟨e, he, hcard⟩ :=
    data.extraspecial.exists_degree_card_eq_two_mul_sq
  exact
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_mixedCentralProduct_of_degree
      hrTwo hd hqp data e he hcard

end LisiSabatini
