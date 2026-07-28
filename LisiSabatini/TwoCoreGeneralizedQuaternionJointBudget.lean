module

public import LisiSabatini.OddCharacteristicTwoCoreTwoOrbitReserve

/-!
# The full distinguished-two budget for a generalized-quaternion core

Every involution in a generalized quaternion group is central.  In a
center-fixed-point-free representation of a finite `2`-group, this forces
the whole group to act fixed-point-freely away from zero: any nontrivial
point stabilizer contains an involution, and that involution would be an
active central element.

Consequently the doubled bad locus has at most one point and the group
order divides the number of nonzero vectors.  Together with the existing
odd-row estimate, these two facts close the exact distinguished-two
reserve.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uI

variable {r d : ℕ} [Fact r.Prime] [NeZero r]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}

local instance fintypeConcreteLinearSubgroupForQuaternionJointBudget
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin e → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P (finite_linearSubgroup_of_finite P)

abbrev generalizedQuaternionJointMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
  (pCore q K).map K.subtype

private abbrev diagonalMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r)
        ((Fin d → ZMod r) × (Fin d → ZMod r))) :=
  (generalizedQuaternionJointMappedCore (K := K) q).map
    (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))

omit [NeZero r] in
private theorem ncard_nonregular_diagonalMappedCore_eq_affineBadSet
    (q : ℕ) :
    (nonregularVectors
      (diagonalMappedCore (K := K) q)).ncard =
      (affineTwoBaseBadSet
        (generalizedQuaternionJointMappedCore (K := K) q) 0 0).ncard := by
  congr 1
  ext z
  simpa using
    (mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
      (generalizedQuaternionJointMappedCore (K := K) q) 0 0 z).symm

private abbrev TwoIndex {I : Type uI} (p : I → ℕ) :=
  {i : I // p i = 2}

private abbrev OddIndex {I : Type uI} (p : I → ℕ) :=
  {i : I // p i ≠ 2}

private theorem sum_eq_sum_twoIndex_add_oddIndex
    {I : Type uI} [Fintype I] (p : I → ℕ) (f : I → ℕ) :
    (∑ i, f i) =
      (∑ i : TwoIndex p, f i.1) +
        ∑ i : OddIndex p, f i.1 := by
  classical
  simpa [TwoIndex, OddIndex] using
    (Fintype.sum_subtype_add_sum_subtype
      (fun i ↦ p i = 2) f).symm

private theorem card_twoIndex_le_one
    {I : Type uI} [Fintype I] (p : I → ℕ)
    (hinj : Function.Injective p) :
    Fintype.card (TwoIndex p) ≤ 1 := by
  letI : Subsingleton (TwoIndex p) :=
    ⟨fun i j ↦ Subtype.ext
      (hinj (i.2.trans j.2.symm))⟩
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

omit [NeZero r] in
/-- If all involutions in a finite `2`-group are central and the center
acts fixed-point-freely, then the whole group acts fixed-point-freely. -/
private theorem fixedPointFreeOffZero_of_allInvolutionsCentral
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hP : IsPGroup 2 P)
    (hcentral : AllInvolutionsCentral P)
    (C : CenterFixedPointFreeAction r d P) :
    FixedPointFreeOffZero P := by
  intro b hbNe v hbFix
  by_contra hvNe
  have hbad :
      (v, (0 : Fin d → ZMod r)) ∈
        affineTwoBaseBadSet P
          (0 : Fin d → ZMod r) 0 := by
    let S : Subgroup P :=
        MulAction.stabilizer P v ⊓
          MulAction.stabilizer P
            (0 : Fin d → ZMod r)
    have hinter : S ≠ ⊥ := by
      apply Subgroup.ne_bot_iff_exists_ne_one.mpr
      let bS : S :=
        ⟨b,
          MulAction.mem_stabilizer_iff.mpr hbFix,
          MulAction.mem_stabilizer_iff.mpr (by simp)⟩
      refine ⟨bS, ?_⟩
      intro hbSOne
      apply hbNe
      exact congrArg Subtype.val hbSOne
    simpa [S, affineTwoBaseBadSet] using hinter
  obtain ⟨g, hgOrder, hgFix, _hgZero⟩ :=
    (mem_affineTwoBaseBadSet_iff_exists_primeOrder_fixed
      P hP 0 0 (v, (0 : Fin d → ZMod r))).mp hbad
  let z : Subgroup.center P :=
    ⟨g, hcentral g hgOrder⟩
  have hzNe : z ≠ 1 := by
    intro hz
    have hgOne : g = 1 :=
      congrArg
        (fun w : Subgroup.center P => w.1) hz
    rw [hgOne, orderOf_one] at hgOrder
    omega
  apply hvNe
  apply C.fixedPointFree z hzNe v
  change g.1.1 v = v
  change g.1.1 (v + 0) = v + 0 at hgFix
  simpa using hgFix

/-- A generalized-quaternion mapped `2`-core supplies the complete exact
two-orbit reserve datum. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_generalizedQuaternion
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (n : ℕ) (hn : 0 < n)
    (e :
      (generalizedQuaternionJointMappedCore (K := K) 2) ≃*
        QuaternionGroup n) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  let P := generalizedQuaternionJointMappedCore (K := K) 2
  let D₂ :=
    (nonregularVectors
      (diagonalMappedCore (K := K) 2)).ncard
  let C₂ :=
    Nat.card (diagonalMappedCore (K := K) 2)
  let N := r ^ d
  let F := mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  have hcentral : AllInvolutionsCentral P :=
    (quaternionGroup_allInvolutionsCentral n).of_mulEquiv e
  have hfp : FixedPointFreeOffZero P :=
    fixedPointFreeOffZero_of_allInvolutionsCentral
      P F.pGroup hcentral F.centerFixedPointFree
  have hactive :
      activePrimeOrderElements 2 P = ∅ :=
    activePrimeOrderElements_two_eq_empty_of_quaternion
      P e F.centerFixedPointFree
  have hhalf :
      TwoCoreSymplecticTypeHalfDensityData K := by
    constructor
    · change
        2 * (activePrimeOrderElements 2 P).card ≤
          r ^ d - 1
      rw [hactive]
      simp
    · intro g hg
      change g ∈ activePrimeOrderElements 2 P at hg
      rw [hactive] at hg
      simp at hg
  have hD₂ : D₂ ≤ 1 := by
    dsimp only [D₂]
    rw [ncard_nonregular_diagonalMappedCore_eq_affineBadSet]
    have hbad :=
      ncard_affineTwoBaseBadSet_le_nonregular_sq P 0 0
    have hsource :=
      ncard_nonregularVectors_le_one_of_fixedPointFreeOffZero P hfp
    exact hbad.trans (by nlinarith)
  have hNthree : 3 ≤ N := by
    have hrThree : 3 ≤ r := by
      have hrGeTwo := (Fact.out : r.Prime).two_le
      omega
    calc
      3 ≤ r := hrThree
      _ = r ^ 1 := by simp
      _ ≤ r ^ d :=
        Nat.pow_le_pow_right (Fact.out : r.Prime).pos hd
      _ = N := rfl
  have hpredPos : 0 < N - 1 := by omega
  have hcardP : Nat.card P ≤ N - 1 := by
    have hdvd :
        Nat.card P ∣ N - 1 := by
      simpa [N, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using
        natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero P hfp
    exact Nat.le_of_dvd hpredPos hdvd
  have hcardMap : C₂ = Nat.card P := by
    change
      Nat.card
          (P.map
            (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))) =
        Nat.card P
    exact
      Subgroup.card_map_of_injective
        (K := P)
        (diagonalGeneralLinearHom_injective
          (ZMod r) (Fin d → ZMod r))
  have hC₂ : C₂ ≤ N - 1 := by
    rw [hcardMap]
    exact hcardP
  refine
    { halfDensity := hhalf
      distinguishedTwo := ?_ }
  intro I _ p hp hinj hcross _i₂ _hi₂
  let f : I → ℕ := fun i ↦
    (nonregularVectors
      (diagonalMappedCore (K := K) (p i))).ncard
  let T := TwoIndex p
  let O := OddIndex p
  let pO : O → ℕ := fun i ↦ p i.1
  let Bodd := ∑ i : O, f i.1
  have hodd :
      2 * Bodd ≤ N * (N - 1) := by
    have h :=
      OddPrimeDiagonalReserve.two_mul_sum_diagonal_bad_le_fieldCard_mul_pred_of_quasiprimitive
          (K := K) hrTwo hd
          (p := pO)
          (fun i ↦ hp i.1)
          (fun i ↦ i.2)
          (fun i ↦ hcross i.1)
          (fun _i _j hij ↦ Subtype.ext (hinj hij))
          hqp
    simpa [Bodd, f, O, pO, N,
      diagonalMappedCore, generalizedQuaternionJointMappedCore] using h
  have htwoSum : (∑ i : T, f i.1) ≤ D₂ := by
    have hterm : ∀ i : T, f i.1 = D₂ := by
      intro i
      dsimp only [f, D₂]
      simp [i.2]
    calc
      (∑ i : T, f i.1) =
          Fintype.card T * D₂ := by
        simp_rw [hterm]
        simp
      _ ≤ 1 * D₂ :=
        Nat.mul_le_mul_right D₂
          (by
            simpa [T] using card_twoIndex_le_one p hinj)
      _ = D₂ := one_mul D₂
  have hsplit :
      (∑ i, f i) =
        (∑ i : T, f i.1) + Bodd := by
    exact sum_eq_sum_twoIndex_add_oddIndex p f
  have hsum :
      (∑ i, f i) ≤ D₂ + Bodd := by
    rw [hsplit]
    exact Nat.add_le_add_right htwoSum Bodd
  have hjoint :
      D₂ + Bodd + 2 * C₂ < N * N := by
    have hDdouble : 2 * D₂ ≤ 2 :=
      Nat.mul_le_mul_left 2 hD₂
    have hCdouble : 4 * C₂ ≤ 4 * (N - 1) :=
      Nat.mul_le_mul_left 4 hC₂
    have hNpred : N - 1 + 1 = N := by omega
    have hpoly :
        2 + N * (N - 1) + 4 * (N - 1) <
          2 * (N * N) := by
      nlinarith
    have hdouble :
        2 * (D₂ + Bodd + 2 * C₂) < 2 * (N * N) := by
      calc
        2 * (D₂ + Bodd + 2 * C₂) =
            2 * D₂ + 2 * Bodd + 4 * C₂ := by ring
        _ ≤ 2 + N * (N - 1) + 4 * (N - 1) := by omega
        _ < 2 * (N * N) := hpoly
    omega
  have htop : r ^ (2 * d) = N * N := by
    dsimp only [N]
    rw [← pow_add]
    congr 1
    omega
  rw [htop]
  change (∑ i, f i) + 2 * C₂ < N * N
  exact (Nat.add_le_add_right hsum (2 * C₂)).trans_lt hjoint

end LisiSabatini
