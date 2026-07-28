module

public import LisiSabatini.OddCharacteristicTwoCoreTwoOrbitReserve
public import LisiSabatini.TwoCoreDistinguishedJointBudgetArithmetic

/-!
# The full distinguished-two budget for a semidihedral normal core

For a semidihedral core with parameter `k`, the group order is `16*k`,
there are at most `4*k` active involutions, and its cyclic rotation
subgroup has order `8*k`.  The rotation subgroup is free away from zero,
so `8*k ∣ r^d-1`.

If the quotient is at least two, these exact shape constants close the
joint budget together with the existing coarse odd-row estimate.  If the
quotient is one, every active odd prime core would force an odd prime
divisor of `r^d-1 = 8*k`; this is impossible because `16*k` is the order
of a `2`-group.  Hence all odd rows vanish in the boundary case.
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

local instance fintypeConcreteLinearSubgroupForSemidihedralJointBudget
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin e → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P (finite_linearSubgroup_of_finite P)

abbrev semidihedralJointMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
  (pCore q K).map K.subtype

private abbrev diagonalMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r)
        ((Fin d → ZMod r) × (Fin d → ZMod r))) :=
  (semidihedralJointMappedCore (K := K) q).map
    (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))

omit [NeZero r] in
private theorem ncard_nonregular_diagonalMappedCore_eq_affineBadSet
    (q : ℕ) :
    (nonregularVectors
      (diagonalMappedCore (K := K) q)).ncard =
      (affineTwoBaseBadSet
        (semidihedralJointMappedCore (K := K) q) 0 0).ncard := by
  congr 1
  ext z
  simpa using
    (mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
      (semidihedralJointMappedCore (K := K) q) 0 0 z).symm

private theorem sum_eq_sum_twoIndex_add_oddIndex
    {I : Type uI} [Fintype I] (p : I → ℕ) (f : I → ℕ) :
    (∑ i, f i) =
      (∑ i : {i : I // p i = 2}, f i.1) +
        ∑ i : {i : I // p i ≠ 2}, f i.1 := by
  classical
  simpa using
    (Fintype.sum_subtype_add_sum_subtype
      (fun i ↦ p i = 2) f).symm

/-- A semidihedral presentation with parameter `k` has order `16*k`. -/
theorem natCard_eq_sixteen_mul_of_semidihedralPresentation
    {P : Type*} [Group P] [Finite P]
    {k : ℕ}
    (hk : 0 < k)
    (presentation : IsSemidihedralPresentation P k) :
    Nat.card P = 16 * k := by
  letI : NeZero (8 * k) := ⟨mul_ne_zero (by norm_num) hk.ne'⟩
  letI : NeZero (k * 8) := ⟨mul_ne_zero hk.ne' (by norm_num)⟩
  calc
    Nat.card P =
        Nat.card (ZMod (8 * k) ⊕ ZMod (8 * k)) :=
      Nat.card_congr presentation.normalForm.symm
    _ = 16 * k := by
      simp only [Nat.card_sum, Nat.card_zmod]
      ring

/-- The semidihedral shape closes the exact two-orbit reserve, including
the distinguished-`2` row. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_semidihedral
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (k : ℕ) (hk : 0 < k)
    (presentation :
      IsSemidihedralPresentation
        (semidihedralJointMappedCore (K := K) 2) k) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  let P := semidihedralJointMappedCore (K := K) 2
  let D := fun q ↦ diagonalMappedCore (K := K) q
  let q := r ^ d
  let F := mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  let head : BergerMaximalClassHead P :=
    .semidihedral k hk presentation
  have hhalf :
      TwoCoreSymplecticTypeHalfDensityData K :=
    twoCoreSymplecticTypeHalfDensityData_of_semidihedral
      hrTwo hd hqp k hk presentation
  refine ⟨hhalf, ?_⟩
  intro I _ p hp hinj hcross i₂ hi₂
  classical
  let row : I → ℕ := fun i ↦
    (nonregularVectors (D (p i))).ncard
  let B :=
    (nonregularVectors (D 2)).ncard
  let C := Nat.card (D 2)
  let O := {i : I // p i ≠ 2}
  let pO : O → ℕ := fun i ↦ p i.1
  have hqThree : 3 ≤ q := by
    dsimp only [q]
    have hrThree : 3 ≤ r := by
      have hrGeTwo := (Fact.out : r.Prime).two_le
      omega
    calc
      3 ≤ r := hrThree
      _ = r ^ 1 := by simp
      _ ≤ r ^ d :=
        Nat.pow_le_pow_right (Fact.out : r.Prime).pos hd
  have hcardP : Nat.card P = 16 * k := by
    exact
      natCard_eq_sixteen_mul_of_semidihedralPresentation hk presentation
  have hcardD : C = 16 * k := by
    change Nat.card (D 2) = 16 * k
    calc
      Nat.card (D 2) = Nat.card P := by
        exact
          Subgroup.card_map_of_injective
            (K := P)
            (diagonalGeneralLinearHom_injective
              (ZMod r) (Fin d → ZMod r))
      _ = 16 * k := hcardP
  have hactive :
      (activePrimeOrderElements 2 P).card ≤ 4 * k :=
    card_activePrimeOrderElements_two_le_of_semidihedral
      hk P presentation F.centerFixedPointFree
  have hfixed :
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤ q := by
    exact hhalf.2
  have hbad :
      B ≤ 1 + 4 * k * (q - 1) := by
    dsimp only [B, D]
    rw [ncard_nonregular_diagonalMappedCore_eq_affineBadSet]
    exact
      ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
        P F.pGroup (4 * k) q hactive hfixed
  have hrotation :
      8 * k ∣ q - 1 := by
    simpa [head, BergerMaximalClassHead.rotationOrder, q] using
      head.rotationOrder_dvd_nonzero
        P F.pGroup hrTwo F.centerFixedPointFree
  obtain ⟨t, ht⟩ := hrotation
  have hqEq : q = 8 * k * t + 1 := by
    have hqPos : 0 < q := by omega
    omega
  have htPos : 0 < t := by
    by_contra htZero
    have : t = 0 := Nat.eq_zero_of_not_pos htZero
    rw [this] at hqEq
    omega
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
  by_cases htOne : t = 1
  · have hqBoundary : q = 8 * k + 1 := by
      rw [hqEq, htOne]
      ring
    let R :
        PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K pO :=
      PrimeCoreMixedCyclicCenterFullSchurFamilyRows.ofQuasiprimitive
        (fun i ↦ hp i.1)
        (fun i ↦ hcross i.1)
        hqp
        (fun i hne hnoncomm ↦ by
          let hA : IsAdmissibleNoncommutingPrimeCore r d (pO i) K :=
            ⟨hp i.1, i.2, hcross i.1, hne, hnoncomm⟩
          exact
            mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
              (Fact.out : Nat.Prime r) hqp hA
              (mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
                (Fact.out : Nat.Prime r) hqp hA))
    have hoddBot :
        ∀ i : O, semidihedralJointMappedCore (K := K) (pO i) = ⊥ := by
      intro i
      let Q := semidihedralJointMappedCore (K := K) (pO i)
      by_contra hQ
      have hpDvd : pO i ∣ q - 1 := by
        by_cases hcomm : IsCommutingPrimeCore (pO i) K
        · have hdiv :=
            prime_dvd_natCard_sub_one_of_nontrivial_pGroup_fixedPointFreeOffZero
              (hp i.1) Q hQ
              ((pCore_isPGroup (pO i) K).map K.subtype)
              (R.commutative_fixedPointFree i hQ hcomm)
          simpa [Q, pO, q, Nat.card_fun, Nat.card_fin,
            Nat.card_zmod] using hdiv
        · exact
            R.prime_dvd_fieldCard_sub_one_of_noncommutative
              i hQ hcomm
      have hpDvdEightK : pO i ∣ 8 * k := by
        simpa [hqBoundary] using hpDvd
      have hpDvdCardP : pO i ∣ Nat.card P := by
        rw [hcardP]
        exact hpDvdEightK.trans (by
          refine ⟨2, ?_⟩
          ring)
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp F.pGroup
      have hpDvdPow : pO i ∣ 2 ^ n := by
        rwa [hn] at hpDvdCardP
      have hpDvdTwo : pO i ∣ 2 :=
        (hp i.1).dvd_of_dvd_pow hpDvdPow
      have hpEqTwo : pO i = 2 :=
        (Nat.prime_dvd_prime_iff_eq (hp i.1) Nat.prime_two).mp
          hpDvdTwo
      exact i.2 hpEqTwo
    have hoddZero :
        (∑ i : O, row i.1) = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      have hdiagBot : D (pO i) = ⊥ := by
        simp [D, diagonalMappedCore, semidihedralJointMappedCore, hoddBot i]
      dsimp only [row, pO]
      rw [hdiagBot, nonregularVectors_bot, Set.ncard_empty]
    have hown :
        B + 2 * (16 * k) < q * q :=
      semidihedral_twoCoreEnvelope_add_twoOrbits_lt_of_rotationQuotient_one
        hk hqBoundary hbad
    change (∑ i, row i) + 2 * C < r ^ (2 * d)
    rw [hsplit, hoddZero, add_zero, hcardD]
    have htop : r ^ (2 * d) = q * q := by
      dsimp only [q]
      rw [← pow_add]
      congr 1
      omega
    rw [htop]
    exact hown
  · have htTwo : 2 ≤ t := by omega
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
      simpa [row, D, pO, q, diagonalMappedCore, semidihedralJointMappedCore] using h
    have hbudget :
        DistinguishedTwoCoreJointEnvelopeBudget
          q (4 * k) (16 * k) :=
      semidihedral_jointEnvelopeBudget_of_rotationQuotient_ge_two
        hk htTwo hqEq
    have hjoint :
        B + (∑ i : O, row i.1) + 2 * (16 * k) < q * q :=
      distinguishedTwo_joint_lt_of_envelopeBudget
        hodd hbad hbudget
    change (∑ i, row i) + 2 * C < r ^ (2 * d)
    rw [hsplit, hcardD]
    have htop : r ^ (2 * d) = q * q := by
      dsimp only [q]
      rw [← pow_add]
      congr 1
      omega
    rw [htop]
    exact hjoint

end LisiSabatini
