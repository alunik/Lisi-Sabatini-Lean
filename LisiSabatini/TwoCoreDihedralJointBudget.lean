module

public import LisiSabatini.OddCharacteristicTwoCoreTwoOrbitReserve
public import LisiSabatini.TwoCoreDistinguishedJointBudgetArithmetic

/-!
# The full distinguished-two budget for a dihedral normal core

For a dihedral core with parameter `k`, the group order is `8*k`,
there are at most `4*k` active involutions, and its cyclic rotation
subgroup has order `4*k`.  The rotation subgroup is free away from zero,
so `4*k ∣ r^d-1`.  The sharp pure-dihedral comparison strengthens this
to `2 * (4*k) ≤ r^d-1`.

Writing `r^d-1 = 4*k*t`, the standard joint envelope closes for `t ≥ 3`.
At the sole boundary `t = 2`, the field-cardinality predecessor equals
the order `8*k` of the dihedral `2`-group.  Every nontrivial odd prime
core would then force its prime to divide this power of two, so every odd
row vanishes.  The remaining dihedral bad locus and two full orbits fit
strictly.
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

local instance fintypeConcreteLinearSubgroupForDihedralJointBudget
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin e → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P (finite_linearSubgroup_of_finite P)

abbrev dihedralJointMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
  (pCore q K).map K.subtype

private abbrev diagonalMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r)
        ((Fin d → ZMod r) × (Fin d → ZMod r))) :=
  (dihedralJointMappedCore (K := K) q).map
    (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))

omit [NeZero r] in
private theorem ncard_nonregular_diagonalMappedCore_eq_affineBadSet
    (q : ℕ) :
    (nonregularVectors
      (diagonalMappedCore (K := K) q)).ncard =
      (affineTwoBaseBadSet
        (dihedralJointMappedCore (K := K) q) 0 0).ncard := by
  congr 1
  ext z
  simpa using
    (mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
      (dihedralJointMappedCore (K := K) q) 0 0 z).symm

private theorem sum_eq_sum_twoIndex_add_oddIndex
    {I : Type uI} [Fintype I] (p : I → ℕ) (f : I → ℕ) :
    (∑ i, f i) =
      (∑ i : {i : I // p i = 2}, f i.1) +
        ∑ i : {i : I // p i ≠ 2}, f i.1 := by
  classical
  simpa using
    (Fintype.sum_subtype_add_sum_subtype
      (fun i ↦ p i = 2) f).symm

/-- The coarse odd-row envelope closes for a dihedral core as soon as
the quotient `(q-1)/(4*k)` is at least three. -/
theorem dihedral_jointEnvelopeBudget_of_rotationQuotient_ge_three
    {q k t : ℕ}
    (hk : 0 < k)
    (ht : 3 ≤ t)
    (hq : q = 4 * k * t + 1) :
    DistinguishedTwoCoreJointEnvelopeBudget q (4 * k) (8 * k) := by
  subst q
  unfold DistinguishedTwoCoreJointEnvelopeBudget
  have hgap :
      32 * k <
        16 * k * k * t * (t - 2) + 12 * k * t := by
    calc
      32 * k < 36 * k :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) hk
      _ = 12 * k * 3 := by ring
      _ ≤ 12 * k * t :=
        Nat.mul_le_mul_left (12 * k) ht
      _ ≤ 16 * k * k * t * (t - 2) + 12 * k * t :=
        Nat.le_add_left _ _
  have hleft :
      2 * (1 + 4 * k * ((4 * k * t + 1) - 1)) +
          4 * (8 * k) =
        2 + 32 * k * k * t + 32 * k := by
    simp only [Nat.add_sub_cancel]
    ring
  have hright :
      (4 * k * t + 1) * (4 * k * t + 1 + 1) =
        2 + 32 * k * k * t +
          (16 * k * k * t * (t - 2) + 12 * k * t) := by
    have htEq : t = (t - 2) + 2 := by omega
    rw [htEq]
    simp only [Nat.add_sub_cancel]
    ring
  rw [hleft, hright]
  exact Nat.add_lt_add_left hgap (2 + 32 * k * k * t)

/-- At rotation quotient two, the dihedral `2`-core contribution itself
(bad locus plus two full orbits) fits strictly. -/
theorem dihedral_twoCoreEnvelope_add_twoOrbits_lt_of_rotationQuotient_two
    {q k twoBad : ℕ}
    (hk : 0 < k)
    (hq : q = 8 * k + 1)
    (htwo : twoBad ≤ 1 + 4 * k * (q - 1)) :
    twoBad + 2 * (8 * k) < q * q := by
  subst q
  have hsmall :
      32 * k * k < 64 * k * k := by
    exact
      Nat.mul_lt_mul_of_pos_right
        (Nat.mul_lt_mul_of_pos_right
          (by norm_num : 32 < 64) hk) hk
  calc
    twoBad + 2 * (8 * k) ≤
        (1 + 4 * k * (8 * k + 1 - 1)) + 2 * (8 * k) :=
      Nat.add_le_add_right htwo _
    _ = 1 + (32 * k * k + 16 * k) := by
      simp only [Nat.add_sub_cancel]
      ring
    _ < 1 + (64 * k * k + 16 * k) :=
      Nat.add_lt_add_left
        (Nat.add_lt_add_right hsmall (16 * k)) 1
    _ = (8 * k + 1) * (8 * k + 1) := by ring

/-- The dihedral shape closes the exact two-orbit reserve, including the
distinguished-`2` row and the `D₈` edge. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_dihedral
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (k : ℕ) (hk : 0 < k)
    (e :
      (dihedralJointMappedCore (K := K) 2) ≃*
        DihedralGroup (4 * k)) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  let P := dihedralJointMappedCore (K := K) 2
  let D := fun q ↦ diagonalMappedCore (K := K) q
  let q := r ^ d
  let F := mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  have hhalf :
      TwoCoreSymplecticTypeHalfDensityData K :=
    twoCoreSymplecticTypeHalfDensityData_of_dihedral
      hrTwo hd hqp k hk e
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
  have hcardP : Nat.card P = 8 * k := by
    calc
      Nat.card P =
          Nat.card (DihedralGroup (4 * k)) :=
        Nat.card_congr e.toEquiv
      _ = 2 * (4 * k) := DihedralGroup.nat_card
      _ = 8 * k := by ring
  have hcardD : C = 8 * k := by
    change Nat.card (D 2) = 8 * k
    calc
      Nat.card (D 2) = Nat.card P := by
        exact
          Subgroup.card_map_of_injective
            (K := P)
            (diagonalGeneralLinearHom_injective
              (ZMod r) (Fin d → ZMod r))
      _ = 8 * k := hcardP
  have hactive :
      (activePrimeOrderElements 2 P).card ≤ 4 * k :=
    card_activePrimeOrderElements_two_le_of_dihedral
      (by omega) P e F.centerFixedPointFree
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
      4 * k ∣ q - 1 := by
    simpa [q] using
      dihedral_rotationOrder_dvd_nonzero
        P F.pGroup hrTwo hd hk e F.centerFixedPointFree
  have hrotationTwo :
      2 * (4 * k) ≤ q - 1 := by
    simpa [q] using
      dihedral_rotationOrder_two_le_nonzero
        P F.pGroup hrTwo hd hk e F.centerFixedPointFree
  obtain ⟨t, ht⟩ := hrotation
  have hqEq : q = 4 * k * t + 1 := by
    have hqPos : 0 < q := by omega
    omega
  have htTwo : 2 ≤ t := by
    by_contra htNot
    have htCases : t = 0 ∨ t = 1 := by omega
    rcases htCases with rfl | rfl
    · simp at hqEq
      omega
    · simp at hqEq
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
  by_cases htBoundary : t = 2
  · have hqBoundary : q = 8 * k + 1 := by
      rw [hqEq, htBoundary]
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
        ∀ i : O, dihedralJointMappedCore (K := K) (pO i) = ⊥ := by
      intro i
      let Q := dihedralJointMappedCore (K := K) (pO i)
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
      have hpDvdCardP : pO i ∣ Nat.card P := by
        rw [hcardP]
        simpa [hqBoundary] using hpDvd
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
        simp [D, diagonalMappedCore, dihedralJointMappedCore, hoddBot i]
      dsimp only [row, pO]
      rw [hdiagBot, nonregularVectors_bot, Set.ncard_empty]
    have hown :
        B + 2 * (8 * k) < q * q :=
      dihedral_twoCoreEnvelope_add_twoOrbits_lt_of_rotationQuotient_two
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
  · have htThree : 3 ≤ t := by omega
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
      simpa [row, D, pO, q, diagonalMappedCore, dihedralJointMappedCore] using h
    have hbudget :
        DistinguishedTwoCoreJointEnvelopeBudget
          q (4 * k) (8 * k) :=
      dihedral_jointEnvelopeBudget_of_rotationQuotient_ge_three
        hk htThree hqEq
    have hjoint :
        B + (∑ i : O, row i.1) + 2 * (8 * k) < q * q :=
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
