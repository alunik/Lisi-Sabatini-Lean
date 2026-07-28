module

public import LisiSabatini.OddCharacteristicTwoCoreTwoOrbitReserve
public import LisiSabatini.TwoCoreCentralCommutatorJointBudgetArithmetic

/-!
# The full distinguished-two budget for a central-commutator core

Write

* `Q = |P/Z(P)|`,
* `Z = |Z(P)|`, and
* `q = r^d`.

The Hall central-coset count gives at most `2(Q-1)` active involutions,
the operator comparison gives `Q ≤ d²`, and the fixed-point-free center
gives `Z ∣ q-1`.  These estimates close the exact joint budget outside
three small modules.

The small modules use the divisibility rather than the weaker inequality
`Z ≤ q-1`: one gets `Z ≤ 8` over `F₅²` and `Z ≤ 16` over `F₃⁴`.
Over `F₃²`, the existing sharp Hall theorem gives `|P| ≤ 8` and at most
four active involutions; every odd row vanishes because its prime would
have to divide `q-1 = 8`.
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

local instance fintypeConcreteLinearSubgroupForCentralJointBudget
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin e → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P (finite_linearSubgroup_of_finite P)

abbrev centralCommutatorJointMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
  (pCore q K).map K.subtype

private abbrev diagonalMappedCore (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r)
        ((Fin d → ZMod r) × (Fin d → ZMod r))) :=
  (centralCommutatorJointMappedCore (K := K) q).map
    (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))

omit [NeZero r] in
private theorem ncard_nonregular_diagonalMappedCore_eq_affineBadSet
    (q : ℕ) :
    (nonregularVectors
      (diagonalMappedCore (K := K) q)).ncard =
      (affineTwoBaseBadSet
        (centralCommutatorJointMappedCore (K := K) q) 0 0).ncard := by
  congr 1
  ext z
  simpa using
    (mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
      (centralCommutatorJointMappedCore (K := K) q) 0 0 z).symm

private theorem sum_eq_sum_twoIndex_add_oddIndex
    {I : Type uI} [Fintype I] (p : I → ℕ) (f : I → ℕ) :
    (∑ i, f i) =
      (∑ i : {i : I // p i = 2}, f i.1) +
        ∑ i : {i : I // p i ≠ 2}, f i.1 := by
  classical
  simpa using
    (Fintype.sum_subtype_add_sum_subtype
      (fun i ↦ p i = 2) f).symm

/-- A group-level active-count and order envelope satisfying the exact
arithmetic budget supplies the full reserve datum. -/
private theorem reserveData_of_jointEnvelopeBudget
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hhalf : TwoCoreSymplecticTypeHalfDensityData K)
    (activeBound coreOrderBound : ℕ)
    (hactive :
      (activePrimeOrderElements 2
        (centralCommutatorJointMappedCore (K := K) 2)).card ≤ activeBound)
    (hcore :
      Nat.card (diagonalMappedCore (K := K) 2) ≤
        coreOrderBound)
    (hbudget :
      DistinguishedTwoCoreJointEnvelopeBudget
        (r ^ d) activeBound coreOrderBound) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  let P := centralCommutatorJointMappedCore (K := K) 2
  let D := fun q ↦ diagonalMappedCore (K := K) q
  let q := r ^ d
  let F := mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  refine ⟨hhalf, ?_⟩
  intro I _ p hp hinj hcross i₂ hi₂
  classical
  let row : I → ℕ := fun i ↦
    (nonregularVectors (D (p i))).ncard
  let B := (nonregularVectors (D 2)).ncard
  let O := {i : I // p i ≠ 2}
  let pO : O → ℕ := fun i ↦ p i.1
  have hfixed :
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤ q := by
    exact hhalf.2
  have hbad :
      B ≤ 1 + activeBound * (q - 1) := by
    dsimp only [B, D]
    rw [ncard_nonregular_diagonalMappedCore_eq_affineBadSet]
    exact
      ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
        P F.pGroup activeBound q hactive hfixed
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
    simpa [row, D, pO, q, diagonalMappedCore, centralCommutatorJointMappedCore] using h
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
      B + (∑ i : O, row i.1) + 2 * coreOrderBound <
        q * q :=
    distinguishedTwo_joint_lt_of_envelopeBudget
      hodd hbad (by simpa [q] using hbudget)
  change
    (∑ i, row i) +
        2 * Nat.card (D 2) <
      r ^ (2 * d)
  rw [hsplit]
  have hleft :
      B + (∑ i : O, row i.1) +
          2 * Nat.card (D 2) ≤
        B + (∑ i : O, row i.1) +
          2 * coreOrderBound :=
    Nat.add_le_add_left
      (Nat.mul_le_mul_left 2 hcore)
      (B + ∑ i : O, row i.1)
  have htop : r ^ (2 * d) = q * q := by
    dsimp only [q]
    rw [← pow_add]
    congr 1
    omega
  rw [htop]
  exact hleft.trans_lt hjoint

/-- A power of two dividing `24` is at most `8`. -/
private theorem powerOfTwo_le_eight_of_dvd_twentyFour
    {z : ℕ}
    (hpow : ∃ n, z = 2 ^ n)
    (hdiv : z ∣ 24) :
    z ≤ 8 := by
  obtain ⟨n, rfl⟩ := hpow
  have hn : n ≤ 3 := by
    by_contra hn
    have hfour : 4 ≤ n := by omega
    have hbad : 2 ^ 4 ∣ 24 :=
      (Nat.pow_dvd_pow 2 hfour).trans hdiv
    norm_num at hbad
  simpa using
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hn)

/-- A power of two dividing `80` is at most `16`. -/
private theorem powerOfTwo_le_sixteen_of_dvd_eighty
    {z : ℕ}
    (hpow : ∃ n, z = 2 ^ n)
    (hdiv : z ∣ 80) :
    z ≤ 16 := by
  obtain ⟨n, rfl⟩ := hpow
  have hn : n ≤ 4 := by
    by_contra hn
    have hfive : 5 ≤ n := by omega
    have hbad : 2 ^ 5 ∣ 80 :=
      (Nat.pow_dvd_pow 2 hfive).trans hdiv
    norm_num at hbad
  simpa using
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hn)

set_option synthInstance.maxHeartbeats 100000 in
-- The center, its quotient, and the diagonal image create three nested
-- finite subgroup instances in the exceptional-module branches.
set_option maxHeartbeats 1000000 in
-- The single theorem deliberately keeps the generic and three exceptional
-- budgets together so that every branch returns the same exact reserve datum.
/-- The central-commutator Hall--Berger shape closes the exact
distinguished-two reserve in every odd-characteristic module. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_centralCommutator
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcomm :
      HasCentralCommutatorOfOrderTwo
        (centralCommutatorJointMappedCore (K := K) 2)) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  let P := centralCommutatorJointMappedCore (K := K) 2
  let D := fun q ↦ diagonalMappedCore (K := K) q
  let q := r ^ d
  let F := mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  let Q := Nat.card (P ⧸ Subgroup.center P)
  let Z := Nat.card (Subgroup.center P)
  letI : Nonempty P := ⟨1⟩
  letI : Nonempty (Subgroup.center P) := ⟨1⟩
  letI : Nonempty (D 2) := ⟨1⟩
  have hhalf :
      TwoCoreSymplecticTypeHalfDensityData K :=
    twoCoreSymplecticTypeHalfDensityData_of_centralCommutator
      hrTwo hd hqp hcomm
  have hactive :
      (activePrimeOrderElements 2 P).card ≤
        2 * (Q - 1) := by
    exact
      card_activePrimeOrderElements_two_le_two_mul_quotientCenter_pred_of_hall
        P hcomm F.hall F.centerFixedPointFree
  have hquotient : Q ≤ d * d := by
    exact
      natCard_quotientCenter_le_dimension_sq_of_centralCommutator
        hrTwo hd P hcomm F.centerFixedPointFree
  have hdeven : Even d :=
    even_dimension_of_centralCommutator
      hrTwo P hcomm F.centerFixedPointFree
  have hcardP : Nat.card P = Q * Z := by
    simpa [Q, Z] using
      (Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center P))
  have hcardD :
      Nat.card (D 2) = Q * Z := by
    calc
      Nat.card (D 2) = Nat.card P := by
        exact
          Subgroup.card_map_of_injective
            (K := P)
            (diagonalGeneralLinearHom_injective
              (ZMod r) (Fin d → ZMod r))
      _ = Q * Z := hcardP
  let Zlinear :
      Subgroup
        (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
    (Subgroup.center P).map P.subtype
  have hZlinearFixedPointFree :
      FixedPointFreeOffZero Zlinear := by
    intro z hz v hv
    obtain ⟨x, hxCenter, hxMap⟩ := z.2
    have hxNe : x ≠ 1 := by
      intro hx
      apply hz
      apply Subtype.ext
      simpa [hx, Zlinear] using hxMap.symm
    let xCenter : Subgroup.center P := ⟨x, hxCenter⟩
    have hxCenterNe : xCenter ≠ 1 := by
      intro h
      apply hxNe
      simpa [xCenter] using congrArg Subtype.val h
    apply F.centerFixedPointFree.fixedPointFree
      xCenter hxCenterNe v
    have hzval : z.1 = x.1 := by
      simpa [Zlinear] using hxMap.symm
    change z.1.toLinearEquiv v = v at hv
    rw [hzval] at hv
    simpa [xCenter] using hv
  have hcardZlinear : Nat.card Zlinear = Z := by
    dsimp only [Zlinear, Z]
    exact
      Subgroup.card_map_of_injective
        (K := Subgroup.center P) P.subtype_injective
  have hcenterDvd : Z ∣ q - 1 := by
    have hdiv :=
      natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero
        Zlinear hZlinearFixedPointFree
    rw [hcardZlinear] at hdiv
    simpa [q, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using hdiv
  have hcenterLe : Z ≤ q - 1 :=
    Nat.le_of_dvd (by
      have hqThree : 3 ≤ q := by
        dsimp only [q]
        have hrThree : 3 ≤ r := by
          have hrTwoLe := (Fact.out : r.Prime).two_le
          omega
        calc
          3 ≤ r := hrThree
          _ = r ^ 1 := by simp
          _ ≤ r ^ d :=
            Nat.pow_le_pow_right (Fact.out : r.Prime).pos hd
      omega) hcenterDvd
  have hcenterPower : ∃ n, Z = 2 ^ n := by
    exact
      IsPGroup.iff_card.mp
        (F.pGroup.to_subgroup (Subgroup.center P))
  by_cases h32 : r = 3 ∧ d = 2
  · obtain ⟨rfl, rfl⟩ := h32
    have hactiveFour :
        (activePrimeOrderElements 2 P).card ≤ 4 := by
      exact
        card_activePrimeOrderElements_two_le_four_of_centralCommutator_f3Plane
          P F.pGroup hcomm F.hall F.centerFixedPointFree
    have hcardPEight : Nat.card P ≤ 8 := by
      exact
        natCard_le_eight_of_centralCommutator_f3Plane
          P F.pGroup hcomm F.hall F.centerFixedPointFree
    refine ⟨hhalf, ?_⟩
    intro I _ p hp hinj hcross i₂ hi₂
    classical
    let row : I → ℕ := fun i ↦
      (nonregularVectors (D (p i))).ncard
    let B := (nonregularVectors (D 2)).ncard
    let O := {i : I // p i ≠ 2}
    let pO : O → ℕ := fun i ↦ p i.1
    have hfixed :
        ∀ g ∈ activePrimeOrderElements 2 P,
          (fixedVectorSet g.1).ncard *
              (fixedVectorSet g.1).ncard ≤ 9 := by
      intro g hg
      have h :=
        activeInvolution_fixedVectorSet_sq_le_of_centralCommutator
          (by norm_num : Even 2)
          P hcomm F.centerFixedPointFree g hg
      norm_num at h ⊢
      exact h
    have hbad : B ≤ 33 := by
      dsimp only [B, D]
      rw [ncard_nonregular_diagonalMappedCore_eq_affineBadSet]
      simpa using
        ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
          P F.pGroup 4 9 hactiveFour hfixed
    let R :
        PrimeCoreMixedCyclicCenterFullSchurFamilyRows 3 2 K pO :=
      PrimeCoreMixedCyclicCenterFullSchurFamilyRows.ofQuasiprimitive
        (fun i ↦ hp i.1)
        (fun i ↦ hcross i.1)
        hqp
        (fun i hne hnoncomm ↦ by
          let hA : IsAdmissibleNoncommutingPrimeCore 3 2 (pO i) K :=
            ⟨hp i.1, i.2, hcross i.1, hne, hnoncomm⟩
          exact
            mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
              (Fact.out : Nat.Prime 3) hqp hA
              (mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
                (Fact.out : Nat.Prime 3) hqp hA))
    have hoddBot :
        ∀ i : O, centralCommutatorJointMappedCore (K := K) (pO i) = ⊥ := by
      intro i
      let S := centralCommutatorJointMappedCore (K := K) (pO i)
      by_contra hS
      have hpDvd : pO i ∣ 8 := by
        have hpDvdField : pO i ∣ 3 ^ 2 - 1 := by
          by_cases hcommuting : IsCommutingPrimeCore (pO i) K
          · have hdiv :=
              prime_dvd_natCard_sub_one_of_nontrivial_pGroup_fixedPointFreeOffZero
                (hp i.1) S hS
                ((pCore_isPGroup (pO i) K).map K.subtype)
                (R.commutative_fixedPointFree i hS hcommuting)
            simpa [S, pO, Nat.card_fun, Nat.card_fin,
              Nat.card_zmod] using hdiv
          · exact
              R.prime_dvd_fieldCard_sub_one_of_noncommutative
                i hS hcommuting
        norm_num at hpDvdField
        exact hpDvdField
      have hpDvdTwoPower : pO i ∣ 2 ^ 3 := by
        simpa using hpDvd
      have hpDvdTwo : pO i ∣ 2 :=
        (hp i.1).dvd_of_dvd_pow hpDvdTwoPower
      have hpEqTwo : pO i = 2 :=
        (Nat.prime_dvd_prime_iff_eq
          (hp i.1) Nat.prime_two).mp hpDvdTwo
      exact i.2 hpEqTwo
    have hoddZero :
        (∑ i : O, row i.1) = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      have hdiagBot : D (pO i) = ⊥ := by
        simp [D, diagonalMappedCore, centralCommutatorJointMappedCore, hoddBot i]
      dsimp only [row, pO]
      rw [hdiagBot, nonregularVectors_bot, Set.ncard_empty]
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
    have hcardDEight : Nat.card (D 2) ≤ 8 := by
      have hmap : Nat.card (D 2) = Nat.card P :=
        Subgroup.card_map_of_injective
          (K := P)
          (diagonalGeneralLinearHom_injective
            (ZMod 3) (Fin 2 → ZMod 3))
      rw [hmap]
      exact hcardPEight
    change (∑ i, row i) + 2 * Nat.card (D 2) < 3 ^ (2 * 2)
    rw [hsplit, hoddZero, add_zero]
    norm_num
    omega
  · by_cases h52 : r = 5 ∧ d = 2
    · obtain ⟨rfl, rfl⟩ := h52
      have hZd : Z ∣ 24 := by
        simpa [q] using hcenterDvd
      have hZle : Z ≤ 8 :=
        powerOfTwo_le_eight_of_dvd_twentyFour hcenterPower hZd
      have hQle : Q ≤ 4 := by
        simpa using hquotient
      have hactiveSix :
          (activePrimeOrderElements 2 P).card ≤ 6 :=
        hactive.trans (by omega)
      have hcoreThirtyTwo :
          Nat.card (D 2) ≤ 32 := by
        rw [hcardD]
        nlinarith
      apply
        reserveData_of_jointEnvelopeBudget
          (K := K)
          (by norm_num : (5 : ℕ) ≠ 2)
          (by norm_num : 0 < 2)
          hqp hhalf 6 32 hactiveSix hcoreThirtyTwo
      norm_num [DistinguishedTwoCoreJointEnvelopeBudget]
    · by_cases h34 : r = 3 ∧ d = 4
      · obtain ⟨rfl, rfl⟩ := h34
        have hZd : Z ∣ 80 := by
          simpa [q] using hcenterDvd
        have hZle : Z ≤ 16 :=
          powerOfTwo_le_sixteen_of_dvd_eighty hcenterPower hZd
        have hQle : Q ≤ 16 := by
          simpa using hquotient
        have hactiveThirty :
            (activePrimeOrderElements 2 P).card ≤ 30 :=
          hactive.trans (by omega)
        have hcoreTwoFiftySix :
            Nat.card (D 2) ≤ 256 := by
          rw [hcardD]
          nlinarith
        apply
          reserveData_of_jointEnvelopeBudget
            (K := K)
            (by norm_num : (3 : ℕ) ≠ 2)
            (by norm_num : 0 < 4)
            hqp hhalf 30 256 hactiveThirty hcoreTwoFiftySix
        norm_num [DistinguishedTwoCoreJointEnvelopeBudget]
      · have hsmall :
            (r ≠ 3 ∨ d ≠ 2) ∧
            (r ≠ 5 ∨ d ≠ 2) ∧
            (r ≠ 3 ∨ d ≠ 4) := by
          refine ⟨?_, ?_, ?_⟩
          · by_cases hr : r = 3
            · exact Or.inr (fun hdTwo ↦ h32 ⟨hr, hdTwo⟩)
            · exact Or.inl hr
          · by_cases hr : r = 5
            · exact Or.inr (fun hdTwo ↦ h52 ⟨hr, hdTwo⟩)
            · exact Or.inl hr
          · by_cases hr : r = 3
            · exact Or.inr (fun hdFour ↦ h34 ⟨hr, hdFour⟩)
            · exact Or.inl hr
        have hdimension :
            8 * d * d < q + 6 := by
          simpa [q] using
            eight_mul_dimension_sq_lt_field_pow_add_six
              hrTwo hd hdeven hsmall
        have hq : 1 < q := by
          have hrTwoLe := (Fact.out : r.Prime).two_le
          dsimp only [q]
          calc
            1 < r := (Fact.out : r.Prime).one_lt
            _ = r ^ 1 := by simp
            _ ≤ r ^ d :=
              Nat.pow_le_pow_right (Fact.out : r.Prime).pos hd
        have hbudget :
            DistinguishedTwoCoreJointEnvelopeBudget
              q (2 * (Q - 1)) (Q * Z) :=
          centralCommutator_jointEnvelopeBudget_of_dimension
            hq hquotient hcenterLe hdimension
        exact
          reserveData_of_jointEnvelopeBudget
            (K := K)
            hrTwo hd hqp hhalf
            (2 * (Q - 1)) (Q * Z)
            hactive hcardD.le
            (by simpa [q] using hbudget)

end LisiSabatini
