module

public import LisiSabatini.AffineTwoBasePairSpectrumArithmetic
public import LisiSabatini.PrimitiveTopMixedPrimeCoreDominationCore
public import LisiSabatini.MappedPCoreFrattini
public import LisiSabatini.MappedPCoreCyclicCenterClassTwo
public import LisiSabatini.TwoCoreAffineTwoBaseHalfDensity

/-!
# Quasiprimitive affine CATB parity leaves

The direct pair-spectrum arithmetic closes the positive-dimensional
characteristic-two quasiprimitive leaf.  In odd characteristic, the mapped
normal two-core estimate is combined below with the exact remaining
odd-prime pair-spectrum arithmetic proposition.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uI

namespace QuasiprimitiveAffineParityCATB

variable {r d : ℕ} [Fact r.Prime] [NeZero r]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
variable {I : Type uI} [Fintype I] {p : I → ℕ}

local instance finiteConcreteLinearSubgroup
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin e → ZMod s))) :
    Finite P :=
  finite_linearSubgroup_of_finite P

abbrev NoncommutingIndex
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : I → ℕ) : Type uI :=
  {i : I //
    (pCore (p i) K).map K.subtype ≠ ⊥ ∧
      ¬ IsCommutingPrimeCore (p i) K}

abbrev CommutingIndex
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : I → ℕ) : Type uI :=
  {i : I //
    (pCore (p i) K).map K.subtype ≠ ⊥ ∧
      IsCommutingPrimeCore (p i) K}

private noncomputable instance
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : I → ℕ) :
    Fintype (NoncommutingIndex K p) :=
  Fintype.ofFinite _

private noncomputable instance
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : I → ℕ) :
    Fintype (CommutingIndex K p) :=
  Fintype.ofFinite _

/-- The direct pair-spectrum row attached to a mixed structural family.
Trivial cores contribute zero, active commuting cores contribute one, and
active noncommuting cores contribute the cyclic-center rectangle bound. -/
noncomputable def pairSpectrumWeight
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (i : I) : ℕ := by
  classical
  let P := (pCore (p i) K).map K.subtype
  exact if P = ⊥ then 0
    else if IsCommutingPrimeCore (p i) K then 1
    else
      1 + (p i ^ (2 * R.rank i + 1) - 1) *
        (r ^ (2 * (d / p i)) - 1)

/-- Every mapped prime core is bounded by its direct pair-spectrum row. -/
theorem ncard_affineTwoBaseBadSet_zero_le_pairSpectrumWeight
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (i : I) :
    (affineTwoBaseBadSet
      ((pCore (p i) K).map K.subtype) 0 0).ncard ≤
        pairSpectrumWeight R i := by
  classical
  let P := (pCore (p i) K).map K.subtype
  by_cases hbot : P = ⊥
  · change (affineTwoBaseBadSet P 0 0).ncard ≤ _
    have hempty : affineTwoBaseBadSet P 0 0 = ∅ := by
      rw [hbot]
      ext z
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hz
      apply hz
      apply le_antisymm
      · intro g _hg
        simpa using Subsingleton.elim g 1
      · exact bot_le
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le _
  · by_cases hcomm : IsCommutingPrimeCore (p i) K
    · have hnonregular :=
        R.ncard_nonregularVectors_le_spectrumWeight i
      have hbad :=
        ncard_affineTwoBaseBadSet_le_nonregular_sq P 0 0
      have hweight : R.spectrumWeight i = 1 := by
        simp [PrimeCoreMixedCyclicCenterFullSchurFamilyRows.spectrumWeight,
          P, hbot, hcomm]
      rw [hweight] at hnonregular
      simpa [pairSpectrumWeight, P, hbot, hcomm] using
        hbad.trans (Nat.mul_le_mul hnonregular hnonregular)
    · have hrow :=
        ncard_affineTwoBaseBadSet_zero_le_cyclicCenter_pairSpectrum
          P (R.cyclicCenter i hbot hcomm)
            (R.centerFixedPointFree i hbot hcomm)
      rw [R.structuralRank_eq i hbot hcomm] at hrow
      simpa [pairSpectrumWeight, P, hbot, hcomm] using hrow

/-- The total direct pair-spectrum weight splits into the noncommuting rows
and one point for each active commuting core. -/
theorem sum_pairSpectrumWeight_eq_split
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p) :
    (∑ i, pairSpectrumWeight R i) =
      (∑ i : NoncommutingIndex (r := r) K p, (
        1 + (p (i : I) ^ (2 * R.rank (i : I) + 1) - 1) *
          (r ^ (2 * (d / p (i : I))) - 1))) +
        Fintype.card (CommutingIndex (r := r) K p) := by
  classical
  let P : I → Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
    fun i ↦ (pCore (p i) K).map K.subtype
  let B : I → ℕ := fun i ↦
    1 + (p i ^ (2 * R.rank i + 1) - 1) *
      (r ^ (2 * (d / p i)) - 1)
  have hsplit :
      (∑ i, pairSpectrumWeight R i) =
        (∑ i, if P i ≠ ⊥ ∧ ¬ IsCommutingPrimeCore (p i) K
          then B i else 0) +
        (∑ i, if P i ≠ ⊥ ∧ IsCommutingPrimeCore (p i) K
          then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    by_cases hbot : P i = ⊥
    · simp [pairSpectrumWeight, P, B, hbot]
    · by_cases hcomm : IsCommutingPrimeCore (p i) K <;>
        simp [pairSpectrumWeight, P, B, hbot, hcomm]
  rw [hsplit]
  congr 1
  · rw [← Finset.sum_filter]
    rw [← Finset.sum_subtype_eq_sum_filter]
    apply Finset.sum_congr (Finset.subtype_univ _)
    intro i _hi
    rfl
  · rw [← Finset.sum_filter]
    rw [← Finset.sum_subtype_eq_sum_filter]
    simp [CommutingIndex, P]

/-- In characteristic two, the noncommuting direct pair-spectrum rows
occupy strictly less than half of the doubled module. -/
theorem two_mul_noncommuting_pairSpectrumSum_lt_of_charTwo
    {K₂ : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 2) (Fin d → ZMod 2))}
    (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p)
    (hcross : ∀ i, p i ≠ 2)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows 2 d K₂ p) :
    2 * (∑ i : NoncommutingIndex (r := 2) K₂ p, (
      1 + (p (i : I) ^ (2 * R.rank (i : I) + 1) - 1) *
        (2 ^ (2 * (d / p (i : I))) - 1))) <
      2 ^ (2 * d) := by
  let A := NoncommutingIndex K₂ p
  let pA : A → ℕ := fun i ↦ p i.1
  let nA : A → ℕ := fun i ↦ R.rank i.1
  let aA : A → ℕ := fun i ↦ R.schurDegree i.1
  let bA : A → ℕ := fun i ↦ R.multiplicity i.1
  have hraw :=
    two_mul_odd_extraspecial_family_pairSpectrum_lt
      pA nA aA bA
      (fun i ↦ hp i.1)
      (fun i ↦ hcross i.1)
      (fun i j hij ↦ Subtype.ext (hinj hij))
      (fun i ↦ by
        dsimp only [nA]
        rw [← R.structuralRank_eq i.1 i.2.1 i.2.2]
        exact
          (R.cyclicCenter i.1 i.2.1 i.2.2)
            |>.cyclicCenterStructuralRank_pos)
      (fun i ↦ R.schurDegree_pos i.1 i.2.1 i.2.2)
      (fun i ↦ R.multiplicity_pos i.1 i.2.1 i.2.2)
      (fun i ↦ by
        let hP := R.cyclicCenter i.1 i.2.1 i.2.2
        exact
          (show p i.1 ∣ Nat.card (Subgroup.center
              ((pCore (p i.1) K₂).map K₂.subtype)) from by
            calc
              p i.1 = Nat.card (centerPrimeKernel (p i.1)
                  ((pCore (p i.1) K₂).map K₂.subtype)) :=
                hP.card_centerPrimeKernel.symm
              _ ∣ Nat.card (Subgroup.center
                  ((pCore (p i.1) K₂).map K₂.subtype)) :=
                Subgroup.card_dvd_of_le
                  (centerPrimeKernel_le_center (p i.1)
                    ((pCore (p i.1) K₂).map K₂.subtype)))
            |>.trans
              (R.center_card_dvd_field_pow_sub_one
                i.1 i.2.1 i.2.2))
      (fun i ↦ R.dimension_eq i.1 i.2.1 i.2.2)
  simpa [A, pA, nA, aA, bA] using hraw

/-- In positive dimension over `F₂`, there are at most `2^d` active
commuting prime-core labels. -/
theorem card_commutingIndex_le_of_charTwo
    {K₂ : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 2) (Fin d → ZMod 2))}
    (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows 2 d K₂ p) :
    Fintype.card (CommutingIndex (r := 2) K₂ p) ≤ 2 ^ d := by
  classical
  let C := CommutingIndex K₂ p
  have hNgt : 1 < 2 ^ d :=
    one_lt_pow₀ (by norm_num) hd.ne'
  let f : C → Fin (2 ^ d) := fun i ↦
    ⟨p i.1, by
      have hfp :=
        R.commutative_fixedPointFree i.1 i.2.1 i.2.2
      have hdvd :
          p i.1 ∣ Nat.card (Fin d → ZMod 2) - 1 :=
        prime_dvd_natCard_sub_one_of_nontrivial_pGroup_fixedPointFreeOffZero
          (hp i.1) ((pCore (p i.1) K₂).map K₂.subtype)
          i.2.1 ((pCore_isPGroup (p i.1) K₂).map K₂.subtype) hfp
      rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hdvd
      exact
        (Nat.le_of_dvd (by omega : 0 < 2 ^ d - 1) hdvd).trans_lt
          (Nat.sub_lt (by omega) (by omega))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply hinj
    exact congrArg Fin.val hij
  simpa [C] using Fintype.card_le_of_injective f hf

/-- Full CATB for every positive-dimensional characteristic-two
quasiprimitive action. -/
theorem commonAffineTwoBaseTranslates_of_quasiprimitive_of_charTwo
    {K₂ : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 2) (Fin d → ZMod 2))}
    (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction 2 d K₂) :
    CommonAffineTwoBaseTranslates.{uI} 2 d K₂ := by
  classical
  rw [commonAffineTwoBaseTranslates_iff_on,
    commonAffineTwoBaseTranslatesOn_iff_primeCores]
  intro I _ p hp hinj hcross a b
  let R :
      PrimeCoreMixedCyclicCenterFullSchurFamilyRows 2 d K₂ p :=
    PrimeCoreMixedCyclicCenterFullSchurFamilyRows.ofQuasiprimitive
      hp hcross hqp
      (fun i hne hnoncomm ↦ by
        let hA : IsAdmissibleNoncommutingPrimeCore 2 d (p i) K₂ :=
          ⟨hp i, hcross i, hcross i, hne, hnoncomm⟩
        exact
          mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
            (by norm_num) hqp hA
            (mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
              (by norm_num) hqp hA))
  let S := ∑ i : NoncommutingIndex K₂ p, (
    1 + (p (i : I) ^ (2 * R.rank (i : I) + 1) - 1) *
      (2 ^ (2 * (d / p (i : I))) - 1))
  let C := Fintype.card (CommutingIndex K₂ p)
  have hrows : 2 * S < 2 ^ (2 * d) := by
    simpa [S] using
      two_mul_noncommuting_pairSpectrumSum_lt_of_charTwo
        hp hinj hcross R
  have hcomm : C ≤ 2 ^ d := by
    simpa [C] using card_commutingIndex_le_of_charTwo hd hp hinj R
  have hmodule : 2 * 2 ^ d ≤ 2 ^ (2 * d) := by
    have hpowTwo : 2 ≤ 2 ^ d := by
      calc
        2 = 2 ^ 1 := by simp
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
    have hsq : 2 ^ (2 * d) = (2 ^ d) * (2 ^ d) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsq]
    exact Nat.mul_le_mul_right _ hpowTwo
  apply exists_commonAffineTwoBaseTranslates_of_sum_bad_ncard_lt
    (fun i ↦ (pCore (p i) K₂).map K₂.subtype) a b
  have hcard :
      Nat.card ((Fin d → ZMod 2) × (Fin d → ZMod 2)) =
        2 ^ (2 * d) := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    rw [← pow_add]
    congr 1
    omega
  rw [hcard]
  have hbad :
      (∑ i,
        (affineTwoBaseBadSet
          ((pCore (p i) K₂).map K₂.subtype) (a i) (b i)).ncard) ≤
        S + C := by
    calc
      _ = ∑ i,
          (affineTwoBaseBadSet
            ((pCore (p i) K₂).map K₂.subtype) 0 0).ncard := by
        simp only [affineTwoBaseBadSet_ncard_eq_untranslated]
      _ ≤ ∑ i, pairSpectrumWeight R i := by
        apply Finset.sum_le_sum
        intro i _hi
        exact ncard_affineTwoBaseBadSet_zero_le_pairSpectrumWeight R i
      _ = S + C := by
        simpa only [S, C] using sum_pairSpectrumWeight_eq_split R
  calc
    _ ≤ S + C := hbad
    _ < 2 ^ (2 * d) := by omega

/-! ## Odd characteristic: the odd-prime half -/

/-- In odd characteristic, the sum of the squared ordinary nonregular
loci of all distinctly labelled odd mapped prime cores occupies strictly
less than half of the doubled module.

The proof reuses the sharper one-point estimate already needed for the
odd-order theorem.  Its total nonregular mass is strictly below `|V|`,
while every individual row has at most half that mass.  Hence

`2 * ∑ |Nonregular(O_p(K))|² < |V|²`.

This is exactly the reserve needed to combine all odd acting primes with
the unique possible acting prime `2`. -/
theorem two_mul_sum_nonregular_sq_lt_of_quasiprimitive_of_oddPrimes
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    2 * (∑ i,
      (nonregularVectors
          ((pCore (p i) K).map K.subtype)).ncard *
        (nonregularVectors
          ((pCore (p i) K).map K.subtype)).ncard) <
      r ^ (2 * d) := by
  classical
  let R :
      PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p :=
    PrimeCoreMixedCyclicCenterFullSchurFamilyRows.ofQuasiprimitive
      hp hcross hqp
      (fun i hne hnoncomm ↦ by
        let hA : IsAdmissibleNoncommutingPrimeCore r d (p i) K :=
          ⟨hp i, hpTwo i, hcross i, hne, hnoncomm⟩
        exact
          mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
            (Fact.out : Nat.Prime r) hqp hA
            (mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
              (Fact.out : Nat.Prime r) hqp hA))
  let N := r ^ d
  let n : I → ℕ := fun i ↦
    (nonregularVectors
      ((pCore (p i) K).map K.subtype)).ncard
  have hNpos : 0 < N := by
    exact pow_pos (Fact.out : Nat.Prime r).pos _
  have hNthree : 3 ≤ N := by
    have hrThree : 3 ≤ r := by
      have hrTwoLe := (Fact.out : Nat.Prime r).two_le
      omega
    calc
      3 ≤ r := hrThree
      _ = r ^ 1 := by simp
      _ ≤ r ^ d :=
        Nat.pow_le_pow_right (Fact.out : Nat.Prime r).pos hd
      _ = N := rfl
  have hsum : (∑ i, n i) < N := by
    let A := NoncommutingIndex (r := r) K p
    let C := CommutingIndex (r := r) K p
    let S := ∑ i : A, R.operatorBound (i : I)
    have hsumLe :
        (∑ i, n i) ≤ S + Fintype.card C := by
      simpa [n, A, C, S] using
        R.sum_ncard_nonregularVectors_le_split
    have hS : 2 * S < N := by
      simpa [A, S, N] using
        R.two_mul_noncommutativeSpectrumSum_lt
          hrTwo hp hpTwo hcross hinj
    have hC : Fintype.card C ≤ N / 2 := by
      simpa [C, N] using
        R.commutative_count_le_half hrTwo hp hpTwo hinj
    omega
  have hrow : ∀ i, 2 * n i ≤ N := by
    intro i
    let P :=
      (pCore (p i) K).map K.subtype
    by_cases hbot : P = ⊥
    · have hnzero : n i = 0 := by
        dsimp only [n, P] at *
        rw [hbot, nonregularVectors_bot, Set.ncard_empty]
      omega
    · by_cases hcomm : IsCommutingPrimeCore (p i) K
      · have hni :=
          R.ncard_nonregularVectors_le_spectrumWeight i
        have hweight : R.spectrumWeight i = 1 := by
          simp [PrimeCoreMixedCyclicCenterFullSchurFamilyRows.spectrumWeight,
            P, hbot, hcomm]
        change n i ≤ R.spectrumWeight i at hni
        rw [hweight] at hni
        omega
      · let A := NoncommutingIndex (r := r) K p
        let iA : A := ⟨i, hbot, hcomm⟩
        let S := ∑ j : A,
          R.operatorBound (j : I)
        have hS : 2 * S < N := by
          simpa [A, S, N] using
            R.two_mul_noncommutativeSpectrumSum_lt
              hrTwo hp hpTwo hcross hinj
        have hni :=
          R.ncard_nonregularVectors_le_spectrumWeight i
        have hweight :
            R.spectrumWeight i = R.operatorBound i := by
          simp [PrimeCoreMixedCyclicCenterFullSchurFamilyRows.spectrumWeight,
            P, hbot, hcomm]
        change n i ≤ R.spectrumWeight i at hni
        rw [hweight] at hni
        have hrowLe : R.operatorBound i ≤ S := by
          change R.operatorBound (iA : I) ≤
            ∑ j : A, R.operatorBound (j : I)
          exact Finset.single_le_sum
            (fun (j : A) _ ↦ Nat.zero_le (R.operatorBound (j : I)))
            (Finset.mem_univ iA)
        omega
  have hterm :
      ∀ i, 2 * (n i * n i) ≤ N * n i := by
    intro i
    nlinarith [hrow i]
  have hsquare :
      2 * (∑ i, n i * n i) ≤
        N * (∑ i, n i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _hi ↦ hterm i
  have htop : r ^ (2 * d) = N * N := by
    dsimp only [N]
    rw [← pow_add]
    congr 1
    omega
  change 2 * (∑ i, n i * n i) < r ^ (2 * d)
  rw [htop]
  exact hsquare.trans_lt
    (Nat.mul_lt_mul_of_pos_left hsum hNpos)

/-- The same half-density estimate for the actual affine two-base bad
loci, with arbitrary independent translations in the two coordinates. -/
theorem two_mul_sum_affineTwoBaseBadSet_lt_of_quasiprimitive_of_oddPrimes
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (a b : I → Fin d → ZMod r) :
    2 * (∑ i,
      (affineTwoBaseBadSet
        ((pCore (p i) K).map K.subtype) (a i) (b i)).ncard) <
      r ^ (2 * d) := by
  let bad : I → ℕ := fun i ↦
    (affineTwoBaseBadSet
      ((pCore (p i) K).map K.subtype) (a i) (b i)).ncard
  let sq : I → ℕ := fun i ↦
    (nonregularVectors
        ((pCore (p i) K).map K.subtype)).ncard *
      (nonregularVectors
        ((pCore (p i) K).map K.subtype)).ncard
  have hle : (∑ i, bad i) ≤ ∑ i, sq i := by
    apply Finset.sum_le_sum
    intro i _hi
    exact
      ncard_affineTwoBaseBadSet_le_nonregular_sq
        ((pCore (p i) K).map K.subtype) (a i) (b i)
  have hhalf :=
    two_mul_sum_nonregular_sq_lt_of_quasiprimitive_of_oddPrimes
      hrTwo hd hp hpTwo hcross hinj hqp
  change 2 * (∑ i, bad i) < r ^ (2 * d)
  exact
    (Nat.mul_le_mul_left 2 hle).trans_lt
      (by simpa only [sq] using hhalf)

end QuasiprimitiveAffineParityCATB

end LisiSabatini
