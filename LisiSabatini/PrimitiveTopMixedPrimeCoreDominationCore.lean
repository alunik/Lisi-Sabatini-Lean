module

public import LisiSabatini.PrimitiveTopPrimeCoreDominationCore
public import LisiSabatini.MixedPrimeCoreOneRowEstimates
public import LisiSabatini.QuasiprimitivePrimeCoreCore
public import LisiSabatini.CyclicCenterOperatorFixedSpaceRowCore
public import LisiSabatini.FixedPointFreePGroupDivisibility
public import LisiSabatini.FixedPointFreePalette
public import LisiSabatini.OrbitAvoidingCountCore
public import LisiSabatini.ExtraspecialFamilyHalfBudget

/-!
# Mixed prime-core domination at quasiprimitive local leaves

The cyclic-center structure used by the operator calculation belongs on the
maximal normal prime subgroup of a quasiprimitive local ambient group, not on
every smaller intrinsic component image.  Commuting prime cores are handled
separately: quasiprimitivity makes them fixed-point-free.  Noncommuting prime
cores carry the cyclic-center structure, and quasiprimitivity generates their
full-center Schur rows.

This file proves the exact mixed family budget for the actual nonregular
sets and actual distinguished orbit.  The already formalized prime-core
containment then transfers one-orbit avoidance to arbitrary normal prime
subgroups without any structural transport to those subgroups.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uJ

local instance finiteConcreteLinearSubgroupForMixedPrimeCoreDomination
    (r d : ℕ) [NeZero r]
    (P : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))) : Finite P :=
  finite_linearSubgroup_of_finite P

/-- Mixed structural rows on a finite family of mapped local prime cores.
The branch predicate is commutativity of the abstract prime core, which is
exactly the input used by the quasiprimitive fixed-point-free theorem. -/
structure PrimeCoreMixedCyclicCenterFullSchurFamilyRows
    (r d : ℕ) [Fact r.Prime] [NeZero r]
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    {J : Type uJ} [Fintype J] (p : J → ℕ) where
  rank : J → ℕ
  schurDegree : J → ℕ
  multiplicity : J → ℕ
  commutative_fixedPointFree : ∀ j,
    (pCore (p j) K).map K.subtype ≠ ⊥ →
    IsCommutingPrimeCore (p j) K →
      FixedPointFreeOffZero ((pCore (p j) K).map K.subtype)
  cyclicCenter : ∀ j,
    (pCore (p j) K).map K.subtype ≠ ⊥ →
    ¬ IsCommutingPrimeCore (p j) K →
      IsOddCyclicCenterClassTwo (p j)
        ((pCore (p j) K).map K.subtype)
  structuralRank_eq : ∀ j
    (hne : (pCore (p j) K).map K.subtype ≠ ⊥)
    (hnoncomm : ¬ IsCommutingPrimeCore (p j) K),
      (cyclicCenter j hne hnoncomm).cyclicCenterStructuralRank = rank j
  centerFixedPointFree : ∀ j
    (_hne : (pCore (p j) K).map K.subtype ≠ ⊥)
    (_hnoncomm : ¬ IsCommutingPrimeCore (p j) K),
      CenterFixedPointFreeAction r d
        ((pCore (p j) K).map K.subtype)
  schurDegree_pos : ∀ j,
    (pCore (p j) K).map K.subtype ≠ ⊥ →
    ¬ IsCommutingPrimeCore (p j) K → 0 < schurDegree j
  multiplicity_pos : ∀ j,
    (pCore (p j) K).map K.subtype ≠ ⊥ →
    ¬ IsCommutingPrimeCore (p j) K → 0 < multiplicity j
  center_card_dvd_field_pow_sub_one : ∀ j,
    (pCore (p j) K).map K.subtype ≠ ⊥ →
    ¬ IsCommutingPrimeCore (p j) K →
      Nat.card (Subgroup.center ((pCore (p j) K).map K.subtype)) ∣
        r ^ schurDegree j - 1
  dimension_eq : ∀ j,
    (pCore (p j) K).map K.subtype ≠ ⊥ →
    ¬ IsCommutingPrimeCore (p j) K →
      d = schurDegree j * p j ^ rank j * multiplicity j

namespace PrimeCoreMixedCyclicCenterFullSchurFamilyRows

variable {r d : ℕ} [Fact r.Prime] [NeZero r]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
variable {J : Type uJ} [Fintype J] {p : J → ℕ}

/-- At a quasiprimitive leaf, the only structural input is cyclic-center
class two on active noncommuting mapped prime cores.  All commuting
fixed-point-free statements and all full-center Schur rows are generated
internally. -/
def ofQuasiprimitive
    (hp : ∀ j, Nat.Prime (p j))
    (hcross : ∀ j, p j ≠ r)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcyclic : ∀ j,
      (pCore (p j) K).map K.subtype ≠ ⊥ →
      ¬ IsCommutingPrimeCore (p j) K →
        IsOddCyclicCenterClassTwo (p j)
          ((pCore (p j) K).map K.subtype)) :
    PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p := by
  classical
  let active : J → Prop := fun j ↦
    (pCore (p j) K).map K.subtype ≠ ⊥
  let hard : J → Prop := fun j ↦
    active j ∧ ¬ IsCommutingPrimeCore (p j) K
  let rows : ∀ j (hj : hard j),
      ∃ a b : ℕ,
        0 < a ∧ 0 < b ∧
        Nat.card (Subgroup.center
          ((pCore (p j) K).map K.subtype)) ∣ r ^ a - 1 ∧
        p j ∣ r ^ a - 1 ∧
        d = a * p j ^ (hcyclic j hj.1 hj.2).cyclicCenterStructuralRank * b :=
    fun j hj ↦
      exists_pCore_schurDegree_fullCenter_row_of_quasiprimitive
        hqp (hcyclic j hj.1 hj.2)
  let rank : J → ℕ := fun j ↦
    if hj : hard j then
      (hcyclic j hj.1 hj.2).cyclicCenterStructuralRank else 0
  let a : J → ℕ := fun j ↦
    if hj : hard j then Classical.choose (rows j hj) else 0
  let b : J → ℕ := fun j ↦
    if hj : hard j then
      Classical.choose (Classical.choose_spec (rows j hj)) else 0
  refine
    { rank := rank
      schurDegree := a
      multiplicity := b
      commutative_fixedPointFree := ?_
      cyclicCenter := hcyclic
      structuralRank_eq := ?_
      centerFixedPointFree := ?_
      schurDegree_pos := ?_
      multiplicity_pos := ?_
      center_card_dvd_field_pow_sub_one := ?_
      dimension_eq := ?_ }
  · intro j _hne hcomm
    exact pCore_fixedPointFree_of_quasiprimitive_of_commuting
      (Fact.out : Nat.Prime r) (hp j) (hcross j) hqp hcomm
  · intro j hne hnoncomm
    let hj : hard j := ⟨hne, hnoncomm⟩
    simp only [rank, dif_pos hj]
  · intro j _hne _hnoncomm
    exact centerFixedPointFreeAction_pCore_of_quasiprimitive
      (hp j) (hcross j) hqp
  · intro j hne hnoncomm
    let hj : hard j := ⟨hne, hnoncomm⟩
    have hs := Classical.choose_spec
      (Classical.choose_spec (rows j hj))
    simpa only [a, dif_pos hj] using hs.1
  · intro j hne hnoncomm
    let hj : hard j := ⟨hne, hnoncomm⟩
    have hs := Classical.choose_spec
      (Classical.choose_spec (rows j hj))
    simpa only [b, dif_pos hj] using hs.2.1
  · intro j hne hnoncomm
    let hj : hard j := ⟨hne, hnoncomm⟩
    have hs := Classical.choose_spec
      (Classical.choose_spec (rows j hj))
    simpa only [a, dif_pos hj] using
      hs.2.2.1
  · intro j hne hnoncomm
    let hj : hard j := ⟨hne, hnoncomm⟩
    have hs := Classical.choose_spec
      (Classical.choose_spec (rows j hj))
    simpa only [rank, a, b, dif_pos hj] using hs.2.2.2.2

/-! ## Exact mixed family arithmetic -/

abbrev NoncommutativeIndex
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : J → ℕ) : Type uJ :=
  {j : J //
    (pCore (p j) K).map K.subtype ≠ ⊥ ∧
      ¬ IsCommutingPrimeCore (p j) K}

abbrev CommutativeIndex
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : J → ℕ) : Type uJ :=
  {j : J //
    (pCore (p j) K).map K.subtype ≠ ⊥ ∧
      IsCommutingPrimeCore (p j) K}

noncomputable instance fintypeNoncommutativeIndex
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : J → ℕ) : Fintype (NoncommutativeIndex K p) :=
  Fintype.ofFinite _

noncomputable instance fintypeCommutativeIndex
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (p : J → ℕ) : Fintype (CommutativeIndex K p) :=
  Fintype.ofFinite _

def operatorBound
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (j : J) : ℕ :=
  cyclicCenterOperatorSpectrumBound r d (p j) (R.rank j)

noncomputable def spectrumWeight
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (j : J) : ℕ := by
  classical
  let P := (pCore (p j) K).map K.subtype
  exact if P = ⊥ then 0
    else if IsCommutingPrimeCore (p j) K then 1
    else R.operatorBound j

/-- Pointwise actual bad-locus bound for the mixed prime-core family. -/
theorem ncard_nonregularVectors_le_spectrumWeight
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (j : J) :
    (nonregularVectors ((pCore (p j) K).map K.subtype)).ncard ≤
      R.spectrumWeight j := by
  classical
  let P := (pCore (p j) K).map K.subtype
  by_cases hbot : P = ⊥
  · change (nonregularVectors P).ncard ≤ _
    rw [hbot]
    simp [spectrumWeight]
  · by_cases hcomm : IsCommutingPrimeCore (p j) K
    · have hfp := R.commutative_fixedPointFree j hbot hcomm
      have hbad :=
        ncard_nonregularVectors_le_one_of_fixedPointFreeOffZero P hfp
      simpa [spectrumWeight, P, hbot, hcomm] using hbad
    · have hcyc := R.cyclicCenter j hbot hcomm
      have hspectrum :=
        fixedSpectrumNonregularBound_le_cyclicCenterOperatorSpectrumBound
          P hcyc (R.centerFixedPointFree j hbot hcomm)
      rw [R.structuralRank_eq j hbot hcomm] at hspectrum
      have hbad :=
        ncard_nonregularVectors_le_fixedSpectrumNonregularBound P
      exact hbad.trans (by
        simpa [spectrumWeight, operatorBound, P, hbot, hcomm] using hspectrum)

/-- The actual nonregular-set sum splits into noncommutative operator rows
and one point for each active commuting prime core. -/
theorem sum_ncard_nonregularVectors_le_split
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p) :
    (∑ j, (nonregularVectors
      ((pCore (p j) K).map K.subtype)).ncard) ≤
      (∑ j : NoncommutativeIndex K p, R.operatorBound j.1) +
        Fintype.card (CommutativeIndex K p) := by
  classical
  let P : J → Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
    fun j ↦ (pCore (p j) K).map K.subtype
  let A := NoncommutativeIndex K p
  let F := CommutativeIndex K p
  let B : J → ℕ := fun j ↦ R.operatorBound j
  have hweight :
      (∑ j, R.spectrumWeight j) =
        (∑ j : A, B j.1) + Fintype.card F := by
    have hsplit :
        (∑ j, R.spectrumWeight j) =
          (∑ j, if P j ≠ ⊥ ∧ ¬ IsCommutingPrimeCore (p j) K
            then B j else 0) +
          (∑ j, if P j ≠ ⊥ ∧ IsCommutingPrimeCore (p j) K
            then 1 else 0) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      by_cases hbot : P j = ⊥
      · simp [spectrumWeight, P, B, hbot]
      · by_cases hcomm : IsCommutingPrimeCore (p j) K <;>
          simp [spectrumWeight, P, B, hbot, hcomm]
    rw [hsplit]
    congr 1
    · rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      apply Finset.sum_congr (Finset.subtype_univ _)
      intro j _hj
      rfl
    · rw [← Finset.sum_filter]
      rw [← Finset.sum_subtype_eq_sum_filter]
      simp only [ne_eq, Finset.subtype_univ, Finset.sum_const,
        Finset.card_univ, smul_eq_mul, mul_one]
      change Fintype.card (CommutativeIndex K p) = Fintype.card F
      rfl
  rw [← hweight]
  exact Finset.sum_le_sum fun j _hj ↦
    R.ncard_nonregularVectors_le_spectrumWeight j

/-- The noncommutative operator rows occupy strictly less than half of the
local vector space. -/
theorem two_mul_noncommutativeSpectrumSum_lt
    (hrTwo : r ≠ 2)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hcross : ∀ j, p j ≠ r)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p) :
    2 * (∑ j : NoncommutativeIndex K p,
      R.operatorBound j.1) < r ^ d := by
  let A := NoncommutativeIndex K p
  let pA : A → ℕ := fun j ↦ p j.1
  let nA : A → ℕ := fun j ↦ R.rank j.1
  let aA : A → ℕ := fun j ↦ R.schurDegree j.1
  let mA : A → ℕ := fun j ↦ R.multiplicity j.1
  have hraw := two_mul_extraspecial_family_activeSpectrum_budget_lt
    pA nA aA mA (Fact.out : Nat.Prime r) hrTwo
    (fun j ↦ hp j.1) (fun j ↦ hpTwo j.1)
    (fun j ↦ hcross j.1)
    (fun j k h ↦ Subtype.ext (hinj h))
    (fun j ↦ by
      change 0 < R.rank j.1
      rw [← R.structuralRank_eq j.1 j.2.1 j.2.2]
      exact (R.cyclicCenter j.1 j.2.1 j.2.2)
        |>.cyclicCenterStructuralRank_pos)
    (fun j ↦ R.schurDegree_pos j.1 j.2.1 j.2.2)
    (fun j ↦ R.multiplicity_pos j.1 j.2.1 j.2.2)
    (fun j ↦ by
      let hP := R.cyclicCenter j.1 j.2.1 j.2.2
      exact (show p j.1 ∣ Nat.card (Subgroup.center
          ((pCore (p j.1) K).map K.subtype)) from by
            calc
              p j.1 = Nat.card (centerPrimeKernel (p j.1)
                  ((pCore (p j.1) K).map K.subtype)) :=
                hP.card_centerPrimeKernel.symm
              _ ∣ Nat.card (Subgroup.center
                  ((pCore (p j.1) K).map K.subtype)) :=
                Subgroup.card_dvd_of_le
                  (centerPrimeKernel_le_center (p j.1)
                    ((pCore (p j.1) K).map K.subtype)))
        |>.trans
          (R.center_card_dvd_field_pow_sub_one j.1 j.2.1 j.2.2))
    (fun j ↦ R.dimension_eq j.1 j.2.1 j.2.2)
  simpa [A, pA, nA, aA, mA, operatorBound,
    cyclicCenterOperatorSpectrumBound] using hraw

/-- A noncommutative full-center prime-core row contributes its prime label
as a divisor of the number of nonzero local vectors. -/
theorem prime_dvd_fieldCard_sub_one_of_noncommutative
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (j : J)
    (hne : (pCore (p j) K).map K.subtype ≠ ⊥)
    (hnoncomm : ¬ IsCommutingPrimeCore (p j) K) :
    p j ∣ r ^ d - 1 := by
  let hP := R.cyclicCenter j hne hnoncomm
  have hpCenter : p j ∣ Nat.card (Subgroup.center
      ((pCore (p j) K).map K.subtype)) := by
    calc
      p j = Nat.card (centerPrimeKernel (p j)
          ((pCore (p j) K).map K.subtype)) :=
        hP.card_centerPrimeKernel.symm
      _ ∣ Nat.card (Subgroup.center
          ((pCore (p j) K).map K.subtype)) :=
        Subgroup.card_dvd_of_le
          (centerPrimeKernel_le_center (p j)
            ((pCore (p j) K).map K.subtype))
  have hpSchur : p j ∣ r ^ R.schurDegree j - 1 :=
    hpCenter.trans
      (R.center_card_dvd_field_pow_sub_one j hne hnoncomm)
  have haDvd : R.schurDegree j ∣ d := by
    refine ⟨p j ^ R.rank j * R.multiplicity j, ?_⟩
    calc
      d = R.schurDegree j * p j ^ R.rank j * R.multiplicity j :=
        R.dimension_eq j hne hnoncomm
      _ = R.schurDegree j *
          (p j ^ R.rank j * R.multiplicity j) := by ring
  exact hpSchur.trans (Nat.pow_sub_one_dvd_pow_sub_one r haDvd)

/-- Active commuting prime cores are at most half as numerous as local
vectors. -/
theorem commutative_count_le_half
    (hrTwo : r ≠ 2)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p) :
    Fintype.card (CommutativeIndex K p) ≤ r ^ d / 2 := by
  classical
  let F := CommutativeIndex K p
  let pF : F → ℕ := fun j ↦ p j.1
  let HF : F → Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
    fun j ↦ (pCore (p j.1) K).map K.subtype
  have hVcard : Nat.card (Fin d → ZMod r) = r ^ d := by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hVodd : Odd (Nat.card (Fin d → ZMod r)) := by
    rw [hVcard]
    exact ((Fact.out : Nat.Prime r).odd_of_ne_two hrTwo).pow
  have hactive : activeLinearIndices HF = Finset.univ := by
    ext j
    simp [activeLinearIndices, HF, j.2.1]
  have hbound :=
    activeLinearIndices_card_le_natCard_div_two_of_distinct_odd_primes_fixedPointFreeOffZero
      hVodd pF
      (fun j ↦ hp j.1) (fun j ↦ hpTwo j.1)
      (fun j k h ↦ Subtype.ext (hinj h))
      HF
      (fun j ↦ (pCore_isPGroup (p j.1) K).map K.subtype)
      (by
        intro j _hj
        exact R.commutative_fixedPointFree j.1 j.2.1 j.2.2)
  rw [hactive] at hbound
  simpa only [Finset.card_univ, hVcard] using hbound

/-- One active noncommutative prime core forces the commuting prime labels
into one sixth of the local vector space. -/
theorem six_mul_commutative_count_le_of_noncommutative
    (hrTwo : r ≠ 2)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (jE : NoncommutativeIndex K p) :
    6 * Fintype.card (CommutativeIndex K p) ≤ r ^ d := by
  classical
  let F := CommutativeIndex K p
  let N := r ^ d
  have hNodd : Odd N :=
    ((Fact.out : Nat.Prime r).odd_of_ne_two hrTwo).pow
  have hdPos : 0 < d := by
    have ha := R.schurDegree_pos jE.1 jE.2.1 jE.2.2
    have hm := R.multiplicity_pos jE.1 jE.2.1 jE.2.2
    rw [R.dimension_eq jE.1 jE.2.1 jE.2.2]
    exact Nat.mul_pos
      (Nat.mul_pos ha (pow_pos (hp jE.1).pos _)) hm
  have hpredPos : 0 < N - 1 := by
    have hNgt : 1 < N :=
      one_lt_pow₀ (Fact.out : Nat.Prime r).one_lt hdPos.ne'
    omega
  have hpEDvd : p jE.1 ∣ N - 1 := by
    simpa [N] using
      R.prime_dvd_fieldCard_sub_one_of_noncommutative
        jE.1 jE.2.1 jE.2.2
  have hsixPrime (j : F) : 6 * p j.1 ≤ N - 1 := by
    let P := (pCore (p j.1) K).map K.subtype
    have hfp : FixedPointFreeOffZero P :=
      R.commutative_fixedPointFree j.1 j.2.1 j.2.2
    have hpDvd : p j.1 ∣ N - 1 := by
      simpa [P, N, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using
        prime_dvd_natCard_sub_one_of_nontrivial_pGroup_fixedPointFreeOffZero
          (hp j.1) P j.2.1
          ((pCore_isPGroup (p j.1) K).map K.subtype) hfp
    have hpNe : p jE.1 ≠ p j.1 := by
      intro heq
      have hindex : jE.1 = j.1 := hinj heq
      exact jE.2.2 (hindex ▸ j.2.2)
    have hcop : (p jE.1).Coprime (p j.1) :=
      (Nat.coprime_primes (hp jE.1) (hp j.1)).2 hpNe
    have hprodDvd : p jE.1 * p j.1 ∣ N - 1 :=
      hcop.mul_dvd_of_dvd_of_dvd hpEDvd hpDvd
    have hprodOdd : Odd (p jE.1 * p j.1) :=
      (hp jE.1).odd_of_ne_two (hpTwo jE.1) |>.mul
        ((hp j.1).odd_of_ne_two (hpTwo j.1))
    have hcopTwo : Nat.Coprime 2 (p jE.1 * p j.1) :=
      Nat.coprime_two_left.mpr hprodOdd
    have htwoDvd : 2 ∣ N - 1 :=
      even_iff_two_dvd.mp (hNodd.tsub_odd odd_one)
    have hfullDvd : 2 * (p jE.1 * p j.1) ∣ N - 1 :=
      hcopTwo.mul_dvd_of_dvd_of_dvd htwoDvd hprodDvd
    have hfullLe := Nat.le_of_dvd hpredPos hfullDvd
    have hpEThree : 3 ≤ p jE.1 := by
      obtain ⟨k, hk⟩ := (hp jE.1).odd_of_ne_two (hpTwo jE.1)
      have := (hp jE.1).two_le
      omega
    calc
      6 * p j.1 ≤ 2 * (p jE.1 * p j.1) := by nlinarith
      _ ≤ N - 1 := hfullLe
  let M := N / 6
  let f : F → Fin M := fun j ↦
    ⟨p j.1 - 1, by
      have hpPos := (hp j.1).pos
      have hpLe : p j.1 ≤ M := by
        apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 6)).2
        have hle := hsixPrime j
        have hpredLe : N - 1 ≤ N := Nat.sub_le _ _
        simpa [M, mul_comm] using hle.trans hpredLe
      omega⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hv : p x.1 - 1 = p y.1 - 1 := congrArg Fin.val hxy
    have hpx := (hp x.1).pos
    have hpy := (hp y.1).pos
    exact Subtype.ext (hinj (by omega))
  have hcard := Fintype.card_le_of_injective f hf
  rw [Fintype.card_fin] at hcard
  change 6 * Fintype.card F ≤ N
  calc
    6 * Fintype.card F ≤ 6 * M := Nat.mul_le_mul_left 6 hcard
    _ = M * 6 := by ring
    _ ≤ N := by simpa [M] using Nat.div_mul_le_self N 6

/-- In the presence of a noncommutative prime core, the order of any active
commuting fixed-point-free prime core occupies at most one sixth of the local
space. -/
theorem six_mul_natCard_commutative_le_of_noncommutative
    (hrTwo : r ≠ 2)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (jE : NoncommutativeIndex K p)
    (j : CommutativeIndex K p) :
    6 * Nat.card ((pCore (p j.1) K).map K.subtype) ≤ r ^ d := by
  let P := (pCore (p j.1) K).map K.subtype
  let N := r ^ d
  letI : Fact (p j.1).Prime := ⟨hp j.1⟩
  have hNodd : Odd N :=
    ((Fact.out : Nat.Prime r).odd_of_ne_two hrTwo).pow
  have hdPos : 0 < d := by
    have ha := R.schurDegree_pos jE.1 jE.2.1 jE.2.2
    have hm := R.multiplicity_pos jE.1 jE.2.1 jE.2.2
    rw [R.dimension_eq jE.1 jE.2.1 jE.2.2]
    exact Nat.mul_pos
      (Nat.mul_pos ha (pow_pos (hp jE.1).pos _)) hm
  have hpredPos : 0 < N - 1 := by
    have hNgt : 1 < N :=
      one_lt_pow₀ (Fact.out : Nat.Prime r).one_lt hdPos.ne'
    omega
  have hpEDvd : p jE.1 ∣ N - 1 := by
    simpa [N] using
      R.prime_dvd_fieldCard_sub_one_of_noncommutative
        jE.1 jE.2.1 jE.2.2
  have hfp : FixedPointFreeOffZero P :=
    R.commutative_fixedPointFree j.1 j.2.1 j.2.2
  have hcardDvd : Nat.card P ∣ N - 1 := by
    simpa [P, N, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using
      natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero P hfp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp
    ((pCore_isPGroup (p j.1) K).map K.subtype)
  have hcardOdd : Odd (Nat.card P) := by
    rw [hk]
    exact (hp j.1).odd_of_ne_two (hpTwo j.1) |>.pow
  have hpNe : p jE.1 ≠ p j.1 := by
    intro heq
    have hindex : jE.1 = j.1 := hinj heq
    exact jE.2.2 (hindex ▸ j.2.2)
  have hcopPrime : (p jE.1).Coprime (p j.1) :=
    (Nat.coprime_primes (hp jE.1) (hp j.1)).2 hpNe
  have hcopCard : (p jE.1).Coprime (Nat.card P) := by
    rw [hk]
    exact hcopPrime.pow_right _
  have hprodDvd : p jE.1 * Nat.card P ∣ N - 1 :=
    hcopCard.mul_dvd_of_dvd_of_dvd hpEDvd hcardDvd
  have hcopTwo : Nat.Coprime 2 (p jE.1 * Nat.card P) := by
    apply Nat.coprime_two_left.mpr
    exact (hp jE.1).odd_of_ne_two (hpTwo jE.1) |>.mul hcardOdd
  have htwoDvd : 2 ∣ N - 1 :=
    even_iff_two_dvd.mp (hNodd.tsub_odd odd_one)
  have hfullDvd : 2 * (p jE.1 * Nat.card P) ∣ N - 1 :=
    hcopTwo.mul_dvd_of_dvd_of_dvd htwoDvd hprodDvd
  have hfullLe := Nat.le_of_dvd hpredPos hfullDvd
  have hpEThree : 3 ≤ p jE.1 := by
    obtain ⟨k, hk⟩ := (hp jE.1).odd_of_ne_two (hpTwo jE.1)
    have := (hp jE.1).two_le
    omega
  change 6 * Nat.card P ≤ N
  calc
    6 * Nat.card P ≤ 2 * (p jE.1 * Nat.card P) := by nlinarith
    _ ≤ N - 1 := hfullLe
    _ ≤ N := Nat.sub_le _ _

/-- A distinguished orbit of a noncommutative prime core costs at most one
third of its own operator-spectrum budget. -/
theorem three_mul_orbit_le_operatorBound_of_noncommutative
    (hrTwo : r ≠ 2)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (j : J)
    (hne : (pCore (p j) K).map K.subtype ≠ ⊥)
    (hnoncomm : ¬ IsCommutingPrimeCore (p j) K)
    (c : Fin d → ZMod r) :
    3 * (MulAction.orbit
      ((pCore (p j) K).map K.subtype) c).ncard ≤
        R.operatorBound j := by
  let P := (pCore (p j) K).map K.subtype
  let hP := R.cyclicCenter j hne hnoncomm
  have hdim := R.dimension_eq j hne hnoncomm
  rw [← R.structuralRank_eq j hne hnoncomm] at hdim
  have hcard :=
    three_mul_natCard_le_cyclicCenterOperatorSpectrumBound_of_fullCenterRow
      hP hrTwo (R.schurDegree_pos j hne hnoncomm)
      (R.multiplicity_pos j hne hnoncomm)
      (R.center_card_dvd_field_pow_sub_one j hne hnoncomm) hdim
  have hrank := R.structuralRank_eq j hne hnoncomm
  rw [hrank] at hcard
  calc
    3 * (MulAction.orbit P c).ncard ≤ 3 * Nat.card P :=
      Nat.mul_le_mul_left 3 (ncard_orbit_le_natCard P c)
    _ ≤ R.operatorBound j := by
      simpa [P, operatorBound] using hcard

/-- Exact mixed budget for the actual nonregular sets of the mapped local
prime cores together with one actual distinguished prime-core orbit. -/
theorem sum_ncard_nonregularVectors_add_pCoreOrbit_lt
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hcross : ∀ j, p j ≠ r)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (j₀ : J) (c : Fin d → ZMod r) :
    (∑ j, (nonregularVectors
      ((pCore (p j) K).map K.subtype)).ncard) +
      (MulAction.orbit
        ((pCore (p j₀) K).map K.subtype) c).ncard < r ^ d := by
  classical
  let A := NoncommutativeIndex K p
  let F := CommutativeIndex K p
  let S := ∑ j : A, R.operatorBound j.1
  let P₀ := (pCore (p j₀) K).map K.subtype
  let O := (MulAction.orbit P₀ c).ncard
  let N := r ^ d
  have hsum :
      (∑ j, (nonregularVectors
        ((pCore (p j) K).map K.subtype)).ncard) ≤
        S + Fintype.card F := by
    simpa [A, F, S] using R.sum_ncard_nonregularVectors_le_split
  have hS : 2 * S < N := by
    simpa [A, S, N] using
      R.two_mul_noncommutativeSpectrumSum_lt
        hrTwo hp hpTwo hcross hinj
  have hOrbitCard : O ≤ Nat.card P₀ := by
    simpa only [O] using ncard_orbit_le_natCard P₀ c
  cases isEmpty_or_nonempty A with
  | inl hA =>
      letI : IsEmpty A := hA
      have hSzero : S = 0 := by simp [S]
      have hFhalf : Fintype.card F ≤ N / 2 := by
        simpa [F, N] using R.commutative_count_le_half hrTwo hp hpTwo hinj
      have hNodd : Odd N :=
        ((Fact.out : Nat.Prime r).odd_of_ne_two hrTwo).pow
      have hNgt : 1 < N :=
        one_lt_pow₀ (Fact.out : Nat.Prime r).one_lt hd.ne'
      have hVcard : Nat.card (Fin d → ZMod r) = N := by
        rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
      have hOhalf : O ≤ (N - 1) / 2 := by
        by_cases hbot : P₀ = ⊥
        · have hcardOne : Nat.card P₀ = 1 := by
            rw [hbot, Subgroup.card_bot]
          have hrThree : 3 ≤ r := by
            obtain ⟨k, hk⟩ :=
              (Fact.out : Nat.Prime r).odd_of_ne_two hrTwo
            have := (Fact.out : Nat.Prime r).two_le
            omega
          have hNthree : 3 ≤ N := by
            calc
              3 ≤ r := hrThree
              _ = r ^ 1 := by simp
              _ ≤ r ^ d := Nat.pow_le_pow_right
                (Fact.out : Nat.Prime r).pos hd
              _ = N := rfl
          omega
        · have hcomm : IsCommutingPrimeCore (p j₀) K := by
            by_contra hnoncomm
            exact isEmptyElim (show A from ⟨j₀, hbot, hnoncomm⟩)
          have hfp := R.commutative_fixedPointFree j₀ hbot hcomm
          have hcard :=
            natCard_le_half_natCard_sub_one_of_oddPGroup_fixedPointFreeOffZero
              (by rw [hVcard]; exact hNodd)
              (by rw [hVcard]; exact hNgt)
              (hp j₀) (hpTwo j₀) P₀
              ((pCore_isPGroup (p j₀) K).map K.subtype) hfp
          rw [hVcard] at hcard
          exact hOrbitCard.trans hcard
      change (∑ j, (nonregularVectors
        ((pCore (p j) K).map K.subtype)).ncard) + O < N
      have hNmod : N % 2 = 1 :=
        Nat.not_even_iff.mp (Nat.not_even_iff_odd.mpr hNodd)
      have hNform := Nat.two_mul_odd_div_two hNmod
      omega
  | inr hA =>
      letI : Nonempty A := hA
      let jE : A := Classical.choice hA
      have hSpos : 0 < S := by
        have hBpos : 0 < R.operatorBound jE.1 := by
          unfold operatorBound cyclicCenterOperatorSpectrumBound
          omega
        have hBLe : R.operatorBound jE.1 ≤ S := by
          change R.operatorBound jE.1 ≤
            ∑ j : A, R.operatorBound j.1
          exact Finset.single_le_sum
            (fun (j : A) _ ↦ Nat.zero_le (R.operatorBound j.1))
            (Finset.mem_univ jE)
        exact hBpos.trans_le hBLe
      have hF6 : 6 * Fintype.card F ≤ N := by
        simpa [F, N] using
          R.six_mul_commutative_count_le_of_noncommutative
            hrTwo hp hpTwo hinj jE
      change (∑ j, (nonregularVectors
        ((pCore (p j) K).map K.subtype)).ncard) + O < N
      refine lt_of_le_of_lt (Nat.add_le_add_right hsum O) ?_
      by_cases hbot : P₀ = ⊥
      · have hcardOne : Nat.card P₀ = 1 := by
          rw [hbot, Subgroup.card_bot]
        omega
      · by_cases hcomm : IsCommutingPrimeCore (p j₀) K
        · let jF : F := ⟨j₀, hbot, hcomm⟩
          have hcard6 : 6 * Nat.card P₀ ≤ N := by
            exact R.six_mul_natCard_commutative_le_of_noncommutative
              hrTwo hp hpTwo hinj jE jF
          have hO6 : 6 * O ≤ N :=
            (Nat.mul_le_mul_left 6 hOrbitCard).trans hcard6
          omega
        · let jA : A := ⟨j₀, hbot, hcomm⟩
          have hO3 : 3 * O ≤ R.operatorBound j₀ := by
            exact R.three_mul_orbit_le_operatorBound_of_noncommutative
              hrTwo j₀ hbot hcomm c
          have hBLe : R.operatorBound j₀ ≤ S := by
            change R.operatorBound jA.1 ≤
              ∑ j : A, R.operatorBound j.1
            exact Finset.single_le_sum
              (fun (j : A) _ ↦ Nat.zero_le (R.operatorBound j.1))
              (Finset.mem_univ jA)
          omega

/-- The exact mixed budget gives one-orbit-avoiding common translated
regularity for the mapped local prime cores. -/
theorem orbitAvoidingCommonRegularTranslates_pCores
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hcross : ∀ j, p j ≠ r)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p) :
    OrbitAvoidingCommonRegularTranslates
      (fun j ↦ (pCore (p j) K).map K.subtype) := by
  apply orbitAvoidingCommonRegularTranslates_of_sum_ncard_add_orbit_lt
  intro j₀ c
  rw [show Nat.card (Fin d → ZMod r) = r ^ d by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]]
  exact R.sum_ncard_nonregularVectors_add_pCoreOrbit_lt
    hrTwo hd hp hpTwo hcross hinj j₀ c

/-- Prime-core containment transfers the exact mixed theorem to arbitrary
normal prime subgroups; no cyclic-center property is transported to them. -/
theorem orbitAvoidingCommonRegularTranslates_normalPSubgroups
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hcross : ∀ j, p j ≠ r)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p)
    (A : J → Subgroup K)
    (hAn : ∀ j, (A j).Normal)
    (hAq : ∀ j, IsPGroup (p j) (A j)) :
    OrbitAvoidingCommonRegularTranslates
      (fun j ↦ (A j).map K.subtype) :=
  orbitAvoidingCommonRegularTranslates_of_pCore p
    (R.orbitAvoidingCommonRegularTranslates_pCores
      hrTwo hd hp hpTwo hcross hinj)
    A hAn hAq

set_option linter.unusedFintypeInType false in
/-- At a quasiprimitive local ambient group, cyclic-center structure only on
active noncommuting mapped prime cores gives one-orbit avoidance for every
family of normal prime subgroups.  Commuting cores and all Schur rows are
automatic. -/
theorem orbitAvoidingCommonRegularTranslates_of_quasiprimitive
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ j, Nat.Prime (p j))
    (hpTwo : ∀ j, p j ≠ 2)
    (hcross : ∀ j, p j ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcyclic : ∀ j,
      (pCore (p j) K).map K.subtype ≠ ⊥ →
      ¬ IsCommutingPrimeCore (p j) K →
        IsOddCyclicCenterClassTwo (p j)
          ((pCore (p j) K).map K.subtype))
    (A : J → Subgroup K)
    (hAn : ∀ j, (A j).Normal)
    (hAq : ∀ j, IsPGroup (p j) (A j)) :
    OrbitAvoidingCommonRegularTranslates
      (fun j ↦ (A j).map K.subtype) := by
  let R := ofQuasiprimitive hp hcross hqp hcyclic
  exact R.orbitAvoidingCommonRegularTranslates_normalPSubgroups
    hrTwo hd hp hpTwo hcross hinj A hAn hAq

end PrimeCoreMixedCyclicCenterFullSchurFamilyRows

end LisiSabatini
