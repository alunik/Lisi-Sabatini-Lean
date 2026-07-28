module

public import LisiSabatini.QuasiprimitiveAffineParityCATBAssembly
public import LisiSabatini.QuasiprimitiveAffineTwoOrbitOddPrimeLeaf
public import LisiSabatini.MappedPCoreHall
public import LisiSabatini.TwoCoreSymplecticTypeNonmixedAssembly
public import LisiSabatini.TwoCoreSymplecticTypeMappedHomogeneous
public import LisiSabatini.TwoCoreSymplecticTypeCentralCommutatorF3Plane

/-!
# The recursively stable odd-characteristic two-core leaf

For an odd-characteristic quasiprimitive affine action, the odd acting
prime rows already have more reserve than is visible in the ordinary CATB
assembly.  After passing to the doubled module, their bad loci together
with two full orbits of any distinguished odd row occupy strictly less
than half of the module.

Consequently, the only genuinely new numerical input is the *joint* budget
when the distinguished row is the mapped normal `2`-core.  This file
isolates that exact boundary.  The boundary is sharp in the following
sense: it asks for the actual total doubled bad locus plus two full
`2`-core orbits to be smaller than the doubled module, rather than imposing
separate half-density conditions which exclude the extremal
`QD₁₆ ≤ GL₂(3)` example.

No classification of finite `2`-groups is asserted here.  At the end of
the file we record exactly what the current quasiprimitive/Hall machinery
does prove unconditionally, and prove the complete recursively stable
leaf when the mapped `2`-core is commuting.  The remaining boundary is
therefore confined to a noncommuting `2`-core satisfying Hall's
cyclic-characteristic-abelian condition and a fixed-point-free center.
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

local instance fintypeConcreteLinearSubgroupForTwoCoreReserve
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin e → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P (finite_linearSubgroup_of_finite P)

abbrev diagonalMappedPCore
    (q : ℕ) :
    Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r)
        ((Fin d → ZMod r) × (Fin d → ZMod r))) :=
  ((pCore q K).map K.subtype).map
    (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))

omit [NeZero r] in
private theorem ncard_nonregular_diagonalMappedPCore_eq_affineBadSet
    (q : ℕ) :
    (nonregularVectors
      (diagonalMappedPCore (K := K) q)).ncard =
      (affineTwoBaseBadSet
        ((pCore q K).map K.subtype) 0 0).ncard := by
  congr 1
  ext z
  simpa using
    (mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
      ((pCore q K).map K.subtype) 0 0 z).symm

/-! ## Extra reserve in the odd acting-prime rows -/

namespace OddPrimeDiagonalReserve

variable {I : Type uI} [Fintype I] {p : I → ℕ}

/-- The source nonregular loci for a distinctly odd-prime-labelled
quasiprimitive family have total size below the module size, and every
single row has size at most half the module.

The conjunction is extracted because it is the exact arithmetic input for
the stronger doubled-module reserve below. -/
theorem source_sum_lt_and_two_mul_row_le
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    (∑ i,
        (nonregularVectors
          ((pCore (p i) K).map K.subtype)).ncard) < r ^ d ∧
      ∀ i,
        2 *
            (nonregularVectors
              ((pCore (p i) K).map K.subtype)).ncard ≤
          r ^ d := by
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
  have hsum : (∑ i, n i) < N := by
    let A :=
      {i : I //
        (pCore (p i) K).map K.subtype ≠ ⊥ ∧
          ¬ IsCommutingPrimeCore (p i) K}
    let C :=
      {i : I //
        (pCore (p i) K).map K.subtype ≠ ⊥ ∧
          IsCommutingPrimeCore (p i) K}
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
    let P := (pCore (p i) K).map K.subtype
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
      · let A :=
          {j : I //
            (pCore (p j) K).map K.subtype ≠ ⊥ ∧
              ¬ IsCommutingPrimeCore (p j) K}
        let iA : A := ⟨i, hbot, hcomm⟩
        let S := ∑ j : A, R.operatorBound (j : I)
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
  exact ⟨by simpa [n, N] using hsum, fun i ↦ by
    simpa [n, N] using hrow i⟩

/-- Abstract arithmetic behind the strengthened odd-row reserve. -/
private theorem
    two_mul_sum_sq_add_two_mul_lt_sq_of_row_half
    (n : I → ℕ) (C N : ℕ)
    (hN : 3 ≤ N)
    (hsum : (∑ i, n i) + C < N)
    (hrow : ∀ i, 2 * n i ≤ N) :
    2 * ((∑ i, n i * n i) + 2 * C) < N * N := by
  let S := ∑ i, n i
  change S + C < N at hsum
  have hterm (i : I) : 2 * (n i * n i) ≤ N * n i := by
    nlinarith [hrow i]
  have hsquares :
      2 * (∑ i, n i * n i) ≤ N * S := by
    dsimp only [S]
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _hi ↦ hterm i
  have hC : C < N := by
    omega
  have htail : N * S + 4 * C < N * N := by
    have hstep : S + C + 1 ≤ N := by
      omega
    by_cases hthree : N = 3
    · subst N
      omega
    · have hfour : 4 ≤ N := by omega
      nlinarith
  calc
    2 * ((∑ i, n i * n i) + 2 * C) =
        2 * (∑ i, n i * n i) + 4 * C := by ring
    _ ≤ N * S + 4 * C := Nat.add_le_add_right hsquares _
    _ < N * N := htail

/-- A regular point has an orbit of full group cardinality. -/
private theorem ncard_orbit_eq_natCard_of_stabilizer_eq_bot
    {R V : Type*}
    [Semiring R] [AddCommGroup V] [Module R V] [Finite V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (c : V) (hregular : MulAction.stabilizer H c = ⊥) :
    (MulAction.orbit H c).ncard = Nat.card H := by
  letI : Finite H := finite_linearSubgroup_of_finite H
  have hinjective : Function.Injective (fun g : H ↦ g • c) := by
    intro g h hgh
    change g • c = h • c at hgh
    let k : H := h⁻¹ * g
    have hkFix : k • c = c := by
      dsimp only [k]
      rw [mul_smul, hgh, inv_smul_smul]
    have hkMem : k ∈ MulAction.stabilizer H c :=
      MulAction.mem_stabilizer_iff.mpr hkFix
    have hkOne : k = 1 :=
      (Subgroup.eq_bot_iff_forall _).mp hregular k hkMem
    exact (inv_mul_eq_one.mp hkOne).symm
  rw [MulAction.orbit, ← Set.image_univ,
    Set.ncard_image_of_injective _ hinjective,
    Set.ncard_univ]

/-- The doubled bad loci of all odd acting-prime rows, together with two
full orbits of a distinguished odd row, occupy strictly less than half of
the doubled module. -/
theorem
    two_mul_sum_diagonal_bad_add_two_mul_card_lt_of_quasiprimitive
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (i₀ : I) :
    2 *
        ((∑ i,
            (nonregularVectors
              (diagonalMappedPCore (K := K) (p i))).ncard) +
          2 * Nat.card
            (diagonalMappedPCore (K := K) (p i₀))) <
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
  let P : I →
      Subgroup
        (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
    fun i ↦ (pCore (p i) K).map K.subtype
  let n : I → ℕ := fun i ↦
    (nonregularVectors (P i)).ncard
  let C := Nat.card (P i₀)
  let N := r ^ d
  have hsource :=
    source_sum_lt_and_two_mul_row_le
      (K := K) hrTwo hd hp hpTwo hcross hinj hqp
  have hsum : (∑ i, n i) < N := by
    simpa [n, P, N] using hsource.1
  have hsumForAvoidance :
      (∑ i, (nonregularVectors (P i)).ncard) <
        Nat.card (Fin d → ZMod r) := by
    simpa [n, N, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using hsum
  obtain ⟨c, hc⟩ :=
    exists_avoids_of_sum_ncard_lt
      (fun i ↦ nonregularVectors (P i)) hsumForAvoidance
  have hregular : MulAction.stabilizer (P i₀) c = ⊥ := by
    simpa [nonregularVectors] using hc i₀
  have horbit :
      (MulAction.orbit (P i₀) c).ncard = C := by
    simpa [C] using
      ncard_orbit_eq_natCard_of_stabilizer_eq_bot
        (P i₀) c hregular
  have hsumCard : (∑ i, n i) + C < N := by
    have h :=
      R.sum_ncard_nonregularVectors_add_pCoreOrbit_lt
        hrTwo hd hp hpTwo hcross hinj i₀ c
    change
      (∑ i,
          (nonregularVectors
            ((pCore (p i) K).map K.subtype)).ncard) +
          C <
        r ^ d
    rw [← horbit]
    exact h
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
  have harithmetic :
      2 * ((∑ i, n i * n i) + 2 * C) < N * N :=
    two_mul_sum_sq_add_two_mul_lt_sq_of_row_half
      n C N hNthree hsumCard
      (fun i ↦ by simpa [n, P, N] using hsource.2 i)
  have hdiag (i : I) :
      (nonregularVectors
        (diagonalMappedPCore (K := K) (p i))).ncard ≤
        n i * n i := by
    rw [ncard_nonregular_diagonalMappedPCore_eq_affineBadSet]
    exact
      ncard_affineTwoBaseBadSet_le_nonregular_sq
        (P i) 0 0
  have hsumDiag :
      (∑ i,
        (nonregularVectors
          (diagonalMappedPCore (K := K) (p i))).ncard) ≤
        ∑ i, n i * n i :=
    Finset.sum_le_sum fun i _hi ↦ hdiag i
  have hcardDiag :
      Nat.card (diagonalMappedPCore (K := K) (p i₀)) = C := by
    change
      Nat.card
          ((P i₀).map
            (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))) =
        Nat.card (P i₀)
    exact
      Subgroup.card_map_of_injective
        (K := P i₀)
        (diagonalGeneralLinearHom_injective
          (ZMod r) (Fin d → ZMod r))
  have htop : r ^ (2 * d) = N * N := by
    dsimp only [N]
    rw [← pow_add]
    congr 1
    omega
  rw [hcardDiag, htop]
  exact
    (Nat.mul_le_mul_left 2
      (Nat.add_le_add_right hsumDiag (2 * C))).trans_lt
      harithmetic

/-- A coarser total bound used in the commuting `2`-core branch. -/
theorem
    two_mul_sum_diagonal_bad_le_fieldCard_mul_pred_of_quasiprimitive
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    2 *
        (∑ i,
          (nonregularVectors
            (diagonalMappedPCore (K := K) (p i))).ncard) ≤
      r ^ d * (r ^ d - 1) := by
  let n : I → ℕ := fun i ↦
    (nonregularVectors
      ((pCore (p i) K).map K.subtype)).ncard
  let N := r ^ d
  have hsource :=
    source_sum_lt_and_two_mul_row_le
      (K := K) hrTwo hd hp hpTwo hcross hinj hqp
  have hterm (i : I) :
      2 * (n i * n i) ≤ N * n i := by
    nlinarith [show 2 * n i ≤ N by
      simpa [n, N] using hsource.2 i]
  have hsquare :
      2 * (∑ i, n i * n i) ≤ N * (∑ i, n i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _hi ↦ hterm i
  have hsumPred : (∑ i, n i) ≤ N - 1 := by
    have : (∑ i, n i) < N := by
      simpa [n, N] using hsource.1
    omega
  have hdiag :
      (∑ i,
        (nonregularVectors
          (diagonalMappedPCore (K := K) (p i))).ncard) ≤
        ∑ i, n i * n i := by
    apply Finset.sum_le_sum
    intro i _hi
    rw [ncard_nonregular_diagonalMappedPCore_eq_affineBadSet]
    exact ncard_affineTwoBaseBadSet_le_nonregular_sq
      ((pCore (p i) K).map K.subtype) 0 0
  exact
    (Nat.mul_le_mul_left 2 hdiag).trans
      (hsquare.trans (Nat.mul_le_mul_left N hsumPred))

end OddPrimeDiagonalReserve

/-! ## The exact noncommuting two-core publication boundary -/

/-- Exact numerical data needed for the recursively stable
odd-characteristic quasiprimitive leaf.

`halfDensity` is the already isolated symplectic-type estimate.  It is
enough whenever the distinguished row has odd acting prime, because the
preceding theorem charges that row and both forbidden orbits inside the
other half.

`distinguishedTwo` is the remaining joint estimate.  It is deliberately
stated using the actual doubled bad loci and two full mapped `2`-core
orbits.  Thus it does not lose the correlations between the `2`-core row
and the odd rows, and it does not impose a false separate half-reserve
condition on the `2`-core. -/
structure OddCharacteristicTwoCoreTwoOrbitReserveData
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop where
  halfDensity : TwoCoreSymplecticTypeHalfDensityData K
  distinguishedTwo :
    ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
      (∀ i, Nat.Prime (p i)) →
      Function.Injective p →
      (∀ i, p i ≠ r) →
      ∀ (i₂ : I), p i₂ = 2 →
        (∑ i,
            (nonregularVectors
              (diagonalMappedPCore (K := K) (p i))).ncard) +
            2 * Nat.card
              (diagonalMappedPCore (K := K) 2) <
          r ^ (2 * d)

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

/-! ## Assembly of the exact leaf -/

/-- The exact two-core reserve data gives the recursively stable
two-orbit property for the full family of mapped prime cores.

For a distinguished odd row, the family is split into its possible
`2`-label and its odd labels.  The `2`-row uses `halfDensity`, while the
odd rows together with the two distinguished orbits use
`OddPrimeDiagonalReserve.two_mul_sum_diagonal_bad_add_two_mul_card_lt_of_quasiprimitive`.
For a distinguished `2`-row, the exact joint field
`distinguishedTwo` applies directly. -/
theorem
    twoOrbitAvoidingCommonRegularTranslates_diagonal_pCores_of_quasiprimitive_of_oddChar
    {I : Type uI} [Finite I] {p : I → ℕ}
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hdata : OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun i ↦ diagonalMappedPCore (K := K) (p i)) := by
  classical
  letI := Fintype.ofFinite I
  apply
    twoOrbitAvoidingCommonRegularTranslates_of_sum_ncard_add_two_mul_natCard_lt
  intro i₀
  have htop :
      Nat.card
          ((Fin d → ZMod r) × (Fin d → ZMod r)) =
        r ^ (2 * d) := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    rw [← pow_add]
    congr 1
    omega
  rw [htop]
  by_cases hiTwo : p i₀ = 2
  · have h :=
      hdata.distinguishedTwo (I := I) p hp hinj hcross i₀ hiTwo
    simpa [diagonalMappedPCore, hiTwo] using h
  · let f : I → ℕ := fun i ↦
      (nonregularVectors
        (diagonalMappedPCore (K := K) (p i))).ncard
    let T := TwoIndex p
    let O := OddIndex p
    let pO : O → ℕ := fun i ↦ p i.1
    let iO : O := ⟨i₀, hiTwo⟩
    let D₂ :=
      (nonregularVectors
        (diagonalMappedPCore (K := K) 2)).ncard
    let C₀ :=
      Nat.card (diagonalMappedPCore (K := K) (p i₀))
    let M := r ^ (2 * d)
    have htwo : 2 * D₂ < M := by
      dsimp only [D₂]
      rw [ncard_nonregular_diagonalMappedPCore_eq_affineBadSet]
      simpa [M] using
        two_mul_ncard_affineTwoBaseBadSet_mapped_pCore_two_lt_of_quasiprimitive
          hqp hrTwo hd hdata.halfDensity
    have hodd :
        2 * ((∑ i : O, f i.1) + 2 * C₀) < M := by
      have h :=
        OddPrimeDiagonalReserve.two_mul_sum_diagonal_bad_add_two_mul_card_lt_of_quasiprimitive
            (K := K) hrTwo hd
            (p := pO)
            (fun i ↦ hp i.1)
            (fun i ↦ i.2)
            (fun i ↦ hcross i.1)
            (fun _i _j hij ↦ Subtype.ext (hinj hij))
            hqp iO
      exact h
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
          (∑ i : T, f i.1) + ∑ i : O, f i.1 := by
      exact sum_eq_sum_twoIndex_add_oddIndex p f
    change (∑ i, f i) + 2 * C₀ < M
    rw [hsplit]
    omega

/-- Prime-core containment transfers the exact leaf to arbitrary normal
prime-power components. -/
theorem
    twoOrbitAvoidingCommonRegularTranslates_diagonal_of_quasiprimitive_of_oddChar
    {I : Type uI} [Finite I] {p : I → ℕ}
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hdata : OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K)
    (H : I → Subgroup K)
    (hHnormal : ∀ i, (H i).Normal)
    (hHp : ∀ i, IsPGroup (p i) (H i)) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun i ↦
        ((H i).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))) := by
  apply
    TwoOrbitAvoidingCommonRegularTranslates.mono
      (B := fun i ↦ diagonalMappedPCore (K := K) (p i))
  · intro i
    exact Subgroup.map_mono
      (map_normalPSubgroup_le_map_pCore (hHp i) (hHnormal i))
  · exact
      twoOrbitAvoidingCommonRegularTranslates_diagonal_pCores_of_quasiprimitive_of_oddChar
        hrTwo hd hp hcross hinj hqp hdata

/-- Full recursively stable odd-characteristic quasiprimitive leaf,
conditional only on the exact two-core reserve datum. -/
theorem
    commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_quasiprimitive_of_oddChar
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hdata : OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
      r (Fin d → ZMod r) K := by
  intro I _ p hp hinj hcross H hHnormal hHp
  exact
    twoOrbitAvoidingCommonRegularTranslates_diagonal_of_quasiprimitive_of_oddChar
      hrTwo hd hp hcross hinj hqp hdata H hHnormal hHp

/-- The strong leaf recovers ordinary CATB.  This statement deliberately
uses the already audited parity assembly, showing that the new datum
strictly extends its former publication boundary. -/
theorem
    commonAffineTwoBaseTranslates_of_quasiprimitive_of_oddChar_of_twoOrbitReserve
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hdata : OddCharacteristicTwoCoreTwoOrbitReserveData K) :
    CommonAffineTwoBaseTranslates.{uI} r d K :=
  QuasiprimitiveAffineParityCATB.commonAffineTwoBaseTranslates_of_quasiprimitive_of_oddChar
    hrTwo hd hqp hdata.halfDensity

/-! ## What the present Hall machinery proves unconditionally -/

/-- The exact structural frontier currently available for the mapped
normal `2`-core of an odd-characteristic quasiprimitive action.

The three fields are all unconditional:

* it is a `2`-group;
* every characteristic abelian subgroup is cyclic (Hall's hypothesis);
* every nonidentity central element acts fixed-point-freely.

What is not contained here is a classification of the noncommuting group
or a count of its active involutions. -/
structure MappedTwoCoreQuasiprimitiveFrontier
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop where
  pGroup :
    IsPGroup 2 ((pCore 2 K).map K.subtype)
  hall :
    HasCyclicCharacteristicAbelianSubgroups
      ((pCore 2 K).map K.subtype)
  centerFixedPointFree :
    CenterFixedPointFreeAction r d
      ((pCore 2 K).map K.subtype)

omit [NeZero r] in
/-- Quasiprimitivity supplies the complete mapped two-core frontier above,
without any solvability or classification hypothesis. -/
theorem mappedTwoCoreQuasiprimitiveFrontier
    (hrTwo : r ≠ 2)
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    MappedTwoCoreQuasiprimitiveFrontier K where
  pGroup := (pCore_isPGroup 2 K).map K.subtype
  hall :=
    mapped_pCore_hasCyclicCharacteristicAbelianSubgroups_of_quasiprimitive
      (Fact.out : Nat.Prime r) Nat.prime_two hrTwo.symm hqp
  centerFixedPointFree :=
    centerFixedPointFreeAction_pCore_of_quasiprimitive
      Nat.prime_two hrTwo.symm hqp

/-- A mixed Hall--Berger description of the mapped `2`-core now supplies
the complete half-density datum.  Quasiprimitivity supplies homogeneity on
the abstract normal core, and homogeneity is transported automatically to
its faithful general-linear image. -/
theorem twoCoreSymplecticTypeHalfDensityData_of_mixedCentralProduct
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (data : BergerMixedCentralProductData
      ((pCore 2 K).map K.subtype)) :
    TwoCoreSymplecticTypeHalfDensityData K := by
  let P := (pCore 2 K).map K.subtype
  let F :=
    mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  have hhom :
      Representation.IsHomogeneous
        (linearSubgroupRepresentation P) := by
    simpa only [P] using
      mappedPCore_linearRepresentation_isHomogeneous
        (q := 2) hqp
  change
    2 * (activePrimeOrderElements 2 P).card ≤
          r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d
  exact
    BergerMixedCentralProductData.halfDensity_of_homogeneous
      P hrTwo hd F.pGroup data hhom F.centerFixedPointFree

/-- A dihedral Hall--Berger description of the mapped `2`-core
supplies the complete half-density datum.  The sharp rotation-orbit
comparison is intrinsic and includes the `D₈` edge. -/
theorem twoCoreSymplecticTypeHalfDensityData_of_dihedral
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (k : ℕ) (hk : 0 < k)
    (e :
      ((pCore 2 K).map K.subtype) ≃*
        DihedralGroup (4 * k)) :
    TwoCoreSymplecticTypeHalfDensityData K := by
  let P := (pCore 2 K).map K.subtype
  let F :=
    mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  change
    2 * (activePrimeOrderElements 2 P).card ≤
          r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d
  exact
    dihedral_halfDensity
      P F.pGroup hrTwo hd hk e
        F.centerFixedPointFree

/-- A semidihedral Hall--Berger description of the mapped `2`-core
supplies the complete half-density datum.  Unlike the mixed case, no
auxiliary square-degree parameter is needed. -/
theorem twoCoreSymplecticTypeHalfDensityData_of_semidihedral
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (k : ℕ) (hk : 0 < k)
    (presentation :
      IsSemidihedralPresentation
        ((pCore 2 K).map K.subtype) k) :
    TwoCoreSymplecticTypeHalfDensityData K := by
  let P := (pCore 2 K).map K.subtype
  let F :=
    mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  change
    2 * (activePrimeOrderElements 2 P).card ≤
          r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d
  exact
    semidihedral_halfDensity
      P F.pGroup hrTwo hd hk presentation
        F.centerFixedPointFree

/-- The central-commutator Hall--Berger branch supplies half-density in
every odd-characteristic module.  The sharp `F₃²` edge is discharged by
`card_activePrimeOrderElements_two_le_four_of_centralCommutator_f3Plane`. -/
theorem
    twoCoreSymplecticTypeHalfDensityData_of_centralCommutator
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcomm :
      HasCentralCommutatorOfOrderTwo
        ((pCore 2 K).map K.subtype)) :
    TwoCoreSymplecticTypeHalfDensityData K := by
  let P := (pCore 2 K).map K.subtype
  let F :=
    mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  have hcomparison :=
    centralCommutator_representationComparison
      hrTwo hd P F.pGroup hcomm F.hall
        F.centerFixedPointFree
  have hactive :
      2 * (activePrimeOrderElements 2 P).card ≤
        r ^ d - 1 :=
    active_halfDensity_of_centralCommutator_representationComparison
      P hcomm F.hall F.centerFixedPointFree
        hcomparison
  have hdeven : Even d :=
    even_dimension_of_centralCommutator
      hrTwo P hcomm F.centerFixedPointFree
  change
    2 * (activePrimeOrderElements 2 P).card ≤
          r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d
  refine ⟨hactive, ?_⟩
  intro g hg
  exact
    activeInvolution_fixedVectorSet_sq_le_of_centralCommutator
      hdeven P hcomm F.centerFixedPointFree g hg

/-! ## The fixed-space cycle and active-involution envelope -/

/-- The existing operator-valued cycle theorem supplies the required
half-dimensional fixed-space bound for an involution once the relevant
commutator-cycle witnesses have been constructed inside the `2`-core.

This theorem is classification-free.  In the Hall central-commutator
branch the witnesses and active count are supplied by the theorem above;
the lower-level cycle interface remains useful for other noncommuting
branches before their structure has been identified. -/
theorem fixedVectorSet_sq_le_of_central_involution_cycle
    (hdeven : Even d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (C : CenterFixedPointFreeAction r d P)
    (x y : P) (z : Subgroup.center P)
    (hzNe : z ≠ 1) (hzSq : z ^ 2 = 1)
    (hxy : x * y = z.1 * y * x) :
    (fixedVectorSet x.1).ncard *
        (fixedVectorSet x.1).ncard ≤
      r ^ d := by
  have hxyGL :
      x.1 * y.1 = z.1.1 * y.1 * x.1 := by
    exact congrArg Subtype.val hxy
  have hxzGL : Commute x.1 z.1.1 := by
    have hxzP : x * z.1 = z.1 * x :=
      Subgroup.mem_center_iff.mp z.2 x
    exact congrArg Subtype.val hxzP
  have hzyGL : Commute z.1.1 y.1 := by
    have hyzP : y * z.1 = z.1 * y :=
      Subgroup.mem_center_iff.mp z.2 y
    exact (congrArg Subtype.val hyzP).symm
  have hzSqGL : z.1.1 ^ 2 = 1 := by
    simpa using congrArg (fun w : Subgroup.center P ↦ w.1.1) hzSq
  have hnonzero :
      (nonzeroFixedVectorSet x.1).ncard ≤
        r ^ (d / 2) - 1 := by
    apply
      ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_GL_fixedPointFree_cycle
        (by norm_num : 0 < 2) x.1 y.1 z.1.1
        hxyGL hxzGL hzyGL hzSqGL
    intro k hkPos hkLt v hv
    have hk : k = 1 := by omega
    subst k
    simpa only [pow_one] using C.fixedPointFree z hzNe v hv
  have hfixed :
      (fixedVectorSet x.1).ncard ≤ r ^ (d / 2) := by
    rw [ncard_nonzeroFixedVectorSet] at hnonzero
    have hcardPos : 0 < (fixedVectorSet x.1).ncard := by
      rw [Set.ncard_pos]
      exact ⟨0, by simp [fixedVectorSet]⟩
    have hpowPos : 0 < r ^ (d / 2) :=
      pow_pos (Fact.out : Nat.Prime r).pos _
    omega
  have hsquare :
      r ^ (d / 2) * r ^ (d / 2) = r ^ d := by
    rw [← pow_add]
    congr 1
    have := Nat.two_mul_div_two_of_even hdeven
    omega
  calc
    (fixedVectorSet x.1).ncard *
          (fixedVectorSet x.1).ncard ≤
        r ^ (d / 2) * r ^ (d / 2) :=
      Nat.mul_le_mul hfixed hfixed
    _ = r ^ d := hsquare

/-- An active-involution envelope reduces the exact reserve datum to a
pure numerical joint inequality.

The `2`-core bad locus is bounded by

`1 + a * (f - 1)`,

where `a` bounds the active involutions and `f` bounds each diagonal fixed
rectangle.  The final hypothesis keeps the odd-row loci actual, so it
retains all correlations needed in the sharp small cases. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_activeInvolutionEnvelope
    (hhalf : TwoCoreSymplecticTypeHalfDensityData K)
    (a f : ℕ)
    (hactive :
      (activePrimeOrderElements 2
        ((pCore 2 K).map K.subtype)).card ≤ a)
    (hfixed :
      ∀ g ∈ activePrimeOrderElements 2
          ((pCore 2 K).map K.subtype),
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤ f)
    (hjoint :
      ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
        (∀ i, Nat.Prime (p i)) →
        Function.Injective p →
        (∀ i, p i ≠ r) →
        ∀ (i₂ : I), p i₂ = 2 →
          (∑ i,
              if p i = 2 then
                1 + a * (f - 1)
              else
                (nonregularVectors
                  (diagonalMappedPCore (K := K) (p i))).ncard) +
              2 * Nat.card
                (diagonalMappedPCore (K := K) 2) <
            r ^ (2 * d)) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  let P := (pCore 2 K).map K.subtype
  have hP : IsPGroup 2 P :=
    (pCore_isPGroup 2 K).map K.subtype
  have hbad :
      (nonregularVectors
        (diagonalMappedPCore (K := K) 2)).ncard ≤
        1 + a * (f - 1) := by
    rw [ncard_nonregular_diagonalMappedPCore_eq_affineBadSet]
    exact
      ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
        P hP a f hactive hfixed
  refine
    { halfDensity := hhalf
      distinguishedTwo := ?_ }
  intro I _ p hp hinj hcross i₂ hi₂
  let actual : I → ℕ := fun i ↦
    (nonregularVectors
      (diagonalMappedPCore (K := K) (p i))).ncard
  let envelope : I → ℕ := fun i ↦
    if p i = 2 then 1 + a * (f - 1) else actual i
  have hpoint : ∀ i, actual i ≤ envelope i := by
    intro i
    by_cases hi : p i = 2
    · simpa [actual, envelope, hi] using hbad
    · simp [envelope, hi]
  have hsum :
      (∑ i, actual i) ≤ ∑ i, envelope i :=
    Finset.sum_le_sum fun i _hi ↦ hpoint i
  have hbound :=
    hjoint p hp hinj hcross i₂ hi₂
  change (∑ i, actual i) +
      2 * Nat.card
        (diagonalMappedPCore (K := K) 2) <
    r ^ (2 * d)
  exact (Nat.add_le_add_right hsum _).trans_lt
    (by simpa [envelope, actual] using hbound)

/-! ## Complete commuting two-core branch -/

/-- A fixed-point-free action has no active elements of prime order. -/
private theorem activePrimeOrderElements_eq_empty_of_fixedPointFreeOffZero
    {R V : Type*}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (q : ℕ)
    (P : Subgroup (LinearMap.GeneralLinearGroup R V))
    [Fintype P]
    (hfp : FixedPointFreeOffZero P) :
    activePrimeOrderElements q P = ∅ := by
  classical
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨g, hg⟩
  obtain ⟨_horder, hgActive⟩ :=
    (mem_activePrimeOrderElements q P g).mp hg
  obtain ⟨hgNe, v, hvFix, hvNe⟩ :=
    (mem_nonzeroFixingElements P g).mp hgActive
  exact hvNe (hfp g hgNe v hvFix)

/-- If the mapped `2`-core is commuting, all exact two-orbit reserve data
is automatic.

The `2`-core then acts fixed-point-freely, so its doubled bad locus costs at
most one point and its order divides `r^d - 1`.  The odd rows satisfy

`2 * B_odd ≤ r^d * (r^d - 1)`.

These three estimates give the strict joint budget in every positive
dimension over an odd prime field, including the small case `r^d = 3`. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_quasiprimitive_of_commuting
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcomm : IsCommutingPrimeCore 2 K) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  classical
  let P :=
    (pCore 2 K).map K.subtype
  let D₂ :=
    (nonregularVectors
      (diagonalMappedPCore (K := K) 2)).ncard
  let C₂ :=
    Nat.card (diagonalMappedPCore (K := K) 2)
  let N := r ^ d
  have hfp : FixedPointFreeOffZero P :=
    pCore_fixedPointFree_of_quasiprimitive_of_commuting
      (Fact.out : Nat.Prime r) Nat.prime_two hrTwo.symm hqp hcomm
  have hactive :
      activePrimeOrderElements 2 P = ∅ :=
    activePrimeOrderElements_eq_empty_of_fixedPointFreeOffZero
      2 P hfp
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
    rw [ncard_nonregular_diagonalMappedPCore_eq_affineBadSet]
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
      (diagonalMappedPCore (K := K) (p i))).ncard
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
    simpa [Bodd, f, O, pO, N] using h
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

/-- The commuting mapped `2`-core branch of the recursively stable leaf is
fully unconditional. -/
theorem
    commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_oddChar_of_commutingTwoCore
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcomm : IsCommutingPrimeCore 2 K) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
      r (Fin d → ZMod r) K :=
  commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_quasiprimitive_of_oddChar.{uI}
    hrTwo hd hqp
      (oddCharacteristicTwoCoreTwoOrbitReserveData_of_quasiprimitive_of_commuting.{uI}
        hrTwo hd hqp hcomm)

end LisiSabatini
