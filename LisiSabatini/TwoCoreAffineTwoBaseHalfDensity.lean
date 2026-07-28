module

public import LisiSabatini.AffineTwoBaseTranslates
public import LisiSabatini.ActiveFixedSpaceSpectrum
public import LisiSabatini.QuasiprimitivePrimeCoreCore

/-!
# A prime-order envelope for affine two-base bad loci

For a finite `p`-group, every nontrivial point stabilizer contains an
element of order `p`.  Thus the affine two-base bad locus can be counted
using only the active elements of order `p`, rather than all active
nonidentity elements.

The specialization `p = 2` is the counting interface needed for a
noncommuting normal `2`-core.  This file deliberately assumes the two
structural estimates which a classification of finite `2`-groups of
symplectic type must provide:

* a bound on the number of active involutions; and
* a bound on their fixed spaces.

No classification statement is asserted here.

The relevant published structure input is Yang--Vasil'ev--Vdovin,
*Regular orbits of finite primitive solvable groups, III*, J. Algebra 590
(2022), Theorem 2.2: the Fitting subgroup of a faithful irreducible
quasiprimitive solvable linear group has the central-product form `F = EU`,
with `U` cyclic and `E` a direct product of extraspecial groups.  Their
Lemma 2.4(1) gives the half-dimensional fixed-space bound for involutions
in `F`.  The active-involution estimates are treated in the `A₁` cases in
the proof of their Theorem 3.1.  The sharper uniform inequality encoded by
`TwoCoreSymplecticTypeHalfDensityData` below is not imported as a theorem
from that paper; it remains an explicit hypothesis.

For the underlying classification of `2`-groups of symplectic type, see
T. R. Berger, *Hall-Higman type theorems I*, Canad. J. Math. 26 (1974),
Lemma 1.1 (citing Huppert, *Endliche Gruppen I*, Theorem III.13.10).
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

/-- The nonzero pairs fixed diagonally by one linear automorphism. -/
def primeOrderNonzeroFixedPairSet
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (g : LinearMap.GeneralLinearGroup R V) : Set (V × V) :=
  (fixedVectorSet g ×ˢ fixedVectorSet g) \ {(0, 0)}

/-- A nonzero diagonal fixed rectangle has `|Fix(g)|² - 1` points. -/
theorem ncard_primeOrderNonzeroFixedPairSet
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [Finite V]
    (g : LinearMap.GeneralLinearGroup R V) :
    (primeOrderNonzeroFixedPairSet g).ncard =
      (fixedVectorSet g).ncard * (fixedVectorSet g).ncard - 1 := by
  rw [primeOrderNonzeroFixedPairSet,
    Set.ncard_diff_singleton_of_mem]
  · rw [Set.ncard_prod]
  · simp [fixedVectorSet]

/-- Nonidentity elements of order `p` which fix a nonzero vector. -/
def activePrimeOrderElements
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (p : ℕ)
    (A : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype A] :
    Finset A :=
  (nonzeroFixingElements A).filter fun g ↦ orderOf g = p

@[simp]
theorem mem_activePrimeOrderElements
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (p : ℕ)
    (A : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype A]
    (g : A) :
    g ∈ activePrimeOrderElements p A ↔
      orderOf g = p ∧ g ∈ nonzeroFixingElements A := by
  classical
  simp [activePrimeOrderElements, and_comm]

/-- The untranslated bad locus of a finite `p`-group is covered by the
zero pair and the nonzero fixed rectangles of its active order-`p`
elements. -/
theorem affineTwoBaseBadSet_zero_subset_activePrimeOrder_fixedPairSpectrum
    {r p : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V]
    [Fact p.Prime]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Fintype A] (hA : IsPGroup p A) :
    affineTwoBaseBadSet A 0 0 ⊆
      {(0, 0)} ∪
        ⋃ g : {g : A // g ∈ activePrimeOrderElements p A},
          primeOrderNonzeroFixedPairSet g.1.1 := by
  classical
  intro z hz
  by_cases hz0 : z = (0, 0)
  · subst z
    simp
  · obtain ⟨g, hgOrder, hgFirst, hgSecond⟩ :=
      (mem_affineTwoBaseBadSet_iff_exists_primeOrder_fixed
        A hA 0 0 z).mp hz
    have hgNe : g ≠ 1 := by
      intro hgOne
      have : orderOf g = 1 := orderOf_eq_one_iff.mpr hgOne
      exact (Fact.out : p.Prime).ne_one (hgOrder.symm.trans this)
    have hgActive : g ∈ nonzeroFixingElements A := by
      rw [mem_nonzeroFixingElements]
      refine ⟨hgNe, ?_⟩
      by_cases hzFirst : z.1 = 0
      · have hzSecond : z.2 ≠ 0 := by
          intro h
          apply hz0
          exact Prod.ext hzFirst h
        exact
          ⟨z.2,
            (mem_nonzeroFixedVectorSet g.1 z.2).2
              ⟨by simpa using hgSecond, hzSecond⟩⟩
      · exact
          ⟨z.1,
            (mem_nonzeroFixedVectorSet g.1 z.1).2
              ⟨by simpa using hgFirst, hzFirst⟩⟩
    have hgFiltered : g ∈ activePrimeOrderElements p A := by
      rw [mem_activePrimeOrderElements]
      exact ⟨hgOrder, hgActive⟩
    apply Set.mem_union_right
    apply Set.mem_iUnion.mpr
    refine ⟨⟨g, hgFiltered⟩, ?_⟩
    rw [primeOrderNonzeroFixedPairSet]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_fixedVectorSet]
      simpa using hgFirst
    · rw [mem_fixedVectorSet]
      simpa using hgSecond
    · simpa using hz0

/-- Direct rectangle-envelope estimate using only active elements of prime
order and a uniform bound on the cardinality of a fixed rectangle. -/
theorem ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
    {r p : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    [Fact p.Prime]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Fintype A] (hA : IsPGroup p A) (a f : ℕ)
    (hactive : (activePrimeOrderElements p A).card ≤ a)
    (hfixed : ∀ g ∈ activePrimeOrderElements p A,
      (fixedVectorSet g.1).ncard *
        (fixedVectorSet g.1).ncard ≤ f) :
    (affineTwoBaseBadSet A 0 0).ncard ≤
      1 + a * (f - 1) := by
  classical
  calc
    (affineTwoBaseBadSet A 0 0).ncard ≤
        ({(0, 0)} ∪
          ⋃ g : {g : A // g ∈ activePrimeOrderElements p A},
            primeOrderNonzeroFixedPairSet g.1.1).ncard :=
      Set.ncard_le_ncard
        (affineTwoBaseBadSet_zero_subset_activePrimeOrder_fixedPairSpectrum
          A hA)
        (Set.toFinite _)
    _ ≤ 1 +
        ∑ g : {g : A // g ∈ activePrimeOrderElements p A},
          (primeOrderNonzeroFixedPairSet g.1.1).ncard := by
      calc
        _ ≤ ({(0, 0)} : Set (V × V)).ncard +
            (⋃ g : {g : A // g ∈ activePrimeOrderElements p A},
              primeOrderNonzeroFixedPairSet g.1.1).ncard :=
          Set.ncard_union_le _ _
        _ ≤ 1 +
            ∑ g : {g : A // g ∈ activePrimeOrderElements p A},
              (primeOrderNonzeroFixedPairSet g.1.1).ncard := by
          simp only [Set.ncard_singleton]
          exact Nat.add_le_add_left (Set.ncard_iUnion_le_of_fintype _) 1
    _ ≤ 1 + (activePrimeOrderElements p A).card *
          (f - 1) := by
      apply Nat.add_le_add_left
      calc
        ∑ g : {g : A // g ∈ activePrimeOrderElements p A},
            (primeOrderNonzeroFixedPairSet g.1.1).ncard ≤
            ∑ _g : {g : A // g ∈ activePrimeOrderElements p A},
              (f - 1) := by
          apply Finset.sum_le_sum
          intro g _hg
          rw [ncard_primeOrderNonzeroFixedPairSet]
          exact Nat.sub_le_sub_right (hfixed g.1 g.2) 1
        _ = (activePrimeOrderElements p A).card *
            (f - 1) := by
          simp
    _ ≤ 1 + a * (f - 1) :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_right (f - 1) hactive) 1

/-- Direct rectangle-envelope estimate in terms of a uniform fixed-space
cardinality bound. -/
theorem ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixed_sq
    {r p : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    [Fact p.Prime]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Fintype A] (hA : IsPGroup p A) (a c : ℕ)
    (hactive : (activePrimeOrderElements p A).card ≤ a)
    (hfixed : ∀ g ∈ activePrimeOrderElements p A,
      (fixedVectorSet g.1).ncard ≤ c) :
    (affineTwoBaseBadSet A 0 0).ncard ≤
      1 + a * (c * c - 1) := by
  apply
    ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
      A hA a (c * c) hactive
  intro g hg
  exact Nat.mul_le_mul (hfixed g hg) (hfixed g hg)

/-- A structural active-involution/fixed-space budget implies the desired
strict half-density estimate. -/
theorem two_mul_ncard_affineTwoBaseBadSet_zero_lt_of_activePrimeOrder_budget
    {r p d a c : ℕ} [Fact r.Prime] [Fact p.Prime]
    (A : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype A] (hA : IsPGroup p A)
    (hactive : (activePrimeOrderElements p A).card ≤ a)
    (hfixed : ∀ g ∈ activePrimeOrderElements p A,
      (fixedVectorSet g.1).ncard ≤ c)
    (hbudget : 2 * (1 + a * (c * c - 1)) < r ^ (2 * d)) :
    2 * (affineTwoBaseBadSet A 0 0).ncard < r ^ (2 * d) := by
  calc
    2 * (affineTwoBaseBadSet A 0 0).ncard ≤
        2 * (1 + a * (c * c - 1)) :=
      Nat.mul_le_mul_left 2
        (ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixed_sq
          A hA a c hactive hfixed)
    _ < r ^ (2 * d) := hbudget

/-- If every active prime-order element fixes at most a half-dimensional
subspace, it is enough to inject two copies of the active prime-order set
into the nonzero ambient vectors.  For `p = 2`, these are precisely the two
classification estimates naturally stated for active involutions. -/
theorem two_mul_ncard_affineTwoBaseBadSet_zero_lt_of_activePrimeOrder_half
    {r p d : ℕ} [Fact r.Prime] [Fact p.Prime]
    (A : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype A] (hA : IsPGroup p A)
    (hrTwo : r ≠ 2) (hd : 0 < d) (hdeven : Even d)
    (hactive :
      2 * (activePrimeOrderElements p A).card ≤ r ^ d - 1)
    (hfixed : ∀ g ∈ activePrimeOrderElements p A,
      (fixedVectorSet g.1).ncard ≤ r ^ (d / 2)) :
    2 * (affineTwoBaseBadSet A 0 0).ncard < r ^ (2 * d) := by
  let N := (activePrimeOrderElements p A).card
  let q := r ^ d
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
  have hqPos : 0 < q := by omega
  have hN : 2 * N ≤ q - 1 := by
    simpa only [N, q] using hactive
  have hbudgetQ : 2 * (1 + N * (q - 1)) < q * q := by
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hqPos
    nlinarith
  have hfixedSquare :
      r ^ (d / 2) * r ^ (d / 2) = q := by
    dsimp only [q]
    rw [← pow_add]
    congr 1
    have := Nat.two_mul_div_two_of_even hdeven
    omega
  have htopSquare : r ^ (2 * d) = q * q := by
    dsimp only [q]
    rw [← pow_add]
    congr 1
    omega
  apply
    two_mul_ncard_affineTwoBaseBadSet_zero_lt_of_activePrimeOrder_budget
      A hA
      (a := (activePrimeOrderElements p A).card)
      (c := r ^ (d / 2))
      (le_refl _) hfixed
  simpa only [N, q, hfixedSquare, htopSquare] using hbudgetQ

/-! ## The explicit mapped two-core publication boundary -/

/-- The two numerical estimates still needed from the symplectic-type
description of a mapped normal `2`-core.

The first bounds the active involutions by half of the nonzero ambient
vectors.  The second says that each active involution's diagonal fixed
rectangle has at most `r ^ d` points.  For an odd-characteristic
half-dimensional fixed space, the second inequality is an equality. -/
def TwoCoreSymplecticTypeHalfDensityData
    {r d : ℕ} [Fact r.Prime]
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype ((pCore 2 K).map K.subtype)] : Prop :=
  2 *
      (activePrimeOrderElements 2
        ((pCore 2 K).map K.subtype)).card ≤
      r ^ d - 1 ∧
    ∀ g ∈ activePrimeOrderElements 2
        ((pCore 2 K).map K.subtype),
      (fixedVectorSet g.1).ncard *
          (fixedVectorSet g.1).ncard ≤
        r ^ d

/-- Conditional half-density for the mapped normal `2`-core of a faithful
irreducible quasiprimitive action.  All group classification content is
kept in the explicit `TwoCoreSymplecticTypeHalfDensityData` hypothesis. -/
theorem two_mul_ncard_affineTwoBaseBadSet_mapped_pCore_two_lt_of_quasiprimitive
    {r d : ℕ} [Fact r.Prime]
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    [Fintype ((pCore 2 K).map K.subtype)]
    (_hqp : IsQuasiprimitiveLinearAction r d K)
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hdata : TwoCoreSymplecticTypeHalfDensityData K) :
    2 *
        (affineTwoBaseBadSet
          ((pCore 2 K).map K.subtype) 0 0).ncard <
      r ^ (2 * d) := by
  let P := (pCore 2 K).map K.subtype
  let N := (activePrimeOrderElements 2 P).card
  let q := r ^ d
  have hP : IsPGroup 2 P := by
    exact (pCore_isPGroup 2 K).map K.subtype
  have hactive : 2 * N ≤ q - 1 := by
    exact hdata.1
  have hfixed :
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤ q := by
    exact hdata.2
  have hbad :
      (affineTwoBaseBadSet P 0 0).ncard ≤
        1 + N * (q - 1) := by
    exact
      ncard_affineTwoBaseBadSet_zero_le_one_add_activePrimeOrder_mul_fixedPair
        P hP N q (le_refl _) hfixed
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
  have hqPos : 0 < q := by omega
  have hbudget : 2 * (1 + N * (q - 1)) < q * q := by
    have hsub : q - 1 + 1 = q := Nat.sub_add_cancel hqPos
    nlinarith
  have htopSquare : r ^ (2 * d) = q * q := by
    dsimp only [q]
    rw [← pow_add]
    congr 1
    omega
  calc
    2 * (affineTwoBaseBadSet P 0 0).ncard ≤
        2 * (1 + N * (q - 1)) :=
      Nat.mul_le_mul_left 2 hbad
    _ < q * q := hbudget
    _ = r ^ (2 * d) := htopSquare.symm

end LisiSabatini
