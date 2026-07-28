module

public import LisiSabatini.SchurCenterHalfOrbitCore
public import LisiSabatini.FiniteLinearSubgroup
public import LisiSabatini.OrbitAvoidingPaletteCore
public import LisiSabatini.PCore
public import LisiSabatini.CyclicCenterClassTwoTransport

/-!
# Core primitive-top control by local prime cores

At an imprimitive node, an intrinsic component image need not inherit the
cyclic-center structure of an ambient normal prime subgroup.  At a genuinely
quasiprimitive local leaf there is a different route: every normal
`q`-subgroup is contained in the local `q`-core.  Both its nonregular locus
and each of its orbits are therefore contained in the corresponding objects
for the prime core.

This file formalizes that domination directly.  In particular,
one-orbit-avoiding common translated regularity is downward monotone in the
acting groups, so a certificate for the local prime cores applies to every
family of normal prime components without transporting any structural
property to their images.

The final section supplies a sharp family certificate on the branch where
all active prime cores in the selected family are odd cyclic-center
class-two groups.  Quasiprimitivity and the full-center Schur row generate
the required fixed-spectrum and half-orbit bounds internally.  Commuting
prime cores are intentionally not hidden in this branch: a fixed-point-free
cyclic core can have one orbit containing every nonzero vector, so prime-core
orbit domination alone cannot give the required forbidden-orbit conclusion
without an additional mixed-family argument.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uJ uR uV

/-! ## Downward monotonicity of orbits and orbit avoidance -/

variable {R : Type uR} {V : Type uV}
variable [Semiring R] [AddCommGroup V] [Module R V]

/-- Enlarging the acting linear group enlarges every point orbit. -/
theorem orbit_subset_of_subgroup_le
    {A B : Subgroup (LinearMap.GeneralLinearGroup R V)}
    (hAB : A ≤ B) (v : V) :
    MulAction.orbit A v ⊆ MulAction.orbit B v := by
  intro w hw
  obtain ⟨a, rfl⟩ := hw
  exact ⟨⟨a.1, hAB a.2⟩, rfl⟩

/-- Cardinality form of orbit monotonicity on a finite module. -/
theorem ncard_orbit_mono
    [Finite V]
    {A B : Subgroup (LinearMap.GeneralLinearGroup R V)}
    (hAB : A ≤ B) (v : V) :
    (MulAction.orbit A v).ncard ≤ (MulAction.orbit B v).ncard :=
  Set.ncard_le_ncard (orbit_subset_of_subgroup_le hAB v) (Set.toFinite _)

/-- Enlarging the acting group enlarges the block-orbit equivalence
relation. -/
theorem sameBlockOrbit_mono
    {A B : Subgroup (LinearMap.GeneralLinearGroup R V)}
    (hAB : A ≤ B) {v w : V} :
    SameBlockOrbit A v w → SameBlockOrbit B v w := by
  rintro ⟨a, ha⟩
  exact ⟨⟨a.1, hAB a.2⟩, ha⟩

namespace OrbitAvoidingCommonRegularTranslates

/-- One-orbit avoidance is downward monotone in every acting subgroup.

Regularity for the larger group implies regularity for the smaller one,
while avoiding the larger distinguished orbit implies avoiding the smaller
orbit. -/
theorem mono
    {J : Type uJ}
    {A B : J → Subgroup (LinearMap.GeneralLinearGroup R V)}
    (hAB : ∀ j, A j ≤ B j)
    (hB : OrbitAvoidingCommonRegularTranslates B) :
    OrbitAvoidingCommonRegularTranslates A := by
  intro j₀ t c
  obtain ⟨v, hregular, havoid⟩ := hB j₀ t c
  refine ⟨v, ?_, ?_⟩
  · intro j
    by_contra hne
    have hlarge : v + t j ∈ nonregularVectors (B j) :=
      nonregularVectors_mono (hAB j) hne
    exact hlarge (hregular j)
  · intro horbit
    exact havoid (sameBlockOrbit_mono (hAB j₀) horbit)

end OrbitAvoidingCommonRegularTranslates

/-! ## Prime-core domination -/

/-- The orbit of a normal `q`-subgroup, after mapping to the concrete
general linear group, is contained in the orbit of the mapped local
`q`-core. -/
theorem orbit_map_normalPSubgroup_subset_pCore
    {K : Subgroup (LinearMap.GeneralLinearGroup R V)}
    {q : ℕ} {A : Subgroup K}
    (hAq : IsPGroup q A) (hAn : A.Normal) (v : V) :
    MulAction.orbit (A.map K.subtype) v ⊆
      MulAction.orbit ((pCore q K).map K.subtype) v :=
  orbit_subset_of_subgroup_le
    (map_normalPSubgroup_le_map_pCore hAq hAn) v

/-- Cardinality form of the normal-prime-subgroup orbit domination. -/
theorem ncard_orbit_map_normalPSubgroup_le_pCore
    [Finite V]
    {K : Subgroup (LinearMap.GeneralLinearGroup R V)}
    {q : ℕ} {A : Subgroup K}
    (hAq : IsPGroup q A) (hAn : A.Normal) (v : V) :
    (MulAction.orbit (A.map K.subtype) v).ncard ≤
      (MulAction.orbit ((pCore q K).map K.subtype) v).ncard :=
  ncard_orbit_mono (map_normalPSubgroup_le_map_pCore hAq hAn) v

/-- A one-orbit-avoidance certificate for a family of local prime cores
automatically applies to arbitrary normal prime subgroups with the same
labels. -/
theorem orbitAvoidingCommonRegularTranslates_of_pCore
    {J : Type uJ}
    {K : Subgroup (LinearMap.GeneralLinearGroup R V)}
    (p : J → ℕ)
    (hcore : OrbitAvoidingCommonRegularTranslates
      (fun j ↦ (pCore (p j) K).map K.subtype))
    (A : J → Subgroup K)
    (hAn : ∀ j, (A j).Normal)
    (hAq : ∀ j, IsPGroup (p j) (A j)) :
    OrbitAvoidingCommonRegularTranslates
      (fun j ↦ (A j).map K.subtype) :=
  hcore.mono (fun j ↦
    map_normalPSubgroup_le_map_pCore (hAq j) (hAn j))

/-! ## Full Schur rows on quasiprimitive prime cores -/

local instance finiteConcreteLinearSubgroupForPrimeCoreDomination
    (r d : ℕ) [NeZero r]
    (P : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))) : Finite P :=
  finite_linearSubgroup_of_finite P

/-- Quasiprimitivity and cyclic-center structure generate the enhanced
Stone--von Neumann row for a mapped prime core, including divisibility by
the order of its entire center.

The representation is first taken on the abstract normal subgroup
`pCore q K`, where quasiprimitivity supplies homogeneity.  The center order
and structural rank are then transported through its faithful map into the
ambient general linear group. -/
theorem exists_pCore_schurDegree_fullCenter_row_of_quasiprimitive
    {r d q : ℕ} [Fact r.Prime] [NeZero r]
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hPbar : IsOddCyclicCenterClassTwo q
      ((pCore q K).map K.subtype)) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧
      Nat.card (Subgroup.center ((pCore q K).map K.subtype)) ∣
        r ^ a - 1 ∧
      q ∣ r ^ a - 1 ∧
      d = a * q ^ hPbar.cyclicCenterStructuralRank * b := by
  let P := pCore q K
  let Pbar := P.map K.subtype
  let e : P ≃* Pbar :=
    Subgroup.equivMapOfInjective P K.subtype Subtype.coe_injective
  let hP : IsOddCyclicCenterClassTwo q P :=
    hPbar.of_mulEquiv e.symm
  have hrank : hP.cyclicCenterStructuralRank =
      hPbar.cyclicCenterStructuralRank :=
    hPbar.cyclicCenterStructuralRank_of_mulEquiv e.symm
  have hd : 0 < d := by
    apply Nat.pos_of_ne_zero
    intro hd0
    subst d
    apply hPbar.noncommutative
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro v
    exact Subsingleton.elim _ _
  let rho : Representation (ZMod r) P (Fin d → ZMod r) :=
    (linearSubgroupRepresentation K).comp P.subtype
  have hfaith : Function.Injective rho :=
    (linearSubgroupRepresentation_faithful K).comp P.subtype_injective
  let H : HomogeneousDimensionData r d rho :=
    homogeneousDimensionData rho hd (hqp.2 P inferInstance)
  obtain ⟨a, b, ha, hb, hcenter, hq, _hend, hdim⟩ :=
    H.exists_schurDegree_fullCenter_row rho hfaith hP
  have hcenterCard : Nat.card (Subgroup.center P) =
      Nat.card (Subgroup.center Pbar) :=
    Nat.card_congr (Subgroup.centerCongr e)
  have hcenterBar : Nat.card (Subgroup.center Pbar) ∣ r ^ a - 1 := by
    rwa [hcenterCard] at hcenter
  refine ⟨a, b, ha, hb, ?_, hq, ?_⟩
  · simpa only [Pbar] using hcenterBar
  · simpa only [hrank] using hdim

end LisiSabatini
