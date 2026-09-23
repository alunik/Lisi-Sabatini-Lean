module

public import LisiSabatini.LinearImprimitivityExtraction
public import LisiSabatini.BlockStabilizerLocalAction
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Common coordinates on the specified Clifford blocks

This adapter retains the actual orbit of the chosen block.  It does not
pass to a maximal coarsening.  Transporters identify every block with the
original base, and the existing internal-direct-sum machinery produces the
imprimitive action data.  The local image comparison is exact, and linear
coordinate changes preserve literal stabilizer containment.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

namespace LinearImprimitivitySystem

variable {R V U : Type*} [Ring R] [AddCommGroup V] [Module R V]
  [AddCommGroup U] [Module R U]

/-- Linear conjugation transports the entire point stabilizer, not only
the assertion that it is trivial. -/
theorem map_stabilizer_linearConjugation_eq
    (e : V ≃ₗ[R] U) (A : Subgroup (LinearMap.GeneralLinearGroup R V)) (x : V) :
    (MulAction.stabilizer A x).map
        ((LinearMap.GeneralLinearGroup.congrLinearEquiv e).subgroupMap A).toMonoidHom =
      MulAction.stabilizer
        (A.map (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom) (e x) := by
  let c := LinearMap.GeneralLinearGroup.congrLinearEquiv e
  let f : A ≃* A.map c.toMonoidHom := c.subgroupMap A
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    change c a.1 • e x = e x
    rw [congrLinearEquiv_smul]
    exact congrArg e (MulAction.mem_stabilizer_iff.mp ha)
  · intro hg
    refine Subgroup.mem_map.mpr ⟨f.symm g, ?_, f.apply_symm_apply g⟩
    apply MulAction.mem_stabilizer_iff.mpr
    apply e.injective
    have hfg : c (f.symm g).1 = g.1 :=
      congrArg Subtype.val (f.apply_symm_apply g)
    calc
      e ((f.symm g).1 • x) = c (f.symm g).1 • e x :=
        (congrLinearEquiv_smul e (f.symm g).1 x).symm
      _ = g.1 • e x := by rw [hfg]
      _ = e x := MulAction.mem_stabilizer_iff.mp hg

/-- Literal containment of reference stabilizers is invariant under a
linear coordinate change. -/
theorem stabilizer_linearConjugation_le_iff
    (e : V ≃ₗ[R] U) (A : Subgroup (LinearMap.GeneralLinearGroup R V)) (x y : V) :
    MulAction.stabilizer
        (A.map (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom) (e x) ≤
      MulAction.stabilizer
        (A.map (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom) (e y) ↔
      MulAction.stabilizer A x ≤ MulAction.stabilizer A y := by
  rw [← map_stabilizer_linearConjugation_eq e A x,
    ← map_stabilizer_linearConjugation_eq e A y]
  constructor
  · intro h a ha
    let f := (LinearMap.GeneralLinearGroup.congrLinearEquiv e).subgroupMap A
    have hfa : f a ∈ (MulAction.stabilizer A x).map f.toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp (h hfa)
    have hba' : b = a := f.injective hba
    simpa only [hba'] using hb
  · exact fun h ↦ Subgroup.map_mono h

/-- Linear coordinate changes preserve the actual orbit relation. -/
theorem sameBlockOrbit_linearConjugation_iff
    (e : V ≃ₗ[R] U) (A : Subgroup (LinearMap.GeneralLinearGroup R V)) (x y : V) :
    SameBlockOrbit (A.map (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom)
      (e x) (e y) ↔ SameBlockOrbit A x y := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨a, ha, hag⟩ := Subgroup.mem_map.mp g.2
    refine ⟨⟨a, ha⟩, ?_⟩
    change a • x = y
    apply e.injective
    change g.1 • e x = e y at hg
    rw [← hag] at hg
    change LinearMap.GeneralLinearGroup.congrLinearEquiv e a • e x = e y at hg
    rw [congrLinearEquiv_smul] at hg
    exact hg
  · rintro ⟨a, ha⟩
    refine ⟨(LinearMap.GeneralLinearGroup.congrLinearEquiv e).subgroupMap A a, ?_⟩
    change LinearMap.GeneralLinearGroup.congrLinearEquiv e a.1 • e x = e y
    rw [congrLinearEquiv_smul]
    exact congrArg e ha

end LinearImprimitivitySystem

namespace LinearImprimitivityExtractionWitness

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
  {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

/-- A selected transporter from the original base block to the given
member of its actual orbit. -/
def blockTransporter (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) : K :=
  Classical.choose
    (W.toLinearImprimitivitySystem.isIndexPretransitive_of_irreducible
      W.irreducible W.baseIndex i)

@[simp]
theorem blockTransporter_maps (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) :
    W.toLinearImprimitivitySystem.blockPerm (W.blockTransporter i) W.baseIndex = i :=
  Classical.choose_spec
    (W.toLinearImprimitivitySystem.isIndexPretransitive_of_irreducible
      W.irreducible W.baseIndex i)

/-- Restriction of the transporter to the original base block. -/
def baseBlockEquiv (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) : W.base ≃ₗ[R] i.1 :=
  (W.blockTransporter i).1.toLinearEquiv.ofSubmodules W.base i.1
    ((W.toLinearImprimitivitySystem.map_block
      (W.blockTransporter i) W.baseIndex).trans
      (congrArg W.toLinearImprimitivitySystem.block (W.blockTransporter_maps i)))

/-- All local spaces are identified with the original base. -/
def baseCoordinates (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) :
    W.toLinearImprimitivitySystem.block i ≃ₗ[R] W.base :=
  (W.baseBlockEquiv i).symm

/-- Product coordinates retaining precisely the specified orbit blocks. -/
def blockCoordinates (W : LinearImprimitivityExtractionWitness K) :
    V ≃ₗ[R] (SubmoduleOrbitIndex K W.base → W.base) :=
  W.toLinearImprimitivitySystem.productCoordinates W.baseCoordinates

/-- The original action in the common-base product coordinates. -/
abbrev blockCoordinateGroup (W : LinearImprimitivityExtractionWitness K) :
    Subgroup (LinearMap.GeneralLinearGroup R (SubmoduleOrbitIndex K W.base → W.base)) :=
  W.toLinearImprimitivitySystem.coordinateSubgroup W.baseCoordinates

/-- The faithful group isomorphism induced by the coordinate change. -/
def blockCoordinateGroupEquiv (W : LinearImprimitivityExtractionWitness K) :
    K ≃* W.blockCoordinateGroup :=
  W.toLinearImprimitivitySystem.coordinateSubgroupEquiv W.baseCoordinates

/-- Monomial action data on the original block set. -/
abbrev blockCoordinateAction (W : LinearImprimitivityExtractionWitness K) :
    ImprimitiveLinearActionData W.blockCoordinateGroup
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W.base)) :=
  W.toLinearImprimitivitySystem.imprimitiveLinearActionData W.baseCoordinates

@[simp]
theorem blockCoordinateAction_blockPerm (W : LinearImprimitivityExtractionWitness K)
    (g : K) :
    W.blockCoordinateAction.blockPerm (W.blockCoordinateGroupEquiv g) =
      W.toLinearImprimitivitySystem.blockPerm g := by
  change W.toLinearImprimitivitySystem.blockPerm
    ((W.toLinearImprimitivitySystem.coordinateSubgroupEquiv W.baseCoordinates).symm
      (W.toLinearImprimitivitySystem.coordinateSubgroupEquiv W.baseCoordinates g)) = _
  rw [MulEquiv.symm_apply_apply]

/-- In particular the original prime-order top is unchanged. -/
theorem blockCoordinateAction_blockPerm_range (W : LinearImprimitivityExtractionWitness K) :
    W.blockCoordinateAction.blockPerm.range =
      W.toLinearImprimitivitySystem.blockPerm.range :=
  W.toLinearImprimitivitySystem.coordinateLinearBlockSystem_blockPerm_range W.baseCoordinates

/-- An internal component transported to the product action. -/
abbrev coordinateComponent (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) : Subgroup W.blockCoordinateGroup :=
  W.toLinearImprimitivitySystem.coordinateInternalSubgroup W.baseCoordinates H

/-- The top of a transported component is its original permutation image.
This preserves the active prime and every trivial-top assertion. -/
theorem coordinateComponent_top_range (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) :
    (W.blockCoordinateAction.restrictComponent (W.coordinateComponent H)).blockPerm.range =
      H.map W.toLinearImprimitivitySystem.blockPerm := by
  rw [← W.blockCoordinateAction.componentTopImage_map_subtype_eq_restrictComponent_range]
  change ((H.map W.blockCoordinateGroupEquiv.toMonoidHom).map
    W.blockCoordinateAction.blockPerm.rangeRestrict).map
      W.blockCoordinateAction.blockPerm.range.subtype = _
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro g
  exact W.blockCoordinateAction_blockPerm g

theorem coordinateComponent_normal (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) (hH : H.Normal) : (W.coordinateComponent H).Normal :=
  hH.map W.blockCoordinateGroupEquiv.toMonoidHom W.blockCoordinateGroupEquiv.surjective

theorem coordinateComponent_isPGroup (W : LinearImprimitivityExtractionWitness K)
    {p : ℕ} (H : Subgroup K) (hH : IsPGroup p H) : IsPGroup p (W.coordinateComponent H) :=
  hH.map W.blockCoordinateGroupEquiv.toMonoidHom

/-- The irreducible local block-stabilizer image, in the common base. -/
abbrev coordinateLocalGroup (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) :
    Subgroup (LinearMap.GeneralLinearGroup R W.base) :=
  W.toLinearImprimitivitySystem.blockStabilizerCoordinateLocalImage i (W.baseCoordinates i)

/-- The local base part of a component, retained internally in the
irreducible local group. -/
abbrev coordinateLocalComponent (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) (i : SubmoduleOrbitIndex K W.base) :
    Subgroup (W.coordinateLocalGroup i) :=
  W.toLinearImprimitivitySystem.componentBaseImageInBlockStabilizerCoordinates
    H i (W.baseCoordinates i)

/-- The intrinsic component supplied to local induction has exactly the
ambient image expected by the composition theorem. -/
theorem coordinateLocalComponent_map_eq (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) (i : SubmoduleOrbitIndex K W.base) :
    (W.coordinateLocalComponent H i).map (W.coordinateLocalGroup i).subtype =
      W.blockCoordinateAction.componentBaseImageInCommonLocalGL
        (W.coordinateComponent H) i :=
  W.toLinearImprimitivitySystem
    |>.map_componentBaseImageInBlockStabilizerCoordinates_eq_commonLocalGL
      W.baseCoordinates H i

theorem coordinateLocalGroup_irreducible (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) :
    LinearImprimitivitySystem.IsIrreducible (W.coordinateLocalGroup i) :=
  W.toLinearImprimitivitySystem.blockStabilizerCoordinateLocalImage_isIrreducible
    W.irreducible i (W.baseCoordinates i)

theorem coordinateLocalGroup_nilpotent [Group.IsNilpotent K]
    (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) : Group.IsNilpotent (W.coordinateLocalGroup i) := by
  let S := W.toLinearImprimitivitySystem
  let : Group.IsNilpotent (S.blockStabilizerLocalImage i) :=
    Group.nilpotent_of_surjective (S.blockStabilizerLocalRangeHom i)
      (S.blockStabilizerLocalRangeHom_surjective i)
  exact Group.nilpotent_of_surjective
    (S.blockStabilizerLocalImageCoordinateEquiv i (W.baseCoordinates i)).toMonoidHom
    (S.blockStabilizerLocalImageCoordinateEquiv i (W.baseCoordinates i)).surjective

theorem coordinateLocalGroup_finite [Finite K]
    (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) : Finite (W.coordinateLocalGroup i) := by
  let S := W.toLinearImprimitivitySystem
  let : Finite (S.blockStabilizerLocalImage i) := S.blockStabilizerLocalImage_finite i
  exact Finite.of_surjective
    (S.blockStabilizerLocalImageCoordinateEquiv i (W.baseCoordinates i))
    (S.blockStabilizerLocalImageCoordinateEquiv i (W.baseCoordinates i)).surjective

/-- Common local coordinates do not change the faithful local group order. -/
theorem coordinateLocalGroup_card (W : LinearImprimitivityExtractionWitness K)
    (i : SubmoduleOrbitIndex K W.base) :
    Nat.card (W.coordinateLocalGroup i) =
      Nat.card (W.toLinearImprimitivitySystem.blockStabilizerLocalImage i) :=
  Nat.card_congr
    (W.toLinearImprimitivitySystem.blockStabilizerLocalImageCoordinateEquiv
      i (W.baseCoordinates i)).symm.toEquiv

/-- Cross characteristic passes to the coordinated local group. -/
theorem coordinateLocalGroup_coprime (W : LinearImprimitivityExtractionWitness K)
    {r : ℕ} (hcop : r.Coprime (Nat.card K)) (i : SubmoduleOrbitIndex K W.base) :
    r.Coprime (Nat.card (W.coordinateLocalGroup i)) := by
  rw [W.coordinateLocalGroup_card]
  exact hcop.of_dvd_right
    ((Subgroup.card_range_dvd
      (W.toLinearImprimitivitySystem.blockStabilizerLocalHom i)).trans
      (W.toLinearImprimitivitySystem.blockStabilizer i).card_subgroup_dvd_card)

theorem coordinateLocalComponent_normal (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) (hH : H.Normal) (i : SubmoduleOrbitIndex K W.base) :
    (W.coordinateLocalComponent H i).Normal :=
  W.toLinearImprimitivitySystem.componentBaseImageInBlockStabilizerCoordinates_normal
    H hH i (W.baseCoordinates i)

theorem coordinateLocalComponent_isPGroup (W : LinearImprimitivityExtractionWitness K)
    {p : ℕ} (H : Subgroup K) (hH : IsPGroup p H)
    (i : SubmoduleOrbitIndex K W.base) : IsPGroup p (W.coordinateLocalComponent H i) :=
  W.toLinearImprimitivitySystem.componentBaseImageInBlockStabilizerCoordinates_isPGroup
    H hH i (W.baseCoordinates i)

theorem coordinateLocalComponent_ne_bot_iff (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) (i : SubmoduleOrbitIndex K W.base) :
    W.coordinateLocalComponent H i ≠ ⊥ ↔
      W.toLinearImprimitivitySystem.componentBaseImageInBlockStabilizerLocal H i ≠ ⊥ := by
  apply not_congr
  exact Subgroup.map_eq_bot_iff_of_injective _
    (W.toLinearImprimitivitySystem.blockStabilizerLocalImageCoordinateEquiv
      i (W.baseCoordinates i)).injective

/-- A component known intrinsically to be a local Sylow subgroup remains
a Sylow subgroup after the common-base coordinate change. -/
theorem coordinateLocalComponent_isSylow [Finite K]
    (W : LinearImprimitivityExtractionWitness K) {p : ℕ} (hp : p.Prime)
    (H : Subgroup K) (i : SubmoduleOrbitIndex K W.base)
    (hSylow : ∃ Q : Sylow p (W.toLinearImprimitivitySystem.blockStabilizerLocalImage i),
      (Q : Subgroup (W.toLinearImprimitivitySystem.blockStabilizerLocalImage i)) =
        W.toLinearImprimitivitySystem.componentBaseImageInBlockStabilizerLocal H i) :
    ∃ Q : Sylow p (W.coordinateLocalGroup i),
      (Q : Subgroup (W.coordinateLocalGroup i)) = W.coordinateLocalComponent H i := by
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (W.toLinearImprimitivitySystem.blockStabilizerLocalImage i) :=
    W.toLinearImprimitivitySystem.blockStabilizerLocalImage_finite i
  obtain ⟨Q, hQ⟩ := hSylow
  let e := W.toLinearImprimitivitySystem.blockStabilizerLocalImageCoordinateEquiv
    i (W.baseCoordinates i)
  refine ⟨Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (Q : Subgroup (W.toLinearImprimitivitySystem.blockStabilizerLocalImage i)).map
    e.toMonoidHom = _
  rw [hQ]
  rfl

/-- Mapping an internal component into the coordinate general linear
group agrees exactly with conjugating its original ambient image. -/
theorem coordinateComponent_map_subtype (W : LinearImprimitivityExtractionWitness K)
    (H : Subgroup K) :
    (W.coordinateComponent H).map W.blockCoordinateGroup.subtype =
      (H.map K.subtype).map
        (LinearMap.GeneralLinearGroup.congrLinearEquiv W.blockCoordinates).toMonoidHom := by
  change (H.map W.blockCoordinateGroupEquiv.toMonoidHom).map
    W.blockCoordinateGroup.subtype = _
  rw [Subgroup.map_map, Subgroup.map_map]
  rfl

/-- The containment condition on the distinguished component can be
proved in product coordinates and transported back unchanged. -/
theorem coordinateComponent_stabilizer_le_iff
    (W : LinearImprimitivityExtractionWitness K) (H : Subgroup K) (x y : V) :
    MulAction.stabilizer ((W.coordinateComponent H).map W.blockCoordinateGroup.subtype)
        (W.blockCoordinates x) ≤
      MulAction.stabilizer ((W.coordinateComponent H).map W.blockCoordinateGroup.subtype)
        (W.blockCoordinates y) ↔
      MulAction.stabilizer (H.map K.subtype) x ≤
        MulAction.stabilizer (H.map K.subtype) y := by
  rw [W.coordinateComponent_map_subtype]
  exact LinearImprimitivitySystem.stabilizer_linearConjugation_le_iff
    W.blockCoordinates (H.map K.subtype) x y

/-- Regularity of a component is unchanged by the common coordinates. -/
theorem coordinateComponent_stabilizer_eq_bot_iff
    (W : LinearImprimitivityExtractionWitness K) (H : Subgroup K) (x : V) :
    MulAction.stabilizer ((W.coordinateComponent H).map W.blockCoordinateGroup.subtype)
      (W.blockCoordinates x) = ⊥ ↔ MulAction.stabilizer (H.map K.subtype) x = ⊥ := by
  rw [W.coordinateComponent_map_subtype,
    ← LinearImprimitivitySystem.map_stabilizer_linearConjugation_eq]
  exact Subgroup.map_eq_bot_iff_of_injective _
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv W.blockCoordinates).subgroupMap
      (H.map K.subtype)).injective

/-- Marked component orbits are unchanged by the common coordinates. -/
theorem coordinateComponent_sameBlockOrbit_iff
    (W : LinearImprimitivityExtractionWitness K) (H : Subgroup K) (x y : V) :
    SameBlockOrbit ((W.coordinateComponent H).map W.blockCoordinateGroup.subtype)
      (W.blockCoordinates x) (W.blockCoordinates y) ↔
      SameBlockOrbit (H.map K.subtype) x y := by
  rw [W.coordinateComponent_map_subtype]
  exact LinearImprimitivitySystem.sameBlockOrbit_linearConjugation_iff
    W.blockCoordinates (H.map K.subtype) x y

/-- The original base of an imprimitivity witness is strictly smaller
than the ambient finite-dimensional vector space. -/
theorem base_finrank_lt {k X : Type*} [Field k] [AddCommGroup X] [Module k X]
    [FiniteDimensional k X] {K₀ : Subgroup (LinearMap.GeneralLinearGroup k X)}
    (W : LinearImprimitivityExtractionWitness K₀) :
    Module.finrank k W.base < Module.finrank k X := by
  simpa only [finrank_top] using
    Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr W.base_ne_top)

/-- The recursive local module has positive dimension. -/
theorem base_finrank_pos {k X : Type*} [Field k] [AddCommGroup X] [Module k X]
    [FiniteDimensional k X] {K₀ : Subgroup (LinearMap.GeneralLinearGroup k X)}
    (W : LinearImprimitivityExtractionWitness K₀) : 0 < Module.finrank k W.base := by
  let : Nontrivial W.base := Submodule.nontrivial_iff_ne_bot.mpr W.base_ne_bot
  exact Module.finrank_pos

end LinearImprimitivityExtractionWitness

end LisiSabatini
