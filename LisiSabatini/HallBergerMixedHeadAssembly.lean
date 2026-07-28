module

public import LisiSabatini.HallBergerCyclicHeadUniformInversion
public import LisiSabatini.HallBergerExtraspecialHeadAdjustment
public import LisiSabatini.HallBergerMixedDataAssembly

/-!
# Assembling the mixed Hall--Berger head

In the noncyclic Frattini-centralizer branch, choose the internal
extraspecial factor `E₀` and correct the cyclic-head coset representative
on the right by an element of its ambient image.  The corrected element
centralizes that image and remains outside the Frattini centralizer.

The internal residual is the center of the Frattini centralizer, hence is
generated ambiently by the distinguished rotation.  The corrected coset
and that rotation therefore form a maximal-class head which commutes with
the extraspecial factor, and the two factors generate the ambient group.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

namespace HallBergerCyclicHeadSeed

variable {G : Type u} [Group G] [Finite G]

/-- The noncyclic Hall--Berger branch assembles into the corrected mixed
maximal-class shape. -/
theorem nonempty_mixedShape_of_internal_extraspecial_cyclic_residual
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (seed : HallBergerCyclicHeadSeed G)
    (E₀ : Subgroup (frattiniCentralizer G))
    (hE₀ : IsExtraspecial 2 E₀)
    (hFactor : IsInternalCentralFactor E₀)
    (hResidualCyclic :
      IsCyclic
        (Subgroup.centralizer
          (E₀ : Set (frattiniCentralizer G)))) :
    Nonempty (HallBergerTwoCoreShape G) := by
  let C : Subgroup G :=
    frattiniCentralizer G
  let F : Subgroup G :=
    E₀.map C.subtype
  let eF : E₀ ≃* F :=
    Subgroup.equivMapOfInjective
      E₀ C.subtype Subtype.coe_injective
  have hF : IsExtraspecial 2 F :=
    hE₀.of_mulEquiv eF
  have hFC : F ≤ C :=
    Subgroup.map_subtype_le E₀
  have hrotationCenter :
      seed.rotation ∈ characteristicCenterImage C := by
    rw [← seed.rotation_generates_centerImage]
    exact Subgroup.mem_zpowers seed.rotation
  obtain ⟨c, hcCentral, hcOutside, _hcRotation⟩ :=
    hE₀.exists_hallBerger_right_adjustment_of_nested_extraspecial
      hG2 hBKN E₀ seed.coset
        seed.coset_not_mem_frattiniCentralizer
        seed.rotation hrotationCenter
  let adjusted : G :=
    seed.coset * (c : G)⁻¹
  let adjustedSeed : HallBergerCyclicHeadSeed G :=
    seed.replaceCoset hG2 adjusted hcOutside
  let H : Subgroup G :=
    Subgroup.zpowers seed.rotation ⊔
      Subgroup.zpowers adjusted
  let cyclicData : CyclicMaximalTwoGroupData H :=
    adjustedSeed.cyclicMaximalTwoGroupData
  have hH2 : IsPGroup 2 H :=
    adjustedSeed.headSubgroup_isPGroup hG2
  let head : BergerMaximalClassHead H :=
    Classical.choice
      (cyclicData.maximalClassHead hH2)
  have hrotationCentralizesF :
      seed.rotation ∈
        Subgroup.centralizer (F : Set G) := by
    have hrotationCentralizesC :
        seed.rotation ∈
          Subgroup.centralizer (C : Set G) := by
      rw [characteristicCenterImage_eq_inf_centralizer]
        at hrotationCenter
      exact hrotationCenter.2
    rw [Subgroup.mem_centralizer_iff]
    intro x hxF
    exact
      Subgroup.mem_centralizer_iff.mp
        hrotationCentralizesC x (hFC hxF)
  have hHCentralizesF :
      H ≤ Subgroup.centralizer (F : Set G) := by
    change
      Subgroup.zpowers seed.rotation ⊔
          Subgroup.zpowers adjusted ≤
        Subgroup.centralizer (F : Set G)
    exact sup_le
      (Subgroup.zpowers_le_of_mem
        hrotationCentralizesF)
      (Subgroup.zpowers_le_of_mem
        hcCentral)
  have hcomm :
      ∀ (x : F) (y : H),
        (x : G) * (y : G) =
          (y : G) * (x : G) := by
    intro x y
    exact hHCentralizesF y.2 x x.2
  let D : Subgroup C :=
    Subgroup.centralizer (E₀ : Set C)
  have hDcenter :
      D = Subgroup.center C :=
    centralizer_eq_center_of_isInternalCentralFactor_of_isCyclic
      E₀ hFactor hResidualCyclic
  have hFCenterGenerate :
      F ⊔ characteristicCenterImage C = C := by
    calc
      F ⊔ characteristicCenterImage C =
          E₀.map C.subtype ⊔
            D.map C.subtype := by
        rw [hDcenter]
        rfl
      _ = (E₀ ⊔ D).map C.subtype :=
        (Subgroup.map_sup E₀ D C.subtype).symm
      _ = (⊤ : Subgroup C).map C.subtype := by
        rw [hFactor.generate]
      _ = C.subtype.range :=
        (MonoidHom.range_eq_map C.subtype).symm
      _ = C :=
        Subgroup.range_subtype C
  have hFRotationGenerate :
      F ⊔ Subgroup.zpowers seed.rotation = C := by
    rw [seed.rotation_generates_centerImage]
    exact hFCenterGenerate
  have hindex :
      C.index = 2 := by
    simpa only [C] using
      seed.frattiniCentralizer_index_eq_two hG2
  have hCAdjustedGenerate :
      C ⊔ Subgroup.zpowers adjusted = ⊤ := by
    have hgenerateAdjusted :=
      adjustedSeed.frattiniCentralizer_sup_zpowers_eq_top_of_index_two
        (show (frattiniCentralizer G).index = 2 from hindex)
    change
      frattiniCentralizer G ⊔
          Subgroup.zpowers adjusted =
        ⊤ at hgenerateAdjusted
    exact hgenerateAdjusted
  have hgenerate :
      F ⊔ H = ⊤ := by
    calc
      F ⊔ H =
          (F ⊔ Subgroup.zpowers seed.rotation) ⊔
            Subgroup.zpowers adjusted := by
        change
          F ⊔
              (Subgroup.zpowers seed.rotation ⊔
                Subgroup.zpowers adjusted) =
            (F ⊔ Subgroup.zpowers seed.rotation) ⊔
              Subgroup.zpowers adjusted
        exact (sup_assoc _ _ _).symm
      _ = C ⊔ Subgroup.zpowers adjusted := by
        rw [hFRotationGenerate]
      _ = ⊤ := hCAdjustedGenerate
  have hcenterImageLePhi :
      characteristicCenterImage F ≤ frattini G := by
    intro z hz
    unfold characteristicCenterImage at hz
    rw [← hF.commutator_eq_center,
      Subgroup.map_subtype_commutator] at hz
    exact
      (commutator_le_frattini_of_isPGroup
        Nat.prime_two hG2)
        (Subgroup.commutator_mono le_top le_top hz)
  have hcenterLe :
      characteristicCenterImage F ≤ H := by
    calc
      characteristicCenterImage F ≤ frattini G :=
        hcenterImageLePhi
      _ = Subgroup.zpowers (seed.rotation ^ 2) :=
        seed.frattini_eq_rotationSquare
      _ ≤ Subgroup.zpowers seed.rotation :=
        Subgroup.zpowers_le_of_mem
          (Subgroup.npow_mem_zpowers seed.rotation 2)
      _ ≤ H := by
        change
          Subgroup.zpowers seed.rotation ≤
            Subgroup.zpowers seed.rotation ⊔
              Subgroup.zpowers adjusted
        exact le_sup_left
  let mixed : BergerMixedCentralProductData G :=
    bergerMixedCentralProductDataOfCommute
      F H hF head hcomm hgenerate hcenterLe
  exact ⟨.mixedMaximalClass mixed⟩

end HallBergerCyclicHeadSeed

end LisiSabatini
