module

public import LisiSabatini.ImprimitiveBundleAction
public import LisiSabatini.ImprimitiveCommonBaseAction

/-!
# Exact bundle-marker infrastructure used by the odd-order proof

This proof core contains the exact fibre description for a semiregular top
and the two local-image lemmas used to pass from ambient to intrinsic
block actions.  Higher-level marker constructions remain in the compatibility
module `ImprimitiveBundleMarker`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-! ## The exact fibre over one top orbit -/

/-- The common base image at block `i`, viewed in the ambient local general
linear group so that its vector orbits can be used directly. -/
def commonBaseLocalImageGL
    (D : ImprimitiveLinearActionData K L) (i : I) :
    Subgroup (LinearMap.GeneralLinearGroup R W) :=
  (D.commonBaseLocalImage i).map L.subtype

/-- The ambient common local image is equivalently the range of the common
block-linear homomorphism into `GL(W)`. -/
theorem commonBaseLocalImageGL_eq_range
    (D : ImprimitiveLinearActionData K L) (i : I) :
    D.commonBaseLocalImageGL i = (D.commonBaseBlockLinearGL i).range := by
  rw [commonBaseLocalImageGL, commonBaseLocalImage,
    commonBaseBlockLinearGL, MonoidHom.range_comp]

/-- The ambient image of one component inside the common local action.  The
two successive maps retain the normality statement internally while exposing
the actual linear action used by orbit avoidance. -/
def componentBaseImageInCommonLocalGL
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    Subgroup (LinearMap.GeneralLinearGroup R W) :=
  ((D.componentBaseImageInCommonLocal H i).map
      (D.commonBaseLocalImage i).subtype).map L.subtype

/-- The common-local presentation of a component has exactly the old
concrete block image as its ambient linear action. -/
theorem componentBaseImageInCommonLocalGL_eq_componentBaseBlockImage
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    D.componentBaseImageInCommonLocalGL H i =
      D.componentBaseBlockImage H i :=
  D.map_componentBaseImageInCommonLocal_subtype_eq_componentBaseBlockImage H i

/-- Taking the common base image after restricting to `H` recovers the
componentwise concrete base image. -/
theorem restrictComponent_commonBaseLocalImageGL_eq_componentBaseBlockImage
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    (D.restrictComponent H).commonBaseLocalImageGL i =
      D.componentBaseBlockImage H i := by
  rw [commonBaseLocalImageGL_eq_range, componentBaseBlockImage]
  congr 1

/-- The common-local action of a restricted component is its intrinsic image
inside the common local general linear group. -/
theorem restrictComponent_commonBaseLocalImageGL_eq_componentBaseImageInCommonLocalGL
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    (D.restrictComponent H).commonBaseLocalImageGL i =
      D.componentBaseImageInCommonLocalGL H i :=
  (D.restrictComponent_commonBaseLocalImageGL_eq_componentBaseBlockImage H i).trans
    (D.componentBaseImageInCommonLocalGL_eq_componentBaseBlockImage H i).symm

/-- **Exact bundle fibre lemma.**

If `g` and `h` carry the marker block `ω` to the same target `i`,
semiregularity of the top at `ω` forces their top permutations to agree.
Thus `h g⁻¹` lies in the common base kernel, and its block factor at `i`
carries the value transported by `g` to the value transported by `h`. -/
theorem sameBlockOrbit_commonBaseLocalImageGL_of_same_target
    (D : ImprimitiveLinearActionData K L)
    (ω i : I) (hsemi : IsSemiregularAt D.blockPerm.range ω)
    (g h : K)
    (hg : D.blockPerm g ω = i) (hh : D.blockPerm h ω = i)
    (c : W) :
    SameBlockOrbit (D.commonBaseLocalImageGL i)
      (D.bundleMap g (ω, c)).2 (D.bundleMap h (ω, c)).2 := by
  let τ : D.blockPerm.range :=
    ⟨D.blockPerm (g⁻¹ * h), ⟨g⁻¹ * h, rfl⟩⟩
  have hτfix : τ ∈ MulAction.stabilizer D.blockPerm.range ω := by
    apply MulAction.mem_stabilizer_iff.mpr
    change D.blockPerm (g⁻¹ * h) ω = ω
    simp only [map_mul, map_inv]
    change (D.blockPerm g).symm (D.blockPerm h ω) = ω
    rw [hh, ← hg]
    simp
  rw [hsemi] at hτfix
  have hker : D.blockPerm (g⁻¹ * h) = 1 :=
    congrArg Subtype.val hτfix
  have hperm : D.blockPerm g = D.blockPerm h := by
    apply eq_of_inv_mul_eq_one
    simpa only [map_mul, map_inv] using hker
  have hbperm : D.blockPerm (h * g⁻¹) = 1 := by
    simp only [map_mul, map_inv, hperm, mul_inv_cancel]
  let b : D.commonBaseKernel := ⟨h * g⁻¹, hbperm⟩
  let aL : D.commonBaseLocalImage i :=
    (D.commonBaseBlockLinear i).rangeRestrict b
  let a : D.commonBaseLocalImageGL i :=
    ⟨(aL : L), Subgroup.mem_map.mpr ⟨aL, aL.2, rfl⟩⟩
  refine ⟨a, ?_⟩
  have hbundle :
      D.bundleMap h (ω, c) =
        D.bundleMap (h * g⁻¹) (D.bundleMap g (ω, c)) := by
    rw [← D.bundleMap_mul]
    simp
  have hvalue := congrArg Prod.snd hbundle
  change (D.blockLinear (h * g⁻¹) i).1 •
      (D.bundleMap g (ω, c)).2 =
    (D.bundleMap h (ω, c)).2
  symm
  simpa [bundleMap, hbperm, hg] using hvalue

/-! ## From ambient block images to intrinsic local regularity -/

/-- The intrinsic local image in `L`, mapped to the ambient general linear
group, is exactly the concrete block image. -/
theorem map_componentBaseBlockImageInLocal_subtype_eq_componentBaseBlockImage
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    (D.componentBaseBlockImageInLocal H i).map L.subtype =
      D.componentBaseBlockImage H i := by
  rw [componentBaseBlockImageInLocal, componentBaseBlockImage,
    componentBaseBlockLinearGL, MonoidHom.range_comp]

/-- Regularity after embedding a subgroup of `L` into the ambient `GL(W)`
implies regularity for the intrinsic subgroup itself. -/
theorem stabilizer_eq_bot_of_map_local_subtype_stabilizer_eq_bot
    (B : Subgroup L) (x : W)
    (h : MulAction.stabilizer (B.map L.subtype) x = ⊥) :
    MulAction.stabilizer B x = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro b hb
  let bGL : B.map L.subtype :=
    ⟨(b.1 : L), Subgroup.mem_map.mpr ⟨b.1, b.2, rfl⟩⟩
  have hbGL : bGL ∈ MulAction.stabilizer (B.map L.subtype) x := by
    apply MulAction.mem_stabilizer_iff.mpr
    exact MulAction.mem_stabilizer_iff.mp hb
  rw [h] at hbGL
  have hbGLone : bGL = 1 := by simpa using hbGL
  have hval : ((b.1 : L) : LinearMap.GeneralLinearGroup R W) = 1 :=
    congrArg
      (fun z : B.map L.subtype ↦
        (z : LinearMap.GeneralLinearGroup R W)) hbGLone
  apply Subtype.ext
  apply Subtype.ext
  exact hval

/-- Ambient common-local regularity implies regularity for the intrinsic
component image in the supplied local group. -/
theorem componentBaseBlockImageInLocal_stabilizer_eq_bot_of_commonLocalGL
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) (x : W)
    (h : MulAction.stabilizer
      (D.componentBaseImageInCommonLocalGL H i) x = ⊥) :
    MulAction.stabilizer (D.componentBaseBlockImageInLocal H i) x = ⊥ := by
  apply stabilizer_eq_bot_of_map_local_subtype_stabilizer_eq_bot
  rw [D.map_componentBaseBlockImageInLocal_subtype_eq_componentBaseBlockImage]
  rw [← D.componentBaseImageInCommonLocalGL_eq_componentBaseBlockImage]
  exact h

/-- Common-local regularity and a trivial restricted top give regularity for
the whole restricted component.  This is the standard top-trivial branch of
the imprimitive stabilizer argument. -/
theorem restrictComponent_stabilizer_eq_bot_of_commonLocalGL_of_top_bot
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (x : I → W)
    (hbaseGL : ∀ i, MulAction.stabilizer
      (D.componentBaseImageInCommonLocalGL H i) (x i) = ⊥)
    (htop : (D.restrictComponent H).blockPerm.range = ⊥) :
    MulAction.stabilizer (restrictedAmbient H) x = ⊥ := by
  have hbase (i : I) :
      MulAction.stabilizer (D.componentBaseBlockImageInLocal H i) (x i) = ⊥ :=
    D.componentBaseBlockImageInLocal_stabilizer_eq_bot_of_commonLocalGL
      H i (x i) (hbaseGL i)
  apply stabilizer_eq_bot_of_indexedBase_regular_of_top_color_disjoint
    (D.restrictComponent H)
    (D.componentBaseBlockImageInLocal H)
    (D.restrictComponent_kernelFactorsIn_componentBaseBlockImages H)
    x hbase
  simp [htop]

end ImprimitiveLinearActionData

end LisiSabatini
