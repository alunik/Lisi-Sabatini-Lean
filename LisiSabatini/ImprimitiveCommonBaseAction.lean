import LisiSabatini.ImprimitiveBaseComponents

/-!
# The common base action of an imprimitive linear group

The componentwise base constructions restrict the imprimitive action to one
normal component before taking its block-permutation kernel.  Recursive NCAS
needs a different viewpoint: first take the base kernel of the common action,
then retain every component as a normal subgroup of that single group and
map all of them into one common local image.

This file constructs that common action intrinsically.  The block factors are
crossed homomorphisms on the whole imprimitive group, but become honest group
homomorphisms on the common permutation kernel; the homomorphism laws are
derived directly from `action_apply`.
-/

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-! ## One common block-permutation kernel -/

/-- The base group of the common imprimitive action: the kernel of its action
on the block system. -/
def commonBaseKernel (D : ImprimitiveLinearActionData K L) : Subgroup K :=
  D.blockPerm.ker

@[simp]
theorem mem_commonBaseKernel_iff
    (D : ImprimitiveLinearActionData K L) (g : K) :
    g ∈ D.commonBaseKernel ↔ D.blockPerm g = 1 :=
  Iff.rfl

/-- The common base kernel is normal in the common imprimitive action. -/
theorem commonBaseKernel_normal
    (D : ImprimitiveLinearActionData K L) :
    D.commonBaseKernel.Normal :=
  D.blockPerm.normal_ker

/-- On the common base kernel, the local factor at a fixed block is an honest
group homomorphism into the supplied local group. -/
def commonBaseBlockLinear
    (D : ImprimitiveLinearActionData K L) (i : I) :
    D.commonBaseKernel →* L where
  toFun g := D.blockLinear g.1 i
  map_one' := D.blockLinear_one i
  map_mul' := by
    intro g h
    change D.blockLinear (g.1 * h.1) i = _
    rw [D.blockLinear_mul]
    rw [show D.blockPerm g.1 = 1 from g.2]
    rfl

/-- The common block homomorphism viewed in the ambient local general linear
group. -/
def commonBaseBlockLinearGL
    (D : ImprimitiveLinearActionData K L) (i : I) :
    D.commonBaseKernel →* LinearMap.GeneralLinearGroup R W :=
  L.subtype.comp (D.commonBaseBlockLinear i)

/-- The single common local action at block `i`, retained inside the supplied
local colour group `L`. -/
def commonBaseLocalImage
    (D : ImprimitiveLinearActionData K L) (i : I) : Subgroup L :=
  (D.commonBaseBlockLinear i).range

/-! ## Normal components inside the common base and local actions -/

/-- The part of an internal component `H ≤ K` lying in the common base
kernel, regarded as a subgroup of that common kernel. -/
def componentInCommonBaseKernel
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    Subgroup D.commonBaseKernel :=
  H.comap D.commonBaseKernel.subtype

/-- Normality of an internal component is retained after intersecting with
the common base kernel. -/
theorem componentInCommonBaseKernel_normal
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : H.Normal) :
    (D.componentInCommonBaseKernel H).Normal :=
  Subgroup.Normal.comap hH D.commonBaseKernel.subtype

/-- Intersecting an internal `p`-component with the common base kernel
preserves the `p`-group property. -/
theorem componentInCommonBaseKernel_isPGroup
    {p : ℕ} (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : IsPGroup p H) :
    IsPGroup p (D.componentInCommonBaseKernel H) :=
  hH.comap_subtype

/-- The local image of the base part of `H`, regarded internally as a
subgroup of the one common local image. -/
def componentBaseImageInCommonLocal
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    Subgroup (D.commonBaseLocalImage i) :=
  (D.componentInCommonBaseKernel H).map
    (D.commonBaseBlockLinear i).rangeRestrict

/-- Component base images are normal in the common local image. -/
theorem componentBaseImageInCommonLocal_normal
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : H.Normal) (i : I) :
    (D.componentBaseImageInCommonLocal H i).Normal := by
  exact Subgroup.Normal.map
    (D.componentInCommonBaseKernel_normal H hH)
    (D.commonBaseBlockLinear i).rangeRestrict
    (D.commonBaseBlockLinear i).rangeRestrict_surjective

/-- Component base images retain their matching prime inside the common local
image. -/
theorem componentBaseImageInCommonLocal_isPGroup
    {p : ℕ} (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : IsPGroup p H) (i : I) :
    IsPGroup p (D.componentBaseImageInCommonLocal H i) := by
  exact (D.componentInCommonBaseKernel_isPGroup H hH).map
    (D.commonBaseBlockLinear i).rangeRestrict

/-! ## Comparison with the componentwise concrete construction -/

/-- Send the base part of `H` inside the common kernel to the kernel obtained
by first restricting the action to the concrete ambient copy of `H`. -/
def componentInCommonBaseKernelToComponentBaseKernel
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    D.componentInCommonBaseKernel H →* D.componentBaseKernel H where
  toFun g :=
    ⟨⟨(g.1.1 : K),
        Subgroup.mem_map.mpr ⟨g.1.1, g.2, rfl⟩⟩,
      g.1.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The internal and concrete versions of the component base kernel are the
same group: the canonical comparison map is onto (and it is visibly
injective as an inclusion into the ambient general linear group). -/
theorem componentInCommonBaseKernelToComponentBaseKernel_surjective
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    Function.Surjective
      (D.componentInCommonBaseKernelToComponentBaseKernel H) := by
  intro g
  obtain ⟨h, hh, hval⟩ := Subgroup.mem_map.mp g.1.2
  have hcommon : restrictedAmbientToCommon H g.1 = h := by
    apply Subtype.ext
    exact hval.symm
  have hbase : D.blockPerm h = 1 := by
    rw [← hcommon]
    exact g.2
  let b : D.commonBaseKernel := ⟨h, hbase⟩
  let a : D.componentInCommonBaseKernel H := ⟨b, hh⟩
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact hval

/-- The comparison between the internal and concrete component base kernels
is injective. -/
theorem componentInCommonBaseKernelToComponentBaseKernel_injective
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    Function.Injective
      (D.componentInCommonBaseKernelToComponentBaseKernel H) := by
  intro a b hab
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun z : D.componentBaseKernel H ↦
      (((z.1 : restrictedAmbient H) :
        LinearMap.GeneralLinearGroup R (I → W))))
    hab

/-- Multiplicative equivalence between the common-kernel and
restrict-first presentations of a component's base group. -/
def componentInCommonBaseKernelEquivComponentBaseKernel
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    D.componentInCommonBaseKernel H ≃* D.componentBaseKernel H :=
  MulEquiv.ofBijective
    (D.componentInCommonBaseKernelToComponentBaseKernel H)
    ⟨D.componentInCommonBaseKernelToComponentBaseKernel_injective H,
      D.componentInCommonBaseKernelToComponentBaseKernel_surjective H⟩

/-- The comparison of base kernels intertwines the two concrete block-linear
homomorphisms. -/
@[simp]
theorem componentBaseBlockLinearGL_comparison
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I)
    (g : D.componentInCommonBaseKernel H) :
    D.componentBaseBlockLinearGL H i
        (D.componentInCommonBaseKernelToComponentBaseKernel H g) =
      D.commonBaseBlockLinearGL i g.1 :=
  rfl

/-- Mapping the new internal component image through the common local image
and then into the ambient local general linear group recovers exactly the
older concrete `componentBaseBlockImage`. -/
theorem map_componentBaseImageInCommonLocal_subtype_eq_componentBaseBlockImage
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    ((D.componentBaseImageInCommonLocal H i).map
        (D.commonBaseLocalImage i).subtype).map L.subtype =
      D.componentBaseBlockImage H i := by
  ext x
  constructor
  · intro hx
    obtain ⟨xL, hxL, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨xC, hxC, rfl⟩ := Subgroup.mem_map.mp hxL
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hxC
    exact MonoidHom.mem_range.mpr
      ⟨D.componentInCommonBaseKernelToComponentBaseKernel H ⟨g, hg⟩, rfl⟩
  · intro hx
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨a, rfl⟩ :=
      D.componentInCommonBaseKernelToComponentBaseKernel_surjective H g
    let y : D.commonBaseLocalImage i :=
      (D.commonBaseBlockLinear i).rangeRestrict a.1
    apply Subgroup.mem_map.mpr
    refine ⟨(y : L), ?_, rfl⟩
    apply Subgroup.mem_map.mpr
    refine ⟨y, ?_, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a.1, a.2, rfl⟩

end ImprimitiveLinearActionData

end LisiSabatini
