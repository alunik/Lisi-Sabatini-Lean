module

public import LisiSabatini.ImprimitiveBaseComponents

/-!
# Block-indexed base groups with a common colour group

The intrinsic base image of one imprimitive component need not be the same on
every block.  This file sharpens the separate base--colour interface once
more: coordinate `i` is tested only against its own subgroup `B i ≤ L`, while
the full group `L` continues to define the orbit colours seen by the top.

The final specialization uses the canonical block images of
`ImprimitiveBaseComponents`.  Their prime-power property is therefore
available without enlarging them to a basis-dependent common envelope.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uJ uR uW

variable {I : Type uI} {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

/-- Every factor of a block-permutation-kernel element belongs to the base
subgroup assigned to its target block. -/
def BlockPermKernelFactorsInAt
    {H : Subgroup (LinearMap.GeneralLinearGroup R (I → W))}
    {L : Subgroup (LinearMap.GeneralLinearGroup R W)}
    (D : ImprimitiveLinearActionData H L) (B : I → Subgroup L) : Prop :=
  ∀ (g : D.blockPerm.ker) (i : I), D.blockLinear g.1 i ∈ B i

/-- Coordinatewise regularity for block-indexed base groups kills the kernel
of the top map on the point stabilizer. -/
theorem pointStabilizerBlockPerm_ker_eq_bot_of_indexedBase_regular
    {H : Subgroup (LinearMap.GeneralLinearGroup R (I → W))}
    {L : Subgroup (LinearMap.GeneralLinearGroup R W)}
    (D : ImprimitiveLinearActionData H L) (B : I → Subgroup L)
    (hkernel : BlockPermKernelFactorsInAt D B)
    (x : I → W)
    (hx : ∀ i, MulAction.stabilizer (B i) (x i) = ⊥) :
    (pointStabilizerBlockPerm D x).ker = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  change D.blockPerm g.1 = 1 at hg
  have hfix : g.1.1 • x = x :=
    MulAction.mem_stabilizer_iff.mp g.2
  have hlocal : ∀ i, D.blockLinear g.1 i = 1 := by
    intro i
    let b : B i :=
      ⟨D.blockLinear g.1 i, hkernel ⟨g.1, hg⟩ i⟩
    have hi := congrFun hfix i
    rw [D.action_apply, hg] at hi
    have hbmem : b ∈ MulAction.stabilizer (B i) (x i) := by
      apply MulAction.mem_stabilizer_iff.mpr
      simpa [b] using hi
    rw [hx i] at hbmem
    exact congrArg Subtype.val hbmem
  apply Subtype.ext
  apply Subtype.ext
  ext y i
  change (g.1.1 • y) i = y i
  rw [D.action_apply, hg, hlocal i]
  simp

/-- Injective form of the block-indexed base-kernel theorem. -/
theorem pointStabilizerBlockPerm_injective_of_indexedBase_regular
    {H : Subgroup (LinearMap.GeneralLinearGroup R (I → W))}
    {L : Subgroup (LinearMap.GeneralLinearGroup R W)}
    (D : ImprimitiveLinearActionData H L) (B : I → Subgroup L)
    (hkernel : BlockPermKernelFactorsInAt D B)
    (x : I → W)
    (hx : ∀ i, MulAction.stabilizer (B i) (x i) = ⊥) :
    Function.Injective (pointStabilizerBlockPerm D x) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact pointStabilizerBlockPerm_ker_eq_bot_of_indexedBase_regular
    D B hkernel x hx

/-- **Indexed-base/common-colour stabilizer reduction.**

The block-dependent groups `B i` kill the base kernel.  The full local group
`L` defines colours, so trivial intersection of its colour stabilizer with
the actual top image kills the remaining point stabilizer. -/
theorem stabilizer_eq_bot_of_indexedBase_regular_of_top_color_disjoint
    {H : Subgroup (LinearMap.GeneralLinearGroup R (I → W))}
    {L : Subgroup (LinearMap.GeneralLinearGroup R W)}
    (D : ImprimitiveLinearActionData H L) (B : I → Subgroup L)
    (hkernel : BlockPermKernelFactorsInAt D B)
    (x : I → W)
    (hbase : ∀ i, MulAction.stabilizer (B i) (x i) = ⊥)
    (htop : D.blockPerm.range ⊓ blockOrbitColorStabilizer L x = ⊥) :
    MulAction.stabilizer H x = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  let gs : MulAction.stabilizer H x := ⟨g, hg⟩
  have hperm_mem : D.blockPerm g ∈
      D.blockPerm.range ⊓ blockOrbitColorStabilizer L x := by
    exact ⟨⟨g, rfl⟩,
      blockPerm_mem_colorStabilizer_of_mem_pointStabilizer D x gs⟩
  rw [htop] at hperm_mem
  have hperm : pointStabilizerBlockPerm D x gs = 1 := hperm_mem
  have hgs : gs = 1 := by
    apply pointStabilizerBlockPerm_injective_of_indexedBase_regular
      D B hkernel x hbase
    simpa using hperm
  exact congrArg Subtype.val hgs

/-- Simultaneous affine form with block-dependent base subgroups and one
colour group per family member. -/
theorem exists_common_regular_translate_of_imprimitive_indexedBase_color
    [AddCommGroup W]
    (L : J → Subgroup (LinearMap.GeneralLinearGroup R W))
    (B : ∀ j, I → Subgroup (L j))
    (H : J → Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (D : ∀ j, ImprimitiveLinearActionData (H j) (L j))
    (hkernel : ∀ j, BlockPermKernelFactorsInAt (D j) (B j))
    (t : J → I → W)
    (hbaseTop : ∃ v : I → W, ∀ j,
      (∀ i, MulAction.stabilizer (B j i) ((v + t j) i) = ⊥) ∧
      (D j).blockPerm.range ⊓
          blockOrbitColorStabilizer (L j) (v + t j) = ⊥) :
    ∃ v : I → W, ∀ j,
      MulAction.stabilizer (H j) (v + t j) = ⊥ := by
  obtain ⟨v, hv⟩ := hbaseTop
  refine ⟨v, fun j ↦ ?_⟩
  exact stabilizer_eq_bot_of_indexedBase_regular_of_top_color_disjoint
    (D j) (B j) (hkernel j) (v + t j) (hv j).1 (hv j).2

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- The intrinsic image of a component's base kernel on block `i`, retained
inside the supplied local colour group `L`. -/
def componentBaseBlockImageInLocal
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    Subgroup L :=
  (D.componentBaseBlockLinear H i).range

/-- Intrinsic local base images preserve the prime-group property. -/
theorem componentBaseBlockImageInLocal_isPGroup
    {p : ℕ} (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : IsPGroup p H) (i : I) :
    IsPGroup p (D.componentBaseBlockImageInLocal H i) := by
  rw [componentBaseBlockImageInLocal, MonoidHom.range_eq_map]
  exact (D.componentBaseKernel_isPGroup H hH).to_subgroup
    (⊤ : Subgroup (D.componentBaseKernel H)) |>.map
      (D.componentBaseBlockLinear H i)

/-- The canonical block-indexed base images contain exactly the factors of
the restricted component's block-permutation kernel. -/
theorem restrictComponent_kernelFactorsIn_componentBaseBlockImages
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    BlockPermKernelFactorsInAt (D.restrictComponent H)
      (D.componentBaseBlockImageInLocal H) := by
  intro g i
  exact MonoidHom.mem_range.mpr ⟨g, rfl⟩

/-- Canonical indexed-base/common-colour criterion for one normal component.
Only the intrinsic prime-power block images must act regularly locally. -/
theorem restrictComponent_stabilizer_eq_bot_of_baseImages_regular_of_top_color_disjoint
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (x : I → W)
    (hbase : ∀ i,
      MulAction.stabilizer (D.componentBaseBlockImageInLocal H i) (x i) = ⊥)
    (htop : (D.restrictComponent H).blockPerm.range ⊓
        blockOrbitColorStabilizer L x = ⊥) :
    MulAction.stabilizer (restrictedAmbient H) x = ⊥ := by
  exact stabilizer_eq_bot_of_indexedBase_regular_of_top_color_disjoint
    (D.restrictComponent H) (D.componentBaseBlockImageInLocal H)
    (D.restrictComponent_kernelFactorsIn_componentBaseBlockImages H)
    x hbase htop

end ImprimitiveLinearActionData

end LisiSabatini
