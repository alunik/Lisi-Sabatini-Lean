module

public import LisiSabatini.ImprimitiveNormalComponentsCore
public import LisiSabatini.ImprimitiveBlockLinearCore

/-!
# Base components of an imprimitive normal component

For a component `H ≤ K` in a common imprimitive action, the kernel of its
restricted permutation action is the component's base group.  Although the
block factors in `ImprimitiveLinearActionData` form a crossed homomorphism in
general, their restriction to this kernel is an honest homomorphism on every
block.  This file constructs those homomorphisms and their concrete images in
the local general linear group.

All constructions are internal to the supplied action data.  In particular,
no wreath-product identification and no extra compatibility axiom for
`blockLinear` is assumed: the homomorphism laws are derived from
`action_apply`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-! ## The restricted base kernel -/

/-- The kernel of the block-permutation action after restricting the common
imprimitive action to `H`. -/
def componentBaseKernel
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    Subgroup (restrictedAmbient H) :=
  (D.restrictComponent H).blockPerm.ker

@[simp]
theorem mem_componentBaseKernel_iff
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (g : restrictedAmbient H) :
    g ∈ D.componentBaseKernel H ↔
      D.blockPerm (restrictedAmbientToCommon H g) = 1 :=
  Iff.rfl

/-- The restricted base kernel of a `p`-component is again a `p`-group. -/
theorem componentBaseKernel_isPGroup
    {p : ℕ} (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : IsPGroup p H) :
    IsPGroup p (D.componentBaseKernel H) := by
  have hrestricted : IsPGroup p (restrictedAmbient H) :=
    hH.map K.subtype
  exact hrestricted.to_subgroup (D.componentBaseKernel H)

/-! ## Blockwise homomorphisms on the base kernel -/

/-- On the block-permutation kernel, the local factor at a fixed block is a
group homomorphism. -/
def componentBaseBlockLinear
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    D.componentBaseKernel H →* L where
  toFun g := D.blockLinear (restrictedAmbientToCommon H g.1) i
  map_one' := D.blockLinear_one i
  map_mul' := by
    intro g h
    change D.blockLinear
        (restrictedAmbientToCommon H g.1 * restrictedAmbientToCommon H h.1) i = _
    rw [D.blockLinear_mul]
    rw [show D.blockPerm (restrictedAmbientToCommon H g.1) = 1 from g.2]
    rfl

/-- The blockwise base homomorphism, viewed in the concrete local general
linear group rather than the supplied envelope `L`. -/
def componentBaseBlockLinearGL
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    D.componentBaseKernel H →* LinearMap.GeneralLinearGroup R W :=
  L.subtype.comp (D.componentBaseBlockLinear H i)

/-- The concrete local image of the component base kernel on block `i`. -/
def componentBaseBlockImage
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    Subgroup (LinearMap.GeneralLinearGroup R W) :=
  (D.componentBaseBlockLinearGL H i).range

/-- Each concrete block image of a `p`-component base kernel is a
`p`-group. -/
theorem componentBaseBlockImage_isPGroup
    {p : ℕ} (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : IsPGroup p H) (i : I) :
    IsPGroup p (D.componentBaseBlockImage H i) := by
  rw [componentBaseBlockImage, MonoidHom.range_eq_map]
  exact (D.componentBaseKernel_isPGroup H hH).to_subgroup
    (⊤ : Subgroup (D.componentBaseKernel H)) |>.map
      (D.componentBaseBlockLinearGL H i)

/-! ## The diagonal base action and coordinate stabilizers -/

/-- On the base kernel there is no block movement: its action at `i` is
exactly its concrete local block homomorphism at `i`. -/
theorem componentBaseKernel_action_apply
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (g : D.componentBaseKernel H) (x : I → W) (i : I) :
    (g.1.1 • x) i = (D.componentBaseBlockLinearGL H i g) • x i := by
  have hi := D.action_apply (restrictedAmbientToCommon H g.1) x i
  have hperm :
      D.blockPerm (restrictedAmbientToCommon H g.1) = 1 := g.2
  rw [hperm] at hi
  exact hi

/-- A base-kernel element fixing a block vector has its local image in the
stabilizer of the corresponding coordinate. -/
theorem componentBaseBlockLinearGL_mem_stabilizer_of_fix
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (g : D.componentBaseKernel H) (x : I → W)
    (hfix : g.1.1 • x = x) (i : I) :
    D.componentBaseBlockLinearGL H i g ∈
      MulAction.stabilizer
        (LinearMap.GeneralLinearGroup R W) (x i) := by
  apply MulAction.mem_stabilizer_iff.mpr
  rw [← D.componentBaseKernel_action_apply H g x i, hfix]

/-- Concrete-image form of the preceding implication. -/
theorem componentBaseBlockImage_element_mem_stabilizer_of_fix
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (g : D.componentBaseKernel H) (x : I → W)
    (hfix : g.1.1 • x = x) (i : I) :
    (⟨D.componentBaseBlockLinearGL H i g,
        MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ :
      D.componentBaseBlockImage H i) ∈
        MulAction.stabilizer (D.componentBaseBlockImage H i) (x i) := by
  apply MulAction.mem_stabilizer_iff.mpr
  exact MulAction.mem_stabilizer_iff.mp
    (D.componentBaseBlockLinearGL_mem_stabilizer_of_fix H g x hfix i)

/-- If every coordinate is regular for the corresponding concrete base
image, then the whole product vector is regular for the base kernel. -/
theorem componentBaseKernel_stabilizer_eq_bot_of_local_regular
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (x : I → W)
    (hx : ∀ i, MulAction.stabilizer (D.componentBaseBlockImage H i) (x i) = ⊥) :
    MulAction.stabilizer (D.componentBaseKernel H) x = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  have hfix : g.1.1 • x = x :=
    MulAction.mem_stabilizer_iff.mp hg
  have hlocal : ∀ i, D.componentBaseBlockLinearGL H i g = 1 := by
    intro i
    have hmem :=
      D.componentBaseBlockImage_element_mem_stabilizer_of_fix
        H g x hfix i
    rw [hx i] at hmem
    exact congrArg Subtype.val hmem
  apply Subtype.ext
  apply Subtype.ext
  ext y i
  change (g.1.1 • y) i = y i
  rw [D.componentBaseKernel_action_apply H g y i, hlocal i]
  simp

end ImprimitiveLinearActionData

end LisiSabatini
