module

public import LisiSabatini.ImprimitiveReductionCore
public import Mathlib.GroupTheory.PGroup

/-!
# Normal components in a common imprimitive action

Normal-component affine synchronization presents every local prime component
as a subgroup `H ≤ K` of one common linear group.  An imprimitive structure,
on the other hand, should be chosen only once, for `K` itself.  This file
connects those two interfaces.

For `D : ImprimitiveLinearActionData K L` and `H : Subgroup K` we construct
the restricted imprimitive action on the concrete ambient subgroup
`H.map K.subtype`.  Its permutation image is also recorded internally as a
subgroup of the common top `D.blockPerm.range`.  Internal top images preserve
both normality and the prime-group property.  Consequently a regular abelian
normal subgroup of the common top, together with distinct prime labels,
forces at most one restricted component to have nontrivial top image.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uJ uR uW

variable {I : Type uI} {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-! ## Restriction to an internal normal component -/

/-- The concrete ambient linear subgroup belonging to an internal component
`H ≤ K`. -/
abbrev restrictedAmbient (H : Subgroup K) :
    Subgroup (LinearMap.GeneralLinearGroup R (I → W)) :=
  H.map K.subtype

/-- The canonical inclusion of the concrete ambient copy of `H` back into
the common action `K`. -/
def restrictedAmbientToCommon (H : Subgroup K) :
    restrictedAmbient H →* K :=
  Subgroup.inclusion (Subgroup.map_subtype_le H)

@[simp]
theorem restrictedAmbientToCommon_coe (H : Subgroup K)
    (g : restrictedAmbient H) :
    ((restrictedAmbientToCommon H g : K) :
      LinearMap.GeneralLinearGroup R (I → W)) = g :=
  rfl

/-- Restrict one common imprimitive structure to the concrete ambient image
of an internal component. -/
def restrictComponent
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    ImprimitiveLinearActionData (restrictedAmbient H) L where
  blockPerm := D.blockPerm.comp (restrictedAmbientToCommon H)
  blockLinear g i := D.blockLinear (restrictedAmbientToCommon H g) i
  action_apply g x i := by
    exact D.action_apply (restrictedAmbientToCommon H g) x i

@[simp]
theorem restrictComponent_blockPerm
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (g : restrictedAmbient H) :
    (D.restrictComponent H).blockPerm g =
      D.blockPerm (restrictedAmbientToCommon H g) :=
  rfl

/-! ## The top image internal to the common top -/

/-- The permutation image of `H`, regarded internally as a subgroup of the
single common top `D.blockPerm.range`. -/
def componentTopImage
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    Subgroup D.blockPerm.range :=
  H.map D.blockPerm.rangeRestrict

/-- Internal top images of normal components are normal in the common top. -/
theorem componentTopImage_normal
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : H.Normal) :
    (D.componentTopImage H).Normal :=
  Subgroup.Normal.map hH D.blockPerm.rangeRestrict
    D.blockPerm.rangeRestrict_surjective

/-- Internal top images preserve the prime-group property. -/
theorem componentTopImage_isPGroup
    {p : ℕ} (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (hH : IsPGroup p H) :
    IsPGroup p (D.componentTopImage H) :=
  hH.map D.blockPerm.rangeRestrict

/-- The internal top image, mapped back to the full permutation group, is
exactly the top range of the restricted imprimitive action. -/
theorem componentTopImage_map_subtype_eq_restrictComponent_range
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    (D.componentTopImage H).map D.blockPerm.range.subtype =
      (D.restrictComponent H).blockPerm.range := by
  ext σ
  constructor
  · intro hσ
    obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hτ
    refine MonoidHom.mem_range.mpr ⟨⟨(h : K), ?_⟩, ?_⟩
    · exact ⟨h, hh, rfl⟩
    · rfl
  · intro hσ
    obtain ⟨g, rfl⟩ := MonoidHom.mem_range.mp hσ
    obtain ⟨h, hh, hval⟩ := Subgroup.mem_map.mp g.2
    have hcommon : restrictedAmbientToCommon H g = h := by
      apply Subtype.ext
      exact hval.symm
    refine Subgroup.mem_map.mpr ⟨D.blockPerm.rangeRestrict h, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    · change D.blockPerm h =
        D.blockPerm (restrictedAmbientToCommon H g)
      rw [hcommon]

/-- The restricted concrete top is trivial exactly when the internal top
image is trivial. -/
theorem restrictComponent_range_eq_bot_iff
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    (D.restrictComponent H).blockPerm.range = ⊥ ↔
      D.componentTopImage H = ⊥ := by
  rw [← D.componentTopImage_map_subtype_eq_restrictComponent_range H]
  exact Subgroup.map_eq_bot_iff_of_injective (D.componentTopImage H)
    D.blockPerm.range.subtype_injective

end ImprimitiveLinearActionData

end LisiSabatini
