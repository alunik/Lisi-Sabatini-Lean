import LisiSabatini.CommonTranslateCore
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Kernels and regular vectors for linear-action images

The affine lifting argument uses the faithful image of a complement's action
instead of quotienting the complement by its action kernel.  This file records
the generic bridge: the stabilizer of a vector in the acting group is exactly
the action kernel if and only if the stabilizer in the image is trivial.
-/

noncomputable section

namespace LisiSabatini

universe uA uR uV

variable {A : Type uA} [Group A]
variable {R : Type uR} [Semiring R]
variable {V : Type uV} [AddCommMonoid V] [Module R V]

/-- The preimage in `A` of the point stabilizer for a linear action `ρ`. -/
def actionPointStabilizer
    (ρ : A →* LinearMap.GeneralLinearGroup R V) (v : V) : Subgroup A :=
  (MulAction.stabilizer (LinearMap.GeneralLinearGroup R V) v).comap ρ

@[simp]
theorem mem_actionPointStabilizer
    (ρ : A →* LinearMap.GeneralLinearGroup R V) (v : V) (a : A) :
    a ∈ actionPointStabilizer ρ v ↔ ρ a • v = v :=
  Iff.rfl

/-- The action kernel fixes every vector. -/
theorem action_ker_le_pointStabilizer
    (ρ : A →* LinearMap.GeneralLinearGroup R V) (v : V) :
    ρ.ker ≤ actionPointStabilizer ρ v := by
  intro a ha
  rw [mem_actionPointStabilizer, MonoidHom.mem_ker.mp ha, one_smul]

/-- The stabilizer in `A` is precisely the action kernel exactly when the
stabilizer in the faithful image `ρ.range` is trivial. -/
theorem actionPointStabilizer_eq_ker_iff_range_stabilizer_eq_bot
    (ρ : A →* LinearMap.GeneralLinearGroup R V) (v : V) :
    actionPointStabilizer ρ v = ρ.ker ↔
      MulAction.stabilizer ρ.range v = ⊥ := by
  constructor
  · intro hker
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp g.2
    have haFix : a ∈ actionPointStabilizer ρ v := by
      rw [mem_actionPointStabilizer, ha]
      exact hg
    have haKer : a ∈ ρ.ker := hker ▸ haFix
    apply Subtype.ext
    exact ha.symm.trans (MonoidHom.mem_ker.mp haKer)
  · intro himage
    apply le_antisymm
    · intro a ha
      rw [MonoidHom.mem_ker]
      let g : ρ.range := ⟨ρ a, ⟨a, rfl⟩⟩
      have hg : g ∈ MulAction.stabilizer ρ.range v := by
        rw [MulAction.mem_stabilizer_iff]
        exact ha
      have hgOne : g = 1 := (Subgroup.eq_bot_iff_forall _).mp himage g hg
      exact congrArg Subtype.val hgOne
    · exact action_ker_le_pointStabilizer ρ v

end LisiSabatini
