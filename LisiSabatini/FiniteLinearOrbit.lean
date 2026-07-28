module

public import LisiSabatini.FiniteLinearSubgroup
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Data.Set.Card

/-!
# Orbit cardinality for finite concrete linear groups
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uR uW

variable {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- An orbit has at most as many points as the acting group has elements. -/
theorem ncard_orbit_le_natCard
    [Finite W]
    (H : Subgroup (LinearMap.GeneralLinearGroup R W)) (c : W) :
    (MulAction.orbit H c).ncard ≤ Nat.card H := by
  letI : Finite H := finite_linearSubgroup_of_finite H
  rw [MulAction.orbit, ← Set.image_univ]
  simpa using
    (Set.ncard_image_le (f := fun h : H ↦ h • c) (s := Set.univ))

end LisiSabatini
