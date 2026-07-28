module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.Data.Finite.Card
public import Mathlib.Data.Finite.Prod

/-!
# Finiteness of concrete linear subgroups

This elementary fact is kept separate from orbit-counting APIs because it is
also needed by the structural Clifford/imprimitivity path.
-/

@[expose] public section

namespace LisiSabatini

universe uR uW

variable {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- A linear subgroup acting on a finite type is finite, independently of
the cardinality of the scalar semiring. -/
theorem finite_linearSubgroup_of_finite
    [Finite W]
    (H : Subgroup (LinearMap.GeneralLinearGroup R W)) : Finite H := by
  exact Finite.of_injective
    (fun h : H ↦ fun w : W ↦ h • w) (by
      intro a b hab
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro w
      exact congrFun hab w)

end LisiSabatini
