module

public import LisiSabatini.CommonTranslateCore
public import Mathlib.Data.Nat.Prime.Basic

/-!
# Fixed-point-free linear actions away from zero

This is the sole interface from the rank-five block-model development used by
the odd-order proof.
-/

@[expose] public section

namespace LisiSabatini

universe u v

/-- Nonidentity elements of `B` have no nonzero fixed vectors. -/
def FixedPointFreeOffZero
    {F : Type u} {V : Type v}
    [Semiring F] [AddCommMonoid V] [Module F V]
    (B : Subgroup (LinearMap.GeneralLinearGroup F V)) : Prop :=
  ∀ b : B, b ≠ 1 → ∀ x : V, b • x = x → x = 0

end LisiSabatini
