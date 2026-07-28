module

public import LisiSabatini.ImprimitiveReductionCore

/-!
# The one-orbit avoiding common-translate predicate

This proof-only core contains the strengthened local regularity predicate.
The later single-top synchronization adapters remain in
`OrbitAvoidingPalette.lean`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uJ uR uW

variable {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- Simultaneous translated regularity with avoidance of one prescribed
orbit of a distinguished component. -/
def OrbitAvoidingCommonRegularTranslates
    (H : J → Subgroup (LinearMap.GeneralLinearGroup R W)) : Prop :=
  ∀ (j₀ : J) (t : J → W) (c : W),
    ∃ v : W,
      (∀ j, MulAction.stabilizer (H j) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit (H j₀) (v + t j₀) c

end LisiSabatini
