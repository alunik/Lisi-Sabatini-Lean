import LisiSabatini.NormalComponentOrbitAvoidingCore
import LisiSabatini.TwoOrbitAvoidingPaletteCore

/-!
# Linear-equivalence invariance of two-orbit avoidance

The recursive affine two-base invariant is stated on a doubled module.
Imprimitive composition instead uses the linearly equivalent blockwise-pair
model.  This file records the exact transport of simultaneous regularity and
both forbidden component orbits through an arbitrary linear equivalence.
-/

noncomputable section

namespace LisiSabatini

universe uJ uV uW

namespace NCASLinearEquiv

variable {r : ℕ} {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module (ZMod r) V]
variable [AddCommGroup W] [Module (ZMod r) W]

/-- Two-orbit-avoiding common translated regularity is invariant under a
simultaneous linear change of coordinates. -/
theorem twoOrbitAvoidingCommonRegularTranslates_map_conjugation_iff
    {J : Type uJ}
    (e : V ≃ₗ[ZMod r] W)
    (A : J → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    TwoOrbitAvoidingCommonRegularTranslates
        (fun j ↦ (A j).map (conjugation e).toMonoidHom) ↔
      TwoOrbitAvoidingCommonRegularTranslates A := by
  constructor
  · intro h j₀ t c
    obtain ⟨w, hregular, havoid⟩ :=
      h j₀ (fun j ↦ e (t j)) (fun k ↦ e (c k))
    refine ⟨e.symm w, ?_, ?_⟩
    · intro j
      apply
        (stabilizer_map_conjugation_eq_bot_iff e (A j)
          (e.symm w + t j)).mp
      simpa using hregular j
    · intro k horbit
      apply havoid k
      have hmapped :=
        (sameBlockOrbit_map_conjugation_iff e (A j₀)
          (e.symm w + t j₀) (c k)).mpr horbit
      simpa using hmapped
  · intro h j₀ t c
    obtain ⟨v, hregular, havoid⟩ :=
      h j₀ (fun j ↦ e.symm (t j)) (fun k ↦ e.symm (c k))
    refine ⟨e v, ?_, ?_⟩
    · intro j
      have htransport :=
        (stabilizer_map_conjugation_eq_bot_iff e (A j)
          (v + e.symm (t j))).mpr (hregular j)
      simpa using htransport
    · intro k horbit
      apply havoid k
      have hmapped : SameBlockOrbit
          ((A j₀).map (conjugation e).toMonoidHom)
          (e (v + e.symm (t j₀))) (e (e.symm (c k))) := by
        simpa using horbit
      exact
        (sameBlockOrbit_map_conjugation_iff e (A j₀)
          (v + e.symm (t j₀)) (e.symm (c k))).mp hmapped

end NCASLinearEquiv

end LisiSabatini
