import LisiSabatini.CommonTranslateCore
import LisiSabatini.OrbitAvoidingPaletteCore

/-!
# The two-orbit avoiding common-translate predicate

This file isolates the recursive local invariant needed to manufacture a
three-colour palette.  At one distinguished row, a common regular translate
may be required to avoid two prescribed orbit colours simultaneously.
-/

noncomputable section

namespace LisiSabatini

universe uJ uR uW

variable {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- Arbitrary translations of a family of linear actions have a common
point with trivial stabilizer for every action. -/
def CommonRegularTranslates
    (H : J → Subgroup (LinearMap.GeneralLinearGroup R W)) : Prop :=
  ∀ t : J → W,
    ∃ v : W, ∀ j, MulAction.stabilizer (H j) (v + t j) = ⊥

/-- Simultaneous translated regularity with avoidance of two prescribed
orbits of one distinguished component.  The two forbidden targets are
allowed to coincide. -/
def TwoOrbitAvoidingCommonRegularTranslates
    (H : J → Subgroup (LinearMap.GeneralLinearGroup R W)) : Prop :=
  ∀ (j₀ : J) (t : J → W) (c : Fin 2 → W),
    ∃ v : W,
      (∀ j, MulAction.stabilizer (H j) (v + t j) = ⊥) ∧
      ∀ k, ¬ SameBlockOrbit (H j₀) (v + t j₀) (c k)

namespace TwoOrbitAvoidingCommonRegularTranslates

/-- Two-orbit avoidance implies ordinary common translated regularity,
including for an empty family of actions. -/
theorem commonRegularTranslates
    {H : J → Subgroup (LinearMap.GeneralLinearGroup R W)}
    (h : TwoOrbitAvoidingCommonRegularTranslates H) :
    CommonRegularTranslates H := by
  intro t
  by_cases hJ : Nonempty J
  · letI : Nonempty J := hJ
    obtain ⟨v, hregular, _⟩ :=
      h (Classical.choice hJ) t (fun _ ↦ 0)
    exact ⟨v, hregular⟩
  · refine ⟨0, fun j ↦ ?_⟩
    exact (hJ ⟨j⟩).elim

/-- Repeating a forbidden target specializes two-orbit avoidance to the
existing one-orbit recursive invariant. -/
theorem orbitAvoidingCommonRegularTranslates
    {H : J → Subgroup (LinearMap.GeneralLinearGroup R W)}
    (h : TwoOrbitAvoidingCommonRegularTranslates H) :
    OrbitAvoidingCommonRegularTranslates H := by
  intro j₀ t c
  obtain ⟨v, hregular, havoid⟩ := h j₀ t (fun _ ↦ c)
  exact ⟨v, hregular, havoid 0⟩

/-- Successive two-orbit avoidance produces three common-regular shifts
whose values in the distinguished row lie in pairwise distinct orbits. -/
theorem exists_three_pairwise_orbitSeparated_commonRegularTranslates
    {H : J → Subgroup (LinearMap.GeneralLinearGroup R W)}
    (h : TwoOrbitAvoidingCommonRegularTranslates H)
    (j₀ : J) (t : J → W) :
    ∃ v₀ v₁ v₂ : W,
      (∀ j, MulAction.stabilizer (H j) (v₀ + t j) = ⊥) ∧
      (∀ j, MulAction.stabilizer (H j) (v₁ + t j) = ⊥) ∧
      (∀ j, MulAction.stabilizer (H j) (v₂ + t j) = ⊥) ∧
      ¬ SameBlockOrbit (H j₀) (v₀ + t j₀) (v₁ + t j₀) ∧
      ¬ SameBlockOrbit (H j₀) (v₀ + t j₀) (v₂ + t j₀) ∧
      ¬ SameBlockOrbit (H j₀) (v₁ + t j₀) (v₂ + t j₀) := by
  obtain ⟨v₀, hregular₀⟩ := h.commonRegularTranslates t
  obtain ⟨v₁, hregular₁, havoid₁⟩ :=
    h j₀ t (fun _ ↦ v₀ + t j₀)
  let c : Fin 2 → W := fun k ↦
    Fin.cases (v₀ + t j₀) (fun _ ↦ v₁ + t j₀) k
  obtain ⟨v₂, hregular₂, havoid₂⟩ := h j₀ t c
  refine ⟨v₀, v₁, v₂, hregular₀, hregular₁, hregular₂, ?_, ?_, ?_⟩
  · intro hsame
    exact havoid₁ 0 (sameBlockOrbit_symm (H j₀) hsame)
  · intro hsame
    exact havoid₂ 0 (by
      simpa only [c, Fin.cases_zero] using
        sameBlockOrbit_symm (H j₀) hsame)
  · intro hsame
    exact havoid₂ 1 (by
      simpa only [c, Fin.cases_succ] using
        sameBlockOrbit_symm (H j₀) hsame)

/-- Two-orbit avoiding common regularity is downward monotone in every
acting subgroup. -/
theorem mono
    {A B : J → Subgroup (LinearMap.GeneralLinearGroup R W)}
    (hAB : ∀ j, A j ≤ B j)
    (hB : TwoOrbitAvoidingCommonRegularTranslates B) :
    TwoOrbitAvoidingCommonRegularTranslates A := by
  intro j₀ t c
  obtain ⟨v, hregular, havoid⟩ := hB j₀ t c
  refine ⟨v, ?_, ?_⟩
  · intro j
    by_contra hne
    have hlarge : v + t j ∈ nonregularVectors (B j) :=
      nonregularVectors_mono (hAB j) hne
    exact hlarge (hregular j)
  · intro k horbit
    obtain ⟨a, ha⟩ := horbit
    exact havoid k ⟨⟨a.1, hAB j₀ a.2⟩, ha⟩

end TwoOrbitAvoidingCommonRegularTranslates

end LisiSabatini
