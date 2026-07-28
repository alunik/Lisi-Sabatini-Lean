module

public import LisiSabatini.OrbitAvoidingCountCore
public import LisiSabatini.TwoOrbitAvoidingPaletteCore

/-!
# Counting criteria for two-orbit avoidance

The bad union consists of the translated nonregular locus for every row and
the two actual translated orbit loci at the distinguished row.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- If the nonregular loci and the two actual forbidden orbits do not fill
the ambient module, then the family has two-orbit avoiding common regular
translates. -/
theorem twoOrbitAvoidingCommonRegularTranslates_of_sum_ncard_add_sum_orbit_lt
    [Fintype I] [Finite W]
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R W))
    (hcard : ∀ (j₀ : I) (c : Fin 2 → W),
      (∑ j, (nonregularVectors (H j)).ncard) +
        ∑ k, (MulAction.orbit (H j₀) (c k)).ncard < Nat.card W) :
    TwoOrbitAvoidingCommonRegularTranslates H := by
  intro j₀ t c
  let bad : I ⊕ Fin 2 → Set W
    | Sum.inl j => translatedNonregularVectors (H j) (t j)
    | Sum.inr k => translatedSameBlockOrbitLocus (H j₀) (t j₀) (c k)
  have hbadCard : ∑ a, (bad a).ncard < Nat.card W := by
    rw [Fintype.sum_sum_type]
    simpa [bad, ncard_translatedNonregularVectors,
      ncard_translatedSameBlockOrbitLocus] using hcard j₀ c
  obtain ⟨v, hv⟩ := exists_avoids_of_sum_ncard_lt bad hbadCard
  refine ⟨v, ?_, ?_⟩
  · intro j
    have hj := hv (Sum.inl j)
    exact not_ne_iff.mp (by simpa [bad] using hj)
  · intro k
    have hk := hv (Sum.inr k)
    simpa [bad] using hk

/-- It is enough to charge each of the two forbidden orbits by the order of
its acting group. -/
theorem twoOrbitAvoidingCommonRegularTranslates_of_sum_ncard_add_two_mul_natCard_lt
    [Fintype I] [Finite W]
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R W))
    (hcard : ∀ j₀ : I,
      (∑ j, (nonregularVectors (H j)).ncard) +
        2 * Nat.card (H j₀) < Nat.card W) :
    TwoOrbitAvoidingCommonRegularTranslates H := by
  apply
    twoOrbitAvoidingCommonRegularTranslates_of_sum_ncard_add_sum_orbit_lt H
  intro j₀ c
  apply lt_of_le_of_lt _ (hcard j₀)
  apply Nat.add_le_add_left
  calc
    (∑ k, (MulAction.orbit (H j₀) (c k)).ncard) ≤
        ∑ _k : Fin 2, Nat.card (H j₀) := by
      exact Finset.sum_le_sum fun k _ ↦ ncard_orbit_le_natCard (H j₀) (c k)
    _ = 2 * Nat.card (H j₀) := by simp [two_mul]

end LisiSabatini
