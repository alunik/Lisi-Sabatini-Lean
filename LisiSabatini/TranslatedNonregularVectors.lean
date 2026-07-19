import LisiSabatini.CommonTranslateCore

/-!
# Translated nonregular loci

Only the translated locus and its cardinality invariance are needed by the
odd-order orbit-avoidance argument.
-/

noncomputable section

namespace LisiSabatini

/-- The locus of base points `v` for which `v + t` is nonregular for `H`. -/
def translatedNonregularVectors
    {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) (t : V) : Set V :=
  (Equiv.addRight t) ⁻¹' nonregularVectors H

@[simp]
theorem mem_translatedNonregularVectors
    {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V]
    {H : Subgroup (LinearMap.GeneralLinearGroup R V)} {t v : V} :
    v ∈ translatedNonregularVectors H t ↔
      MulAction.stabilizer H (v + t) ≠ ⊥ :=
  Iff.rfl

/-- Translation does not change the number of bad vectors. -/
theorem ncard_translatedNonregularVectors
    {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V] [Finite V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) (t : V) :
    (translatedNonregularVectors H t).ncard =
      (nonregularVectors H).ncard := by
  apply Set.ncard_preimage_of_injective_subset_range
  · exact (Equiv.addRight t).injective
  · rw [(Equiv.addRight t).surjective.range_eq]
    exact Set.subset_univ _

end LisiSabatini
