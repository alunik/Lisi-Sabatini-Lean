module

public import LisiSabatini.OrbitAvoidingPaletteCore
public import LisiSabatini.TranslatedNonregularVectors
public import LisiSabatini.FiniteLinearSubgroup
public import LisiSabatini.FiniteLinearOrbit
public import Mathlib.Data.Fintype.BigOperators

/-!
# Core counting criteria for one-orbit avoidance

This file contains exactly the translated-orbit loci and union bounds used by
the odd-order proof.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- Base points whose translate has the same `H`-orbit colour as `c`. -/
def translatedSameBlockOrbitLocus
    (H : Subgroup (LinearMap.GeneralLinearGroup R W))
    (t c : W) : Set W :=
  {v | SameBlockOrbit H (v + t) c}

@[simp]
theorem mem_translatedSameBlockOrbitLocus
    {H : Subgroup (LinearMap.GeneralLinearGroup R W)}
    {t c v : W} :
    v ∈ translatedSameBlockOrbitLocus H t c ↔
      SameBlockOrbit H (v + t) c :=
  Iff.rfl

theorem sameBlockOrbit_iff_mem_orbit
    (H : Subgroup (LinearMap.GeneralLinearGroup R W))
    (x c : W) :
    SameBlockOrbit H x c ↔ x ∈ MulAction.orbit H c := by
  constructor
  · rintro ⟨a, ha⟩
    refine MulAction.mem_orbit_iff.mpr ⟨a⁻¹, ?_⟩
    rw [← ha, inv_smul_smul]
  · rintro ⟨a, ha⟩
    refine ⟨a⁻¹, ?_⟩
    rw [← ha, inv_smul_smul]

theorem translatedSameBlockOrbitLocus_eq_preimage_orbit
    (H : Subgroup (LinearMap.GeneralLinearGroup R W))
    (t c : W) :
    translatedSameBlockOrbitLocus H t c =
      (Equiv.addRight t) ⁻¹' MulAction.orbit H c := by
  ext v
  exact sameBlockOrbit_iff_mem_orbit H (v + t) c

theorem ncard_translatedSameBlockOrbitLocus
    [Finite W]
    (H : Subgroup (LinearMap.GeneralLinearGroup R W))
    (t c : W) :
    (translatedSameBlockOrbitLocus H t c).ncard =
      (MulAction.orbit H c).ncard := by
  rw [translatedSameBlockOrbitLocus_eq_preimage_orbit]
  apply Set.ncard_preimage_of_injective_subset_range
  · exact (Equiv.addRight t).injective
  · rw [(Equiv.addRight t).surjective.range_eq]
    exact Set.subset_univ _

theorem ncard_translatedSameBlockOrbitLocus_le_natCard
    [Finite W]
    (H : Subgroup (LinearMap.GeneralLinearGroup R W))
    (t c : W) :
    (translatedSameBlockOrbitLocus H t c).ncard ≤ Nat.card H := by
  rw [ncard_translatedSameBlockOrbitLocus]
  exact ncard_orbit_le_natCard H c

theorem orbitAvoidingCommonRegularTranslates_of_sum_ncard_add_orbit_lt
    [Fintype I] [Finite W]
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R W))
    (hcard : ∀ (j₀ : I) (c : W),
      (∑ j, (nonregularVectors (H j)).ncard) +
        (MulAction.orbit (H j₀) c).ncard < Nat.card W) :
    OrbitAvoidingCommonRegularTranslates H := by
  intro j₀ t c
  let bad : Option I → Set W
    | none => translatedSameBlockOrbitLocus (H j₀) (t j₀) c
    | some j => translatedNonregularVectors (H j) (t j)
  have hbadCard : ∑ o, (bad o).ncard < Nat.card W := by
    rw [Fintype.sum_option]
    simpa [bad, ncard_translatedSameBlockOrbitLocus,
      ncard_translatedNonregularVectors, Nat.add_comm] using hcard j₀ c
  obtain ⟨v, hv⟩ := exists_avoids_of_sum_ncard_lt bad hbadCard
  refine ⟨v, ?_, ?_⟩
  · intro j
    have hj := hv (some j)
    exact not_ne_iff.mp (by simpa [bad] using hj)
  · have hnone := hv none
    simpa [bad] using hnone

theorem orbitAvoidingCommonRegularTranslates_of_sum_ncard_add_natCard_lt
    [Fintype I] [Finite W]
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R W))
    (hcard : ∀ j₀ : I,
      (∑ j, (nonregularVectors (H j)).ncard) + Nat.card (H j₀) <
        Nat.card W) :
    OrbitAvoidingCommonRegularTranslates H := by
  apply orbitAvoidingCommonRegularTranslates_of_sum_ncard_add_orbit_lt H
  intro j₀ c
  exact lt_of_le_of_lt
    (Nat.add_le_add_left (ncard_orbit_le_natCard (H j₀) c) _)
    (hcard j₀)

end LisiSabatini
