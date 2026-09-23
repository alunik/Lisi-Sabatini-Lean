module

public import LisiSabatini.A8DoubleCosetVerified
public import LisiSabatini.PaperFiniteDegrees
public import LisiSabatini.PaperTinyAlternating

/-!
# Alternating groups in every degree

The general bounds, finite-degree refinements and degree-eight certificate
give mixed trivial intersections from degree five onward. The smaller
degrees retain their prime cores. Together they give Lisi--Sabatini for
every alternating group.
-/

@[expose] public section

namespace LisiSabatini

universe uI

/-- Every finite family of independently prescribed mixed Sylow rows has
simultaneously trivial intersections in alternating degree at least five. -/
theorem exists_common_mixedSylowInter_bot_alternatingGroup_ge_five
    (n : ℕ) (hn : 5 ≤ n)
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin n))) :
    ∃ x : alternatingGroup (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  by_cases he : n = 8
  · subst n
    exact exists_common_mixedSylowInter_bot_alternatingGroup_eight p hp hinj P Q
  exact exists_common_mixedSylowInter_bot_alternatingGroup_ge_five_of_ne_eight
    n hn he p hp hinj P Q

/-- Mixed trivial-intersection synchronization in alternating degree at least five. -/
theorem mixedTwoSylowBotSynchronization_alternatingGroup_ge_five
    (n : ℕ) (hn : 5 ≤ n) :
    HasMixedTwoSylowBotSynchronization.{0, uI} (alternatingGroup (Fin n)) := by
  intro I _ p hp hinj P Q
  exact exists_common_mixedSylowInter_bot_alternatingGroup_ge_five n hn p hp hinj P Q

/-- Every alternating group has mixed simultaneous Sylow-core attainment. -/
theorem mixedTwoSylowCoreSynchronization_alternatingGroup (n : ℕ) :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (alternatingGroup (Fin n)) := by
  intro I _ p hp hinj P Q
  by_cases hn : n ≤ 4
  · exact mixedTwoSylowCoreSynchronization_alternatingGroup_le_four n hn p hp hinj P Q
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_alternatingGroup_ge_five n (by omega) p hp hinj P Q
  refine ⟨x, fun i ↦ ?_⟩
  have hc : pCore (p i) (alternatingGroup (Fin n)) ≤ ⊥ := by
    simpa only [hx i] using pCore_le_mixedSylowInter (P i) (Q i) x
  exact (hx i).trans (le_antisymm hc bot_le).symm

/-- The strong Lisi--Sabatini conclusion in every alternating degree. -/
theorem strongLisiSabatini_alternatingGroup (n : ℕ) :
    StrongLisiSabatini.{0, uI} (alternatingGroup (Fin n)) :=
  HasMixedTwoSylowCoreSynchronization.strongLisiSabatini
    (mixedTwoSylowCoreSynchronization_alternatingGroup n)

/-- The original Lisi--Sabatini conjecture for every alternating group. -/
theorem hasLisiSabatini_alternatingGroup (n : ℕ) :
    HasLisiSabatini.{0, uI} (alternatingGroup (Fin n)) :=
  StrongLisiSabatini.hasLisiSabatini (strongLisiSabatini_alternatingGroup n)

/-- Any two nilpotent subgroups have conjugates intersecting trivially
in alternating degree at least five. -/
theorem mixedNilpotentIntersectionTrivial_alternatingGroup_ge_five
    (n : ℕ) (hn : 5 ≤ n) : MixedNilpotentIntersectionTrivial (alternatingGroup (Fin n)) :=
  mixedNilpotentIntersectionTrivial_of_mixedSylowBot
    (mixedTwoSylowBotSynchronization_alternatingGroup_ge_five n hn)

/-- In every alternating degree, two nilpotent subgroups have a relative
conjugate whose intersection lies in the Fitting subgroup. -/
theorem mixedNilpotentIntersectionInFitting_alternatingGroup (n : ℕ) :
    MixedNilpotentIntersectionInFitting (alternatingGroup (Fin n)) :=
  mixedNilpotentIntersectionInFitting_of_mixedStrongLS
    (mixedTwoSylowCoreSynchronization_alternatingGroup n)

end LisiSabatini
