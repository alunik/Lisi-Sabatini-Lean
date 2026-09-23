module

public import LisiSabatini.PaperFiniteDegrees
public import LisiSabatini.PaperTinySymmetric
public import LisiSabatini.SymmetricEightVerified
public import LisiSabatini.SymmetricDoubleCosetCompletion
public import LisiSabatini.SymmetricFiniteCertificates
public import LisiSabatini.SymmetricSmallDegreeMatchingCompletion

/-!
# Symmetric-group endpoints for the paper

The uniform large-degree estimate and the finite-degree refinements are
assembled here into public statements with a single degree hypothesis.
-/

@[expose] public section

namespace LisiSabatini

universe uI

/-- Arbitrary mixed Sylow rows admit simultaneous trivial intersections
in every symmetric degree at least thirteen. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_ge_thirteen
    (n : ℕ) (hn : 13 ≤ n)
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin n))) :
    ∃ x : Equiv.Perm (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  by_cases hlarge : 40 ≤ n
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_ge_forty n hlarge p hp hinj P Q
  by_cases hmatching : n = 14 ∨ n = 16
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_fourteen_sixteen
      hmatching p hp hinj P Q
  exact exists_common_mixedSylowInter_bot_symmetricGroup_finite_degrees n
    (by omega) p hp hinj P Q

/-- Mixed trivial-intersection synchronization in every degree at least thirteen. -/
theorem mixedTwoSylowBotSynchronization_symmetricGroup_ge_thirteen
    (n : ℕ) (hn : 13 ≤ n) :
    HasMixedTwoSylowBotSynchronization.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinj P Q
  exact exists_common_mixedSylowInter_bot_symmetricGroup_ge_thirteen n hn p hp hinj P Q

/-- Lisi--Sabatini in every symmetric degree at least thirteen. -/
theorem hasLisiSabatini_symmetricGroup_ge_thirteen
    (n : ℕ) (hn : 13 ≤ n) : HasLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinj P
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_symmetricGroup_ge_thirteen n hn p hp hinj P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  change mixedSylowInter (P i) (P i) x ≤ _
  rw [hx i]
  exact bot_le

/-- Two arbitrary nilpotent subgroups have conjugates intersecting trivially
in every symmetric degree at least thirteen. -/
theorem mixedNilpotentIntersectionTrivial_symmetricGroup_ge_thirteen
    (n : ℕ) (hn : 13 ≤ n) : MixedNilpotentIntersectionTrivial (Equiv.Perm (Fin n)) :=
  mixedNilpotentIntersectionTrivial_of_mixedSylowBot
    (mixedTwoSylowBotSynchronization_symmetricGroup_ge_thirteen n hn)

/-- Mixed Sylow rows have a common trivial intersection in every symmetric
degree at least five except eight. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_ge_five_of_ne_eight
    (n : ℕ) (hn : 5 ≤ n) (hne : n ≠ 8)
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin n))) :
    ∃ x : Equiv.Perm (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  by_cases hlarge : 13 ≤ n
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_ge_thirteen n hlarge p hp hinj P Q
  have hupper : n ≤ 12 := by omega
  interval_cases n
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_five p hp hinj P Q
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_six p hp hinj P Q
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_seven p hp hinj P Q
  · exact (hne rfl).elim
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_nine_ten_twelve
      9 (Or.inl rfl) p hp hinj P Q
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_nine_ten_twelve
      10 (Or.inr (Or.inl rfl)) p hp hinj P Q
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_finite_degrees
      11 (Or.inl rfl) p hp hinj P Q
  · exact exists_common_mixedSylowInter_bot_symmetricGroup_nine_ten_twelve
      12 (Or.inr (Or.inr rfl)) p hp hinj P Q

/-- Every symmetric group except S8 has mixed simultaneous Sylow-core attainment. -/
theorem mixedTwoSylowCoreSynchronization_symmetricGroup_of_ne_eight
    (n : ℕ) (hne : n ≠ 8) :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinj P Q
  by_cases hsmall : n ≤ 4
  · exact mixedTwoSylowCoreSynchronization_symmetricGroup_le_four n hsmall p hp hinj P Q
  obtain ⟨x, hx⟩ := exists_common_mixedSylowInter_bot_symmetricGroup_ge_five_of_ne_eight
    n (by omega) hne p hp hinj P Q
  refine ⟨x, fun i ↦ ?_⟩
  have hc : pCore (p i) (Equiv.Perm (Fin n)) ≤ ⊥ := by
    simpa only [hx i] using pCore_le_mixedSylowInter (P i) (Q i) x
  exact (hx i).trans (le_antisymm hc bot_le).symm

/-- The original Lisi--Sabatini conjecture for every symmetric group.
The degree-eight branch uses inclusion-minimality, not triviality. -/
theorem hasLisiSabatini_symmetricGroup (n : ℕ) :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinj P
  by_cases he : n = 8
  · subst n
    exact hasLisiSabatini_symmetricGroup_eight p hp hinj P
  exact StrongLisiSabatini.hasLisiSabatini
    (HasMixedTwoSylowCoreSynchronization.strongLisiSabatini
      (mixedTwoSylowCoreSynchronization_symmetricGroup_of_ne_eight n he)) p hp hinj P

/-- Two arbitrary nilpotent subgroups have conjugates intersecting trivially
in symmetric degree at least five, except eight. -/
theorem mixedNilpotentIntersectionTrivial_symmetricGroup_ge_five_of_ne_eight
    (n : ℕ) (hn : 5 ≤ n) (hne : n ≠ 8) :
    MixedNilpotentIntersectionTrivial (Equiv.Perm (Fin n)) :=
  mixedNilpotentIntersectionTrivial_of_mixedSylowBot
    (fun p hp hinj P Q ↦
      exists_common_mixedSylowInter_bot_symmetricGroup_ge_five_of_ne_eight
        n hn hne p hp hinj P Q)

end LisiSabatini
