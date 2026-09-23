module

public import LisiSabatini.A8DoubleCosetCompletion
public import LisiSabatini.FiniteCertificates.A8SylowTwoWitness
public import LisiSabatini.ThreeConjugatesSynchronization

/-!
# The degree-eight alternating group

An explicit kernel-checked Sylow-two pair supplies the double-coset bound.
The exact odd-prime budgets then prove simultaneous trivial intersections
for every finite family of independently prescribed mixed Sylow rows.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI

open FiniteCertificates

/-- In degree eight, one conjugator makes every prescribed mixed Sylow
intersection trivial. The finite index family may lie in any universe. -/
theorem exists_common_mixedSylowInter_bot_alternatingGroup_eight
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin 8))) :
    ∃ x : alternatingGroup (Fin 8), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ :=
  exists_common_mixedSylowInter_bot_A8_of_one_pair
    A8Rows.sylow2 A8SylowTwoWitness.card_sylow2
    ⟨A8SylowTwoWitness.witness, A8SylowTwoWitness.sylow2_inter_witness_eq_bot⟩
    p hp hinj P Q

/-- The mixed trivial-intersection property in degree eight. -/
theorem mixedTwoSylowBotSynchronization_alternatingGroup_eight :
    HasMixedTwoSylowBotSynchronization.{0, uI} (alternatingGroup (Fin 8)) := by
  intro I _ p hp hinj P Q
  exact exists_common_mixedSylowInter_bot_alternatingGroup_eight p hp hinj P Q

/-- Trivial mixed intersections attain each prime core. -/
theorem mixedTwoSylowCoreSynchronization_alternatingGroup_eight :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (alternatingGroup (Fin 8)) := by
  intro I _ p hp hinj P Q
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_alternatingGroup_eight p hp hinj P Q
  refine ⟨x, fun i ↦ ?_⟩
  have hcore : pCore (p i) (alternatingGroup (Fin 8)) ≤ ⊥ := by
    simpa only [hx i] using pCore_le_mixedSylowInter (P i) (Q i) x
  exact (hx i).trans (le_antisymm hcore bot_le).symm

/-- The strong same-row Lisi--Sabatini conclusion in degree eight. -/
theorem strongLisiSabatini_alternatingGroup_eight :
    StrongLisiSabatini.{0, uI} (alternatingGroup (Fin 8)) :=
  HasMixedTwoSylowCoreSynchronization.strongLisiSabatini
    mixedTwoSylowCoreSynchronization_alternatingGroup_eight

/-- The original inclusion-minimal Lisi--Sabatini conclusion in degree eight. -/
theorem hasLisiSabatini_alternatingGroup_eight :
    HasLisiSabatini.{0, uI} (alternatingGroup (Fin 8)) :=
  StrongLisiSabatini.hasLisiSabatini strongLisiSabatini_alternatingGroup_eight

end LisiSabatini
