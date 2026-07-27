import LisiSabatini.MixedSylowIntersections
import LisiSabatini.Strong

/-!
# Two-row and three-row Sylow-core synchronization

The properties in this file separate three logically distinct assertions:

* mixed two-row synchronization, with independently prescribed `P` and `Q`;
* mixed three-row synchronization, with independently prescribed `P`, `Q`,
  and `R`;
* same-row three-conjugates synchronization.

No classification theorem is assumed here.  The elementary implication
ledger is proved directly from the definitions.
-/

noncomputable section

namespace LisiSabatini

universe uG uI

/-- Mixed two-row synchronization: one conjugator works simultaneously for
independently prescribed Sylow rows at all distinct labelled primes. -/
def HasMixedTwoSylowCoreSynchronization
    (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    ∀ P Q : ∀ i, Sylow (p i) G,
      ∃ x : G, ∀ i,
        mixedSylowInter (P i) (Q i) x = pCore (p i) G

/-- Mixed three-row synchronization: two conjugators work simultaneously for
three independently prescribed Sylow rows at all distinct labelled primes. -/
def HasMixedThreeSylowCoreSynchronization
    (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    ∀ P Q R : ∀ i, Sylow (p i) G,
      ∃ x y : G, ∀ i,
        mixedSylowTripleInter (P i) (Q i) (R i) x y =
          pCore (p i) G

/-- Huang's same-row three-intersection synchronization property. -/
def HasThreeConjugatesSylowSynchronization
    (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    ∀ P : ∀ i, Sylow (p i) G,
      ∃ x y : G, ∀ i,
        mixedSylowTripleInter (P i) (P i) (P i) x y =
          pCore (p i) G

/-- Mixed two-row synchronization holds in a trivial group. -/
theorem mixedTwoSylowCoreSynchronization_of_subsingleton
    {G : Type uG} [Group G] [Finite G] [Subsingleton G] :
    HasMixedTwoSylowCoreSynchronization.{uG, uI} G := by
  intro I _ p _hp _hinj P Q
  refine ⟨1, fun i ↦ ?_⟩
  exact Subsingleton.elim
    (mixedSylowInter (P i) (Q i) 1) (pCore (p i) G)

/-- Mixed three-row synchronization holds in a trivial group. -/
theorem mixedThreeSylowCoreSynchronization_of_subsingleton
    {G : Type uG} [Group G] [Finite G] [Subsingleton G] :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G := by
  intro I _ p _hp _hinj P Q R
  refine ⟨1, 1, fun i ↦ ?_⟩
  exact Subsingleton.elim
    (mixedSylowTripleInter (P i) (Q i) (R i) 1 1)
    (pCore (p i) G)

/-- Mixed two-row synchronization contains the existing same-row strong
property as its diagonal specialization. -/
theorem HasMixedTwoSylowCoreSynchronization.strongLisiSabatini
    {G : Type uG} [Group G] [Finite G]
    (hG : HasMixedTwoSylowCoreSynchronization.{uG, uI} G) :
    StrongLisiSabatini.{uG, uI} G := by
  intro I _ p hp hinj P
  exact hG p hp hinj P P

/-- Mixed two-row synchronization implies mixed three-row synchronization:
after the first two rows meet in the core, intersecting with any third Sylow
subgroup leaves the core unchanged. -/
theorem mixedTwo_to_mixedThree
    {G : Type uG} [Group G] [Finite G]
    (hG : HasMixedTwoSylowCoreSynchronization.{uG, uI} G) :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G := by
  intro I _ p hp hinj P Q R
  obtain ⟨x, hx⟩ := hG p hp hinj P Q
  refine ⟨x, 1, fun i ↦ ?_⟩
  change mixedSylowInter (P i) (Q i) x ⊓
      (((1 : G) • R i : Sylow (p i) G) : Subgroup G) =
    pCore (p i) G
  rw [hx i]
  exact inf_eq_left.mpr (pCore_le_sylow ((1 : G) • R i))

/-- The mixed three-row theorem specializes to the same-row theorem. -/
theorem mixedThree_to_threeConjugates
    {G : Type uG} [Group G] [Finite G]
    (hG : HasMixedThreeSylowCoreSynchronization.{uG, uI} G) :
    HasThreeConjugatesSylowSynchronization.{uG, uI} G := by
  intro I _ p hp hinj P
  exact hG p hp hinj P P P

/-- The existing strong two-conjugate theorem implies the same-row
three-conjugates theorem. -/
theorem strongLS_to_threeConjugates
    {G : Type uG} [Group G] [Finite G]
    (hG : StrongLisiSabatini.{uG, uI} G) :
    HasThreeConjugatesSylowSynchronization.{uG, uI} G := by
  intro I _ p hp hinj P
  obtain ⟨x, hx⟩ := hG p hp hinj P
  refine ⟨x, 1, fun i ↦ ?_⟩
  change sylowInter (P i) x ⊓
      (((1 : G) • P i : Sylow (p i) G) : Subgroup G) =
    pCore (p i) G
  rw [hx i]
  exact inf_eq_left.mpr (pCore_le_sylow ((1 : G) • P i))

end LisiSabatini
