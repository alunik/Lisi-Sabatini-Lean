import Definitions
import LisiSabatini.PaperAlignment

/-! Proofs of the independently written Challenge statements. -/

namespace PaperVerification

open PaperSpecification
open scoped MonoidAlgebra Pointwise

universe uG uI

/-- The good solvable theorem, with the stronger prime-core conclusion. -/
theorem goodSolvable
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : EveryQuotientHasStar G) :
    CoreSynchronization.{uG, uI} G := by
  exact LisiSabatini.strongLisiSabatini_of_solvable_of_quotientSylowCoreAttainment hstar

/-- A nilpotent-subgroup consequence of the good solvable theorem. -/
theorem goodSolvableNilpotent
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : EveryQuotientHasStar G)
    (H : Subgroup G) (hH : Group.IsNilpotent H) :
    ∃ x : G, H ⊓ ((MulAut.conj x) • H) ≤ fitting G := by
  exact LisiSabatini.nilpotentSelfIntersectionInFitting_of_solvable_of_quotientSylowCoreAttainment
    hstar H hH

/-- Proposition 2.3 over an arbitrary field and module. -/
theorem translatedRegularOrbits
    {k G V I : Type*} [Field k] [Group G] [Finite G]
    [Group.IsNilpotent G] [AddCommGroup V] [Module k V] [Finite I]
    (rho : Representation k G V) (hfaith : Function.Injective rho)
    (hsemi : IsSemisimpleModule k[G] rho.asModule)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P : ∀ i, Sylow (p i) G)
    (hregular : ∀ i, ∃ w : V, ∀ g : G,
      g ∈ (P i : Subgroup G) → rho g w = w → g = 1)
    (t : I → V) :
    ∃ v : V, ∀ i, ∀ g : G,
      g ∈ (P i : Subgroup G) → rho g (v + t i) = v + t i → g = 1 := by
  exact LisiSabatini.exists_translated_regular_sylows rho hfaith hsemi p hp hinj P hregular t

/-- Prime-core synchronization for every alternating group. -/
theorem alternating (n : ℕ) :
    CoreSynchronization.{0, uI} (alternatingGroup (Fin n)) := by
  exact LisiSabatini.strongLisiSabatini_alternatingGroup n

/-- Inclusion-minimal synchronization for every symmetric group, including S8. -/
theorem symmetric (n : ℕ) :
    MinimalSynchronization.{0, uI} (Equiv.Perm (Fin n)) := by
  exact LisiSabatini.hasLisiSabatini_symmetricGroup n

end PaperVerification
