import Definitions

/-! Trusted statements. These deliberate specification holes are never imported by Solution. -/

namespace PaperVerification

open PaperSpecification
open scoped MonoidAlgebra Pointwise

universe uG uI

/-- The good solvable theorem, with the stronger prime-core conclusion. -/
theorem goodSolvable
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : EveryQuotientHasStar G) :
    CoreSynchronization.{uG, uI} G := by sorry

/-- A nilpotent-subgroup consequence of the good solvable theorem. -/
theorem goodSolvableNilpotent
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : EveryQuotientHasStar G)
    (H : Subgroup G) (hH : Group.IsNilpotent H) :
    ∃ x : G, H ⊓ ((MulAut.conj x) • H) ≤ fitting G := by sorry

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
      g ∈ (P i : Subgroup G) → rho g (v + t i) = v + t i → g = 1 := by sorry

/-- Prime-core synchronization for every alternating group. -/
theorem alternating (n : ℕ) :
    CoreSynchronization.{0, uI} (alternatingGroup (Fin n)) := by sorry

/-- Inclusion-minimal synchronization for every symmetric group, including S8. -/
theorem symmetric (n : ℕ) :
    MinimalSynchronization.{0, uI} (Equiv.Perm (Fin n)) := by sorry

end PaperVerification
