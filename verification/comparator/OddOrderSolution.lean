import Definitions
import LisiSabatini.FeitThompsonApplications

/-! Odd-order proofs using the actual formalized Feit–Thompson theorem. -/

namespace PaperVerification

open PaperSpecification
open scoped Pointwise

universe uG uI

/-- Every finite group of odd order has simultaneous prime-core intersections. -/
theorem oddOrderCore
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : CoreSynchronization.{uG, uI} G := by
  exact LisiSabatini.strongLisiSabatini_of_odd hodd

/-- The original inclusion-minimal conclusion for every finite group of odd order. -/
theorem oddOrderMinimal
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : MinimalSynchronization.{uG, uI} G := by
  exact LisiSabatini.hasLisiSabatini_of_odd hodd

/-- Odd-order nilpotent self-intersections lie in the Fitting subgroup. -/
theorem oddOrderNilpotent
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (H : Subgroup G) (hH : Group.IsNilpotent H) :
    ∃ x : G, H ⊓ ((MulAut.conj x) • H) ≤ fitting G := by
  exact LisiSabatini.nilpotentSelfIntersectionInFitting_of_odd hodd H hH

/-- The mixed nilpotent corollary for every finite group of odd order. -/
theorem oddOrderMixedNilpotent
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (H K : Subgroup G) (hH : Group.IsNilpotent H) (hK : Group.IsNilpotent K) :
    ∃ x : G, H ⊓ ((MulAut.conj x) • K) ≤ fitting G := by
  exact LisiSabatini.mixedNilpotentIntersectionInFitting_of_odd hodd H K hH hK

end PaperVerification
