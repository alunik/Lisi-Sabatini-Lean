import Definitions

/-! Trusted odd-order statements; no Feit–Thompson theorem is imported. -/

namespace PaperVerification

open PaperSpecification
open scoped Pointwise

universe uG uI

/-- Every finite group of odd order has simultaneous prime-core intersections. -/
theorem oddOrderCore
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : CoreSynchronization.{uG, uI} G := by sorry

/-- The original inclusion-minimal conclusion for every finite group of odd order. -/
theorem oddOrderMinimal
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) : MinimalSynchronization.{uG, uI} G := by sorry

/-- Odd-order nilpotent self-intersections lie in the Fitting subgroup. -/
theorem oddOrderNilpotent
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (H : Subgroup G) (hH : Group.IsNilpotent H) :
    ∃ x : G, H ⊓ ((MulAut.conj x) • H) ≤ fitting G := by sorry

/-- The mixed nilpotent corollary for every finite group of odd order. -/
theorem oddOrderMixedNilpotent
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G))
    (H K : Subgroup G) (hH : Group.IsNilpotent H) (hK : Group.IsNilpotent K) :
    ∃ x : G, H ⊓ ((MulAut.conj x) • K) ≤ fitting G := by sorry

end PaperVerification
