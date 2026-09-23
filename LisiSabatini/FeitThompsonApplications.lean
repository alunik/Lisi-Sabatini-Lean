import OddOrder.FeitThompson
import LisiSabatini.OddOrderProof
import LisiSabatini.MixedOddOrderProof
import LisiSabatini.NilpotentIntersectionCorollaries

/-!
# Odd-order applications of the Feit–Thompson theorem

The odd-order proofs in this project retain their solvability hypothesis.
This module discharges that hypothesis using `OddOrder.feitThompson` from
the pinned, vendored OddOrder package. The resulting statements apply to
every finite group of odd order.

This file uses ordinary imports because the pinned OddOrder endpoint uses
Lean's legacy file format. The core library remains a module development.
-/

noncomputable section

namespace LisiSabatini

universe uG uI

/-- Simultaneous Sylow intersections equal the corresponding prime cores
in every finite group of odd order. -/
theorem strongLisiSabatini_of_odd
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    StrongLisiSabatini.{uG, uI} G := by
  let : Group.IsSolvable G := OddOrder.feitThompson hodd
  intro I _ p hp hinj P
  exact strongLisiSabatini_of_solvable_of_odd (G := G) hodd p hp hinj P

/-- The original Lisi–Sabatini property for every finite group of odd order. -/
theorem hasLisiSabatini_of_odd
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    HasLisiSabatini.{uG, uI} G :=
  StrongLisiSabatini.hasLisiSabatini (strongLisiSabatini_of_odd (G := G) hodd)

/-- The mixed simultaneous Sylow-intersection property for every finite
group of odd order. -/
theorem mixedStrongLisiSabatini_of_odd
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    HasMixedTwoSylowCoreSynchronization.{uG, uI} G := by
  let : Group.IsSolvable G := OddOrder.feitThompson hodd
  intro I _ p hp hinj P Q
  exact mixedStrongLisiSabatini_of_solvable_of_odd (G := G) hodd p hp hinj P Q

/-- A nilpotent subgroup of a finite group of odd order has a conjugate
whose intersection with it lies in the Fitting subgroup. -/
theorem nilpotentSelfIntersectionInFitting_of_odd
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    NilpotentSelfIntersectionInFitting G := by
  exact nilpotentSelfIntersectionInFitting_of_strongLS
    (strongLisiSabatini_of_odd (G := G) hodd)

/-- Any two nilpotent subgroups of a finite group of odd order admit a
relative conjugate whose intersection lies in the Fitting subgroup. -/
theorem mixedNilpotentIntersectionInFitting_of_odd
    {G : Type uG} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) :
    MixedNilpotentIntersectionInFitting G := by
  exact mixedNilpotentIntersectionInFitting_of_mixedStrongLS
    (mixedStrongLisiSabatini_of_odd (G := G) hodd)

end LisiSabatini
