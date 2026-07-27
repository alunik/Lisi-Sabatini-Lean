import LisiSabatini.CommutativeSylowTwoCase
import LisiSabatini.MixedOddOrderProof
import LisiSabatini.NilpotentIntersectionCorollaries
import LisiSabatini.OddOrderProof
import LisiSabatini.SolvableThreeSylowSynchronization

/-!
# Nilpotent-intersection applications

Concrete consequences of the synchronized Sylow theorems for finite
solvable groups.  The general implications are kept separately in
`NilpotentIntersectionCorollaries`.
-/

noncomputable section

namespace LisiSabatini

universe uG

/-- Every three nilpotent subgroups of a finite solvable group admit two
relative conjugates whose common intersection lies in the Fitting
subgroup. -/
theorem threeNilpotentIntersectionInFitting_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    ThreeNilpotentIntersectionInFitting G :=
  threeNilpotentIntersectionInFitting_of_mixedThree
    mixedThreeSylowCoreSynchronization_of_solvable

/-- Finite solvable groups of odd order satisfy the nilpotent
self-intersection Fitting property. -/
theorem nilpotentSelfIntersectionInFitting_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    NilpotentSelfIntersectionInFitting G :=
  nilpotentSelfIntersectionInFitting_of_strongLS
    (strongLisiSabatini_of_solvable_of_odd hodd)

/-- Finite solvable groups of odd order satisfy the mixed
nilpotent-intersection Fitting property. -/
theorem mixedNilpotentIntersectionInFitting_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    MixedNilpotentIntersectionInFitting G :=
  mixedNilpotentIntersectionInFitting_of_mixedStrongLS
    (mixedStrongLisiSabatini_of_solvable_of_odd hodd)

/-- Finite solvable groups with commutative Sylow `2`-subgroups satisfy
the three-nilpotent-subgroup Fitting containment. -/
theorem
    threeNilpotentIntersectionInFitting_of_solvable_of_commutativeSylowTwo
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hG : HasCommutativeSylowSubgroups 2 G) :
    ThreeNilpotentIntersectionInFitting G :=
  threeNilpotentIntersectionInFitting_of_mixedThree
    (mixedThreeSylowCoreSynchronization_of_solvable_of_commutativeSylowTwo
      hG)

end LisiSabatini
