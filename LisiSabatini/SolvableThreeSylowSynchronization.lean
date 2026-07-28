module

public import LisiSabatini.HallBergerClassificationAssembly
public import LisiSabatini.SolvableThreeSylowOfHallBergerClassification

/-!
# Mixed three-row Sylow synchronization for all finite solvable groups

The formalized Berger--Kovács--Newman classification supplies the final
noncommuting `2`-core input in the affine reduction.  Substituting it into
the already-assembled shape dispatcher closes the theorem for every finite
solvable group, without an odd-order or commutative-Sylow-`2` hypothesis.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG uI

/-- **Mixed three-row Sylow-core synchronization for all finite solvable
groups.**

For any finite family of distinct primes and three independently prescribed
Sylow rows, there are common conjugators for the second and third rows whose
triple intersection is the corresponding normal prime core in every row. -/
theorem mixedThreeSylowCoreSynchronization_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G :=
  mixedThreeSylowCoreSynchronization_of_solvable_of_hallBergerClassification
    hallBergerTwoGroupClassification

/-- Same-row three-conjugates specialization for every finite solvable
group. -/
theorem threeConjugatesSylowSynchronization_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    HasThreeConjugatesSylowSynchronization.{uG, uI} G :=
  mixedThree_to_threeConjugates
    mixedThreeSylowCoreSynchronization_of_solvable

end LisiSabatini
