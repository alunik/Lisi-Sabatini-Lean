import LisiSabatini.AffineTwoOrbitDimensionRecursion
import LisiSabatini.CharacteristicTwoTwoOrbitReserve
import LisiSabatini.OddCharacteristicTwoCoreTwoOrbitReserve

/-!
# Assembly of the quasiprimitive affine two-orbit leaf

The characteristic-two leaf and the commuting mapped `2`-core leaf in odd
characteristic are unconditional.  Consequently the universal
quasiprimitive leaf used by dimension recursion has one remaining affine
input: the sharp joint reserve for a noncommuting mapped `O₂(K)` in odd
characteristic.

This file names exactly that input and performs the parity/commutativity
case split.  It does not install the Hall--Berger structural theorem as an
axiom.
-/

noncomputable section

namespace LisiSabatini

open CharacteristicTwoTwoOrbitReserve

universe uG uI

/-- The exact remaining quasiprimitive affine input.

For every positive-dimensional quasiprimitive action over an odd prime
field whose mapped `2`-core is noncommuting, provide the joint two-orbit
reserve data.  All other quasiprimitive cases are already proved in Lean.
-/
def
    AllOddCharacteristicNoncommutingTwoCoresHaveTwoOrbitReserve :
    Prop :=
  ∀ (r d : ℕ) [Fact r.Prime],
    ∀ K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)),
      r ≠ 2 →
      0 < d →
      IsQuasiprimitiveLinearAction r d K →
      ¬ IsCommutingPrimeCore 2 K →
      OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K

/-- The Hall--Berger noncommuting-`2`-core reserve, together with the
already proved characteristic-two and commuting cases, supplies the
universal quasiprimitive affine leaf needed by dimension recursion. -/
theorem
    allQuasiprimitiveActionsCommonDiagonalAffineTwoOrbitAvoidingTranslates_of_twoCoreReserve
    (htwo :
      AllOddCharacteristicNoncommutingTwoCoresHaveTwoOrbitReserve.{uI}) :
    AllQuasiprimitiveActionsCommonDiagonalAffineTwoOrbitAvoidingTranslates.{uI} := by
  intro r d _ K hd hqp
  by_cases hrTwo : r = 2
  · subst r
    exact
      commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_quasiprimitive_of_charTwo
        hd hqp
  · by_cases hcomm : IsCommutingPrimeCore 2 K
    · exact
        commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_oddChar_of_commutingTwoCore
          hrTwo hd hqp hcomm
    · exact
        commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_quasiprimitive_of_oddChar
          hrTwo hd hqp (htwo r d K hrTwo hd hqp hcomm)

/-- Thus the single noncommuting-`2`-core input closes the solvable mixed
three-row theorem. -/
theorem
    mixedThreeSylowCoreSynchronization_of_solvable_of_twoCoreReserve
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (htwo :
      AllOddCharacteristicNoncommutingTwoCoresHaveTwoOrbitReserve.{uI}) :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G :=
  mixedThreeSylowCoreSynchronization_of_solvable_of_quasiprimitiveTwoOrbit.{uG, uI}
    (allQuasiprimitiveActionsCommonDiagonalAffineTwoOrbitAvoidingTranslates_of_twoCoreReserve
      htwo)

end LisiSabatini
