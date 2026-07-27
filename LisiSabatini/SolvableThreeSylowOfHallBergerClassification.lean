import LisiSabatini.OddCharacteristicTwoCoreShapeDispatch
import LisiSabatini.QuasiprimitiveAffineTwoOrbitAssembly

/-!
# From Hall--Berger classification to the solvable synchronization theorem

The structural classification and the six sharp counting branches meet in
one short interface.  This file records that interface separately so the
final structural theorem can be substituted without reopening the affine
argument.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uG uI

local instance fintypeConcreteLinearSubgroupForHallBergerDispatch
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup
        (ZMod s) (Fin e → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P
    (finite_linearSubgroup_of_finite P)

/-- A proof of the corrected Hall--Berger classification supplies the sole
remaining noncommuting two-core reserve input. -/
theorem
    allOddCharacteristicNoncommutingTwoCoresHaveTwoOrbitReserve_of_hallBergerClassification
    (hclass :
      HallBergerTwoGroupClassificationStatement.{0}) :
    AllOddCharacteristicNoncommutingTwoCoresHaveTwoOrbitReserve.{uI} := by
  intro r d _ K hrTwo hd hqp _hnoncomm
  let F :=
    mappedTwoCoreQuasiprimitiveFrontier hrTwo hqp
  obtain ⟨shape⟩ :=
    hclass
      ((pCore 2 K).map K.subtype)
      F.pGroup F.hall
  exact
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_hallBergerShape
      hrTwo hd hqp shape

/-- Consequently, the corrected Hall--Berger classification closes mixed
three-row Sylow-core synchronization for every finite solvable group. -/
theorem
    mixedThreeSylowCoreSynchronization_of_solvable_of_hallBergerClassification
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hclass :
      HallBergerTwoGroupClassificationStatement.{0}) :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G :=
  mixedThreeSylowCoreSynchronization_of_solvable_of_twoCoreReserve
    (allOddCharacteristicNoncommutingTwoCoresHaveTwoOrbitReserve_of_hallBergerClassification
      hclass)

end LisiSabatini
