import LisiSabatini.CyclicFrattiniCentralityCore
import LisiSabatini.HallFrattiniCyclicCenterCore
import LisiSabatini.MappedPCoreHall

/-!
# Cyclic-center class-two structure for mapped quasiprimitive prime cores

This file packages the exact structural consequence consumed at a
quasiprimitive leaf.  It is separated from the small-order Hobby regression
theorems that historically shared its module.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

local instance finiteConcreteLinearSubgroupForMappedPCoreCyclicCenter
    (r d : ℕ) [NeZero r]
    (H : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    Finite H :=
  finite_linearSubgroup_of_finite H

/-- Abelianness of the one Frattini subgroup needed by Hall's reduction
gives the cyclic-center class-two structure on the ambient prime group. -/
def oddCyclicCenterClassTwo_of_hall_of_frattini_isMulCommutative
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hHall : HasCyclicCharacteristicAbelianSubgroups P)
    (hnoncomm : ¬ IsMulCommutative P)
    (hPhiComm : IsMulCommutative (frattini P)) :
    IsOddCyclicCenterClassTwo p P := by
  letI : IsMulCommutative (frattini P) := hPhiComm
  have hPhiCyclic : IsCyclic (frattini P) :=
    hHall.isCyclic (frattini P)
  exact oddCyclicCenterClassTwo_of_hall_of_frattini_le_center
    hp hpOdd hPp hHall hnoncomm
      (frattini_le_center_of_odd_of_isCyclic
        hp hpOdd hPp hPhiCyclic)

/-- A quasiprimitive mapped prime core acquires cyclic-center class-two
structure from commutativity of its own Frattini subgroup. -/
theorem mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
    {r d q : ℕ} [NeZero r] (hr : Nat.Prime r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hq : IsAdmissibleNoncommutingPrimeCore r d q K)
    (hPhiComm : IsMulCommutative
      (frattini ((pCore q K).map K.subtype))) :
    IsOddCyclicCenterClassTwo q ((pCore q K).map K.subtype) := by
  rcases hq with ⟨hqPrime, hqTwo, hqr, _hcore, hnoncomm⟩
  let Pbar := (pCore q K).map K.subtype
  let e : pCore q K ≃* Pbar :=
    Subgroup.equivMapOfInjective (pCore q K) K.subtype
      Subtype.coe_injective
  have hPbarPGroup : IsPGroup q Pbar :=
    (pCore_isPGroup q K).map K.subtype
  have hPbarHall : HasCyclicCharacteristicAbelianSubgroups Pbar :=
    mapped_pCore_hasCyclicCharacteristicAbelianSubgroups_of_quasiprimitive
      hr hqPrime hqr hqp
  have hPbarNoncomm : ¬ IsMulCommutative Pbar := by
    intro hcomm
    apply hnoncomm
    intro a b
    change a * b = b * a
    apply e.injective
    exact hcomm.1.1 (e a) (e b)
  exact oddCyclicCenterClassTwo_of_hall_of_frattini_isMulCommutative
    hqPrime (hqPrime.odd_of_ne_two hqTwo) hPbarPGroup hPbarHall
      hPbarNoncomm hPhiComm

end LisiSabatini
