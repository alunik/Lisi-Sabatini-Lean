import LisiSabatini.TwoCoreCentralCommutatorJointBudget
import LisiSabatini.TwoCoreDihedralJointBudget
import LisiSabatini.TwoCoreSemidihedralJointBudget
import LisiSabatini.TwoCoreGeneralizedQuaternionJointBudget
import LisiSabatini.TwoCoreMixedJointBudget

/-!
# Dispatching a Hall--Berger shape to the exact two-orbit reserve

Each corrected Hall--Berger shape now has its own sharp counting theorem.
This file contains the deliberately small case split that turns a supplied
shape of the mapped `2`-core into the uniform reserve datum consumed by the
quasiprimitive affine assembly.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uI

variable {r d : ℕ} [Fact r.Prime]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}

local instance fintypeConcreteLinearSubgroupForShapeDispatch
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup
        (ZMod s) (Fin e → ZMod s))) :
    Fintype P :=
  @Fintype.ofFinite P
    (finite_linearSubgroup_of_finite P)

/-- Every corrected Hall--Berger shape supplies the complete exact reserve
for a noncommuting mapped `2`-core in odd characteristic.  The cyclic case
is routed through the already-proved commuting-core theorem. -/
theorem
    oddCharacteristicTwoCoreTwoOrbitReserveData_of_hallBergerShape
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (shape :
      HallBergerTwoCoreShape
        ((pCore 2 K).map K.subtype)) :
    OddCharacteristicTwoCoreTwoOrbitReserveData.{uI} K := by
  cases shape with
  | cyclic hcyclic =>
      have hcomm : IsCommutingPrimeCore 2 K := by
        intro a b
        let aMap :
            (pCore 2 K).map K.subtype :=
          ⟨(a : K), Subgroup.mem_map.mpr
            ⟨a, a.2, rfl⟩⟩
        let bMap :
            (pCore 2 K).map K.subtype :=
          ⟨(b : K), Subgroup.mem_map.mpr
            ⟨b, b.2, rfl⟩⟩
        have habMap :
            aMap * bMap = bMap * aMap :=
          hcyclic.commutative.comm aMap bMap
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg
          (fun x :
            (pCore 2 K).map K.subtype =>
              (x : LinearMap.GeneralLinearGroup
                (ZMod r) (Fin d → ZMod r)))
          habMap
      exact
        oddCharacteristicTwoCoreTwoOrbitReserveData_of_quasiprimitive_of_commuting
          hrTwo hd hqp hcomm
  | extraspecialCyclicProduct hcommutator =>
      exact
        oddCharacteristicTwoCoreTwoOrbitReserveData_of_centralCommutator
          hrTwo hd hqp hcommutator
  | dihedral k hk e =>
      exact
        oddCharacteristicTwoCoreTwoOrbitReserveData_of_dihedral
          hrTwo hd hqp k hk e
  | semidihedral k hk presentation =>
      exact
        oddCharacteristicTwoCoreTwoOrbitReserveData_of_semidihedral
          hrTwo hd hqp k hk presentation
  | generalizedQuaternion n hn e =>
      exact
        oddCharacteristicTwoCoreTwoOrbitReserveData_of_generalizedQuaternion
          hrTwo hd hqp n hn e
  | mixedMaximalClass data =>
      exact
        oddCharacteristicTwoCoreTwoOrbitReserveData_of_mixedCentralProduct
          hrTwo hd hqp data

end LisiSabatini
