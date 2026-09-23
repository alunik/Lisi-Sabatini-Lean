module

public import LisiSabatini.HallClassTwoCore
public import LisiSabatini.QuasiprimitivePrimeCoreCore

/-!
# Minimal Hall input for quasiprimitive prime cores
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped IsMulCommutative

set_option backward.isDefEq.respectTransparency false

/-- Every characteristic abelian subgroup of a cross-characteristic prime
core of a quasiprimitive linear group is cyclic. -/
theorem pCore_hasCyclicCharacteristicAbelianSubgroups_of_quasiprimitive
    {r d q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    HasCyclicCharacteristicAbelianSubgroups (pCore q K) := by
  intro A hAchar hAcomm
  let : A.Characteristic := hAchar
  let : IsMulCommutative A := hAcomm
  let Abar : Subgroup K := A.map (pCore q K).subtype
  have hAbarNormal : Abar.Normal := by
    dsimp only [Abar]
    exact ConjAct.normal_of_characteristic_of_normal
  have hAbarPGroup : IsPGroup q Abar := by
    dsimp only [Abar]
    exact ((pCore_isPGroup q K).to_subgroup A).map
      (pCore q K).subtype
  have hAbarComm : ∀ a b : Abar, Commute a b := by
    let : IsMulCommutative Abar := by
      dsimp only [Abar]
      exact Subgroup.map_isMulCommutative A (pCore q K).subtype
    intro a b
    exact Commute.all a b
  have hAbarCyclic : IsCyclic Abar :=
    normalAbelianPSubgroup_isCyclic_of_quasiprimitive
      hr hq hqr hqp Abar hAbarNormal hAbarPGroup hAbarComm
  exact (Subgroup.equivMapOfInjective A (pCore q K).subtype
    Subtype.coe_injective).isCyclic.mpr hAbarCyclic

end LisiSabatini
