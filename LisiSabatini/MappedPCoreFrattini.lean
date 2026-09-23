module

public import LisiSabatini.HobbyFrattiniTheoremCore
public import LisiSabatini.MappedPCoreHall

/-!
# Hobby's theorem for mapped quasiprimitive prime cores

This is the single Hobby consequence used at the quasiprimitive leaves of
the block-stabilizer tower.  Keeping it separate prevents the publication
proof from importing the legacy all-dimensional Frattini frontier.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- A mapped admissible prime core in a quasiprimitive action has a
commutative Frattini subgroup, with no separate Hobby hypothesis. -/
theorem mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
    {r d q : ℕ} [NeZero r] (hr : Nat.Prime r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hq : IsAdmissibleNoncommutingPrimeCore r d q K) :
    IsMulCommutative
      (frattini ((pCore q K).map K.subtype)) := by
  let Pbar := (pCore q K).map K.subtype
  let : Finite K := finite_linearSubgroup_of_finite K
  let : Finite Pbar := finite_linearSubgroup_of_finite Pbar
  have hPbarPGroup : IsPGroup q Pbar :=
    (pCore_isPGroup q K).map K.subtype
  have hPbarHall : HasCyclicCharacteristicAbelianSubgroups Pbar :=
    mapped_pCore_hasCyclicCharacteristicAbelianSubgroups_of_quasiprimitive
      hr hq.1 hq.2.2.1 hqp
  exact hPbarHall.frattini_isMulCommutative hq.1 hPbarPGroup

end LisiSabatini
