import LisiSabatini.QuasiprimitiveHallBridgeCore

/-!
# Hall's hypothesis on mapped quasiprimitive prime cores

This file contains the small transport layer needed by the publication
proof.  It is separated from the whole-core Hall development so that the
block-stabilizer tower does not import the later centralizer and index
arguments merely to move Hall's hypothesis across a group isomorphism.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

namespace HasCyclicCharacteristicAbelianSubgroups

variable {G H : Type*} [Group G] [Group H]

/-- Hall's cyclic-characteristic-abelian property is invariant under group
isomorphism. -/
theorem of_mulEquiv
    (hG : HasCyclicCharacteristicAbelianSubgroups G)
    (e : G ≃* H) :
    HasCyclicCharacteristicAbelianSubgroups H := by
  intro A hAchar hAcomm
  let B : Subgroup G := A.comap e.toMonoidHom
  have hBchar : B.Characteristic := by
    rw [Subgroup.characteristic_iff_comap_eq]
    intro phi
    ext x
    change e (phi x) ∈ A ↔ e x ∈ A
    let psi : H ≃* H := e.symm.trans (phi.trans e)
    have hfixed : A.comap psi.toMonoidHom = A := hAchar.fixed psi
    have hpsi : psi (e x) = e (phi x) := by
      simp only [psi, MulEquiv.trans_apply, e.symm_apply_apply]
    rw [← hpsi]
    change e x ∈ A.comap psi.toMonoidHom ↔ e x ∈ A
    rw [hfixed]
  have hBcomm : IsMulCommutative B := by
    refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩⟩
    apply e.injective
    have hxy := hAcomm.1.1
      ⟨e x, x.2⟩ ⟨e y, y.2⟩
    simpa using congrArg Subtype.val hxy
  have hBCyclic : IsCyclic B := hG B hBchar hBcomm
  have hmap : B.map e.toMonoidHom = A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e (e.symm y) ∈ A
      simpa using hy
  have hMapCyclic : IsCyclic (B.map e.toMonoidHom) :=
    (Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).isCyclic.mp
      hBCyclic
  rwa [hmap] at hMapCyclic

end HasCyclicCharacteristicAbelianSubgroups

/-- The faithful image of a quasiprimitive cross-characteristic prime core
inherits Hall's hypothesis. -/
theorem mapped_pCore_hasCyclicCharacteristicAbelianSubgroups_of_quasiprimitive
    {r d q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    HasCyclicCharacteristicAbelianSubgroups
      ((pCore q K).map K.subtype) := by
  let e : pCore q K ≃* (pCore q K).map K.subtype :=
    Subgroup.equivMapOfInjective (pCore q K) K.subtype
      Subtype.coe_injective
  exact
    (pCore_hasCyclicCharacteristicAbelianSubgroups_of_quasiprimitive
      hr hq hqr hqp).of_mulEquiv e

end LisiSabatini
