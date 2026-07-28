module

public import LisiSabatini.CyclicCenterSymplectic

/-!
# Transport of cyclic-center class-two structure

The quasiprimitive pipeline naturally meets the same prime core in two
forms: as an internal subgroup of the acting group and as its faithful image
in the ambient general linear group.  This file proves that the intrinsic
cyclic-center class-two package, its central quotient, and its canonical
symplectic rank are invariant under a group isomorphism.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- A group isomorphism induces an isomorphism of the quotients by the
centers. -/
def quotientCenterMulEquiv
    {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (G ⧸ Subgroup.center G) ≃* (H ⧸ Subgroup.center H) :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center H) e (by
    rw [Subgroup.map_equiv_eq_comap_symm]
    ext h
    exact MulEquivClass.apply_mem_center_iff e.symm)

namespace IsOddCyclicCenterClassTwo

variable {p : ℕ} {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
private theorem map_commutator_eq_of_mulEquiv (e : G ≃* H) :
    (commutator G).map e.toMonoidHom = commutator H := by
  rw [map_commutator_eq,
    e.toMonoidHom.range_eq_top_of_surjective e.surjective]
  rfl

omit [Finite G] [Finite H] in
private theorem mem_commutator_map_iff (e : G ≃* H) (x : G) :
    e x ∈ commutator H ↔ x ∈ commutator G := by
  rw [← map_commutator_eq_of_mulEquiv e, Subgroup.mem_map_equiv]
  simp

/-- The intrinsic odd cyclic-center class-two package is invariant under a
group isomorphism. -/
theorem of_mulEquiv
    (hG : IsOddCyclicCenterClassTwo p G) (e : G ≃* H) :
    IsOddCyclicCenterClassTwo p H := by
  have hHp : IsPGroup p H := hG.pGroup.of_equiv e
  have hHnoncomm : ¬ IsMulCommutative H := by
    intro hcomm
    apply hG.noncommutative
    refine ⟨⟨fun x y ↦ e.injective ?_⟩⟩
    simpa using hcomm.1.1 (e x) (e y)
  have hHclass : commutator H ≤ Subgroup.center H := by
    intro c hc
    have hcG : e.symm c ∈ commutator G := by
      exact (mem_commutator_map_iff e (e.symm c)).mp (by simpa)
    have hcCenter := hG.commutator_le_center hcG
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.symm.injective
    simpa using (Subgroup.mem_center_iff.mp hcCenter (e.symm y))
  have hHcenter : IsCyclic (Subgroup.center H) :=
    (Subgroup.centerCongr e).isCyclic.mp hG.center_isCyclic
  have hHpow : ∀ c : commutator H, (c : H) ^ p = 1 := by
    intro c
    have hcG : e.symm (c : H) ∈ commutator G := by
      exact (mem_commutator_map_iff e (e.symm (c : H))).mp (by simp)
    let cG : commutator G := ⟨e.symm (c : H), hcG⟩
    apply e.symm.injective
    simpa [cG] using hG.commutator_pow_prime_eq_one cG
  exact
    { prime := hG.prime
      odd := hG.odd
      pGroup := hHp
      noncommutative := hHnoncomm
      commutator_le_center := hHclass
      center_isCyclic := hHcenter
      commutator_eq_centerPrimeKernel :=
        commutator_eq_centerPrimeKernel_of_classTwo_of_center_isCyclic
          hG.prime hHp hHclass hHcenter hHnoncomm hHpow }

/-- The canonical symplectic rank is invariant under transport. -/
theorem cyclicCenterStructuralRank_of_mulEquiv
    (hG : IsOddCyclicCenterClassTwo p G) (e : G ≃* H) :
    (hG.of_mulEquiv e).cyclicCenterStructuralRank =
      hG.cyclicCenterStructuralRank := by
  have hcard : Nat.card (H ⧸ Subgroup.center H) =
      Nat.card (G ⧸ Subgroup.center G) :=
    Nat.card_congr (quotientCenterMulEquiv e).symm
  have hpow :
      p ^ (2 * (hG.of_mulEquiv e).cyclicCenterStructuralRank) =
        p ^ (2 * hG.cyclicCenterStructuralRank) := by
    rw [← (hG.of_mulEquiv e).cyclicCenterStructuralRank_card_quotient_center,
      ← hG.cyclicCenterStructuralRank_card_quotient_center]
    exact hcard
  have hexp :
      2 * (hG.of_mulEquiv e).cyclicCenterStructuralRank =
        2 * hG.cyclicCenterStructuralRank :=
    Nat.pow_right_injective hG.prime.two_le hpow
  omega

end IsOddCyclicCenterClassTwo

end LisiSabatini
