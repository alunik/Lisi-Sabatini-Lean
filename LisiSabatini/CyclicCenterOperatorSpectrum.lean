module

public import LisiSabatini.CyclicCenterOperatorFixedSpaceRowCore
public import LisiSabatini.FixedSpectrumNonregularBound

/-!
# The compressed cyclic-center operator spectrum

This file isolates the one-group fixed-spectrum estimate used by both the
quasiprimitive prime-core argument and the higher primitive-top marker
packaging.  In particular, it has no dependency on imprimitive block data or
primitive-top marker structures.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

local instance finiteConcreteLinearSubgroupForCyclicCenterOperatorSpectrum
    (r e : ℕ) [NeZero r]
    (P : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin e → ZMod r))) : Finite P :=
  finite_linearSubgroup_of_finite P

/-! ## One cyclic-center operator spectrum -/

/-- The compressed fixed-spectrum charge furnished by the unsplit
cyclic-center operator row. -/
def cyclicCenterOperatorSpectrumBound
    (r e q n : ℕ) : ℕ :=
  1 + (q ^ (2 * n + 1) - 1) * (r ^ (e / q) - 1)

/-- The canonical intrinsic spectrum charge is bounded by the compressed
active-element/operator-fixed-space row. -/
theorem fixedSpectrumNonregularBound_le_cyclicCenterOperatorSpectrumBound
    {r e q : ℕ} [Fact r.Prime]
    (P : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin e → ZMod r)))
    (hP : IsOddCyclicCenterClassTwo q P)
    (hcenter : CenterFixedPointFreeAction r e P) :
    fixedSpectrumNonregularBound P ≤
      cyclicCenterOperatorSpectrumBound
        r e q hP.cyclicCenterStructuralRank := by
  classical
  let : Finite P := finite_linearSubgroup_of_finite P
  let : Fintype P := Fintype.ofFinite P
  have hPne : P ≠ ⊥ := by
    intro hbot
    have : Subsingleton P := by
      rw [hbot]
      infer_instance
    exact (not_nontrivial P) hP.nontrivial
  rw [fixedSpectrumNonregularBound, ite_eq_right hPne]
  simp_rw [← ncard_nonzeroFixedVectorSet]
  rw [sum_nonidentity_ncard_nonzeroFixedVectorSet_eq_active]
  unfold cyclicCenterOperatorSpectrumBound
  apply Nat.add_le_add_left
  calc
    (∑ h ∈ nonzeroFixingElements P,
        (nonzeroFixedVectorSet h.1).ncard) ≤
        ∑ _h ∈ nonzeroFixingElements P,
          (r ^ (e / q) - 1) := by
      apply Finset.sum_le_sum
      intro h hh
      exact hcenter.active_fixed_le_of_cyclicCenterClassTwo hP h hh
    _ = (nonzeroFixingElements P).card *
          (r ^ (e / q) - 1) := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ (q ^ (2 * hP.cyclicCenterStructuralRank + 1) - 1) *
          (r ^ (e / q) - 1) :=
      Nat.mul_le_mul_right _
        (hcenter.card_nonzeroFixingElements_le_cyclicCenterStructuralRank_bound
          hP)

end LisiSabatini
