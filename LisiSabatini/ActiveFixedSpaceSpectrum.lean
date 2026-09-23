module

public import LisiSabatini.NonzeroFixedSpaceSpectrum
public import LisiSabatini.FixedSpaceCodimension
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Compressing the fixed-space spectrum to active elements

Only those nonidentity elements that fix a nonzero vector contribute to the
nonzero fixed-space spectrum.  This file isolates that finite set and gives
the bound

`|Nonregular(H)| ≤ 1 + (# active elements) * b`

when every active element fixes at most `b` nonzero vectors.  Large cyclic
scalar factors disappear from the active count, which is the feature needed
for extraspecial central products.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uR uV

variable {R : Type uR} {V : Type uV}
variable [Semiring R] [AddCommMonoid V] [Module R V]

/-- Nonidentity subgroup elements with at least one nonzero fixed vector. -/
noncomputable def nonzeroFixingElements
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype H] :
    Finset H := by
  classical
  exact (nonidentityElements H).filter fun h ↦
    (nonzeroFixedVectorSet h.1).Nonempty

@[simp]
theorem mem_nonzeroFixingElements
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype H]
    (h : H) :
    h ∈ nonzeroFixingElements H ↔
      h ≠ 1 ∧ (nonzeroFixedVectorSet h.1).Nonempty := by
  classical
  simp [nonzeroFixingElements]

/-- Inactive nonidentity elements contribute zero to the nonzero fixed-space
spectrum. -/
theorem sum_nonidentity_ncard_nonzeroFixedVectorSet_eq_active
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype H] :
    ∑ h ∈ nonidentityElements H, (nonzeroFixedVectorSet h.1).ncard =
      ∑ h ∈ nonzeroFixingElements H,
        (nonzeroFixedVectorSet h.1).ncard := by
  classical
  rw [nonzeroFixingElements]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro h hh hha
  have hnot : ¬(nonzeroFixedVectorSet h.1).Nonempty := by
    intro hne
    exact hha (by
      exact Finset.mem_filter.mpr ⟨hh, hne⟩)
  have hempty : nonzeroFixedVectorSet h.1 = ∅ := Set.not_nonempty_iff_eq_empty.mp hnot
  simp [hempty]

/-- Bound the nonregular locus by the number of active nonidentity elements
and a uniform nonzero fixed-set bound. -/
theorem ncard_nonregularVectors_le_one_add_active_mul
    [Finite V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype H]
    (a b : ℕ)
    (hactive : (nonzeroFixingElements H).card ≤ a)
    (hfixed : ∀ h ∈ nonzeroFixingElements H,
      (nonzeroFixedVectorSet h.1).ncard ≤ b) :
    (nonregularVectors H).ncard ≤ 1 + a * b := by
  calc
    (nonregularVectors H).ncard ≤
        1 + ∑ h ∈ nonidentityElements H,
          (nonzeroFixedVectorSet h.1).ncard :=
      ncard_nonregularVectors_le_one_add_sum_nonzeroFixedVectorSet H
    _ = 1 + ∑ h ∈ nonzeroFixingElements H,
          (nonzeroFixedVectorSet h.1).ncard := by
      rw [sum_nonidentity_ncard_nonzeroFixedVectorSet_eq_active]
    _ ≤ 1 + (nonzeroFixingElements H).card * b := by
      apply Nat.add_le_add_left
      calc
        ∑ h ∈ nonzeroFixingElements H,
            (nonzeroFixedVectorSet h.1).ncard ≤
            ∑ _h ∈ nonzeroFixingElements H, b := by
          apply Finset.sum_le_sum
          intro h hh
          exact hfixed h hh
        _ = (nonzeroFixingElements H).card * b := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ 1 + a * b :=
      Nat.add_le_add_left (Nat.mul_le_mul_right b hactive) 1

/-- Over a prime field, the number of nonzero fixed vectors is exactly one
less than the cardinality of the fixed subspace. -/
theorem ncard_nonzeroFixedVectorSet_eq_pow_finrank_sub_one_zmod
    {r : ℕ} [Fact (Nat.Prime r)]
    {W : Type*} [AddCommGroup W] [Module (ZMod r) W]
    [Module.Finite (ZMod r) W]
    (g : LinearMap.GeneralLinearGroup (ZMod r) W) :
    (nonzeroFixedVectorSet g).ncard =
      r ^ Module.finrank (ZMod r) (fixedSpace g) - 1 := by
  let : Finite W := Module.finite_of_finite (ZMod r)
  rw [ncard_nonzeroFixedVectorSet,
    ncard_fixedVectorSet_eq_pow_finrank_fixedSpace_zmod]

end LisiSabatini
