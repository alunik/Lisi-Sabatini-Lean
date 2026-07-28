module

public import LisiSabatini.RepeatedBlockAmplification

/-!
# Nonzero fixed-space spectra

The coarse elementwise bound counts the zero vector once for every
nonidentity group element.  For central products with a large scalar group,
that is wasteful: many nonidentity scalars fix only zero.

This file separates the common zero vector from all nonzero fixed spaces.
It gives the sharper spectrum estimate

`|Nonregular(H)| ≤ 1 + Σ_{1 ≠ h ∈ H} (|Fix(h)| - 1)`.

The summands vanish exactly for fixed-point-free elements.  This is the
appropriate counting interface for cyclic central factors and extraspecial
prime cores in quasi-primitive linear groups.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uR uV

variable {R : Type uR} {V : Type uV}
variable [Semiring R] [AddCommMonoid V] [Module R V]

/-- The nonzero vectors fixed by a specified linear automorphism. -/
def nonzeroFixedVectorSet
    (g : LinearMap.GeneralLinearGroup R V) : Set V :=
  fixedVectorSet g \ {0}

@[simp]
theorem mem_nonzeroFixedVectorSet
    (g : LinearMap.GeneralLinearGroup R V) (v : V) :
    v ∈ nonzeroFixedVectorSet g ↔ g • v = v ∧ v ≠ 0 := by
  simp [nonzeroFixedVectorSet, fixedVectorSet]

/-- The zero vector together with every nonzero fixed space of a
nonidentity subgroup element. -/
def nonzeroFixedSpaceSpectrumEnvelope
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) : Set V :=
  {0} ∪ ⋃ h : {h : H // h ≠ 1}, nonzeroFixedVectorSet h.1.1

/-- The nonregular locus is contained in the nonzero fixed-space spectrum
envelope. -/
theorem nonregularVectors_subset_nonzeroFixedSpaceSpectrumEnvelope
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) :
    nonregularVectors H ⊆ nonzeroFixedSpaceSpectrumEnvelope H := by
  intro v hv
  by_cases hvzero : v = 0
  · exact Set.mem_union_left _ (by simp [hvzero])
  · obtain ⟨h, hh⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hv
    have hhH : (h.1 : H) ≠ 1 := by
      intro hhOne
      apply hh
      exact Subtype.ext hhOne
    apply Set.mem_union_right
    apply Set.mem_iUnion.mpr
    refine ⟨⟨h.1, hhH⟩, ?_⟩
    exact (mem_nonzeroFixedVectorSet h.1.1 v).mpr ⟨h.2, hvzero⟩

/-- Cardinal union bound with zero counted only once. -/
theorem ncard_nonregularVectors_le_one_add_sum_nonzeroFixedVectorSet
    [Finite V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype H] :
    (nonregularVectors H).ncard ≤
      1 + ∑ h ∈ nonidentityElements H,
        (nonzeroFixedVectorSet h.1).ncard := by
  classical
  letI : Fintype {h : H // h ≠ 1} := Fintype.ofFinite _
  calc
    (nonregularVectors H).ncard ≤
        (nonzeroFixedSpaceSpectrumEnvelope H).ncard :=
      Set.ncard_le_ncard
        (nonregularVectors_subset_nonzeroFixedSpaceSpectrumEnvelope H)
        (Set.toFinite _)
    _ ≤ ({0} : Set V).ncard +
        (⋃ h : {h : H // h ≠ 1},
          nonzeroFixedVectorSet h.1.1).ncard := by
      exact Set.ncard_union_le _ _
    _ ≤ 1 + ∑ h : {h : H // h ≠ 1},
          (nonzeroFixedVectorSet h.1.1).ncard := by
      simp only [Set.ncard_singleton]
      exact Nat.add_le_add_left (Set.ncard_iUnion_le_of_fintype _) 1
    _ = 1 + ∑ h ∈ nonidentityElements H,
          (nonzeroFixedVectorSet h.1).ncard := by
      congr 1
      rw [nonidentityElements, ← Finset.filter_ne',
        ← Finset.sum_subtype_eq_sum_filter]
      simp

/-- Removing zero subtracts exactly one point from a finite linear fixed
space. -/
theorem ncard_nonzeroFixedVectorSet
    [Finite V]
    (g : LinearMap.GeneralLinearGroup R V) :
    (nonzeroFixedVectorSet g).ncard = (fixedVectorSet g).ncard - 1 := by
  rw [nonzeroFixedVectorSet,
    Set.ncard_diff_singleton_of_mem (s := fixedVectorSet g)]
  simp [fixedVectorSet]

/-- Fixed-space spectrum form of the nonregular-locus bound. -/
theorem ncard_nonregularVectors_le_one_add_sum_fixedVectorSet_sub_one
    [Finite V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype H] :
    (nonregularVectors H).ncard ≤
      1 + ∑ h ∈ nonidentityElements H,
        ((fixedVectorSet h.1).ncard - 1) := by
  simpa only [ncard_nonzeroFixedVectorSet] using
    ncard_nonregularVectors_le_one_add_sum_nonzeroFixedVectorSet H

end LisiSabatini
