module

public import LisiSabatini.NonzeroFixedSpaceSpectrum
public import LisiSabatini.FiniteLinearSubgroup

/-!
# The intrinsic fixed-spectrum nonregular bound

This module contains the representation-theoretic charge used to bound the
nonregular locus of a finite linear group.  It is independent of primitive
tops, block systems, and marker structures, so both quasiprimitive and
imprimitive arguments can depend on it without creating a dependency cycle.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uR uV

variable {R : Type uR} {V : Type uV}
variable [Semiring R] [AddCommGroup V] [Module R V]

/-- The intrinsic fixed-spectrum charge of a finite linear subgroup.  A
trivial group has empty nonregular locus and is assigned charge zero.  For a
nontrivial group the common zero vector is counted once, rather than once per
nonidentity element. -/
noncomputable def fixedSpectrumNonregularBound
    [Finite V]
    (A : Subgroup (LinearMap.GeneralLinearGroup R V)) : ℕ := by
  classical
  letI : Finite A := finite_linearSubgroup_of_finite A
  letI : Fintype A := Fintype.ofFinite A
  exact if A = ⊥ then 0 else
    1 + ∑ a ∈ nonidentityElements A,
      ((fixedVectorSet a.1).ncard - 1)

/-- The canonical spectrum charge bounds the nonregular locus. -/
theorem ncard_nonregularVectors_le_fixedSpectrumNonregularBound
    [Finite V]
    (A : Subgroup (LinearMap.GeneralLinearGroup R V)) :
    (nonregularVectors A).ncard ≤ fixedSpectrumNonregularBound A := by
  classical
  let : Finite A := finite_linearSubgroup_of_finite A
  let : Fintype A := Fintype.ofFinite A
  by_cases hA : A = ⊥
  · subst A
    rw [nonregularVectors_bot]
    simp [fixedSpectrumNonregularBound]
  · simpa [fixedSpectrumNonregularBound, hA] using
      ncard_nonregularVectors_le_one_add_sum_fixedVectorSet_sub_one A

end LisiSabatini
