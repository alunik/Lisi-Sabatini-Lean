module

public import Mathlib.Data.Set.Card.Arithmetic
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Minimal bad-set core for common affine translates

This file contains only the finite-union and nonregular-vector primitives
used by the odd-order proof.  Translated-union and cardinal-bound convenience
theorems remain in `CommonTranslate.lean`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

/-- A finite family of sets whose `ncard`s sum to less than the cardinality of
the ambient finite type has a common point outside every member. -/
theorem exists_avoids_of_sum_ncard_lt
    {I V : Type*} [Fintype I] [Finite V]
    (bad : I → Set V)
    (hcard : ∑ i, (bad i).ncard < Nat.card V) :
    ∃ v : V, ∀ i, v ∉ bad i := by
  by_contra h
  push Not at h
  have hcover : (⋃ i, bad i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro v
    obtain ⟨i, hi⟩ := h v
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  have hunion := Set.ncard_iUnion_le_of_fintype bad
  rw [hcover, Set.ncard_univ] at hunion
  exact (not_le_of_gt hcard) hunion

/-- Vectors with nontrivial stabilizer for a subgroup of a general linear
group. -/
def nonregularVectors
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) : Set V :=
  {v | MulAction.stabilizer H v ≠ ⊥}

/-- The trivial acting group has no nonregular vectors. -/
@[simp]
theorem nonregularVectors_bot
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V] :
    nonregularVectors
        (⊥ : Subgroup (LinearMap.GeneralLinearGroup R V)) = ∅ := by
  ext v
  simp only [nonregularVectors, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hne
  apply hne
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g _hg
  apply Subtype.ext
  exact g.2

/-- Indices at which the prescribed linear group acts nontrivially. -/
noncomputable def activeLinearIndices
    {I R V : Type*} [Fintype I] [Semiring R] [AddCommMonoid V] [Module R V]
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R V)) : Finset I := by
  classical
  exact Finset.univ.filter (fun i ↦ H i ≠ ⊥)

/-- Enlarging the acting linear group can only enlarge its set of nonregular
vectors. -/
theorem nonregularVectors_mono
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    {H K : Subgroup (LinearMap.GeneralLinearGroup R V)} (hHK : H ≤ K) :
    nonregularVectors H ⊆ nonregularVectors K := by
  intro v hv
  obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hv
  let gK : K := ⟨g.1.1, hHK g.1.2⟩
  have hgK_ne : gK ≠ 1 := by
    intro h
    apply hg
    apply Subtype.ext
    apply Subtype.ext
    simpa [gK] using congrArg Subtype.val h
  apply Subgroup.ne_bot_iff_exists_ne_one.mpr
  refine ⟨⟨gK, ?_⟩, ?_⟩
  · rw [MulAction.mem_stabilizer_iff]
    change (g.1 : H) • v = v
    exact g.2
  · exact fun h ↦ hgK_ne (congrArg Subtype.val h)

end LisiSabatini
