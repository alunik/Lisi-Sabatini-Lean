import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Semiregular permutation subgroups

The two proof-level predicates used by the odd-order imprimitive argument.
The marker constructions built from them remain in `SemiregularTop`.
-/

namespace LisiSabatini

universe uI

variable {I : Type uI}

/-- A permutation subgroup is semiregular at `ω` when its point stabilizer
there is trivial. -/
def IsSemiregularAt
    (T : Subgroup (Equiv.Perm I)) (ω : I) : Prop :=
  MulAction.stabilizer T ω = ⊥

/-- A permutation subgroup is semiregular when it is semiregular at every
point. Transitivity is not required. -/
def IsSemiregularPermutationSubgroup
    (T : Subgroup (Equiv.Perm I)) : Prop :=
  ∀ ω, IsSemiregularAt T ω

/-- The trivial permutation subgroup is semiregular at every point. -/
theorem isSemiregularAt_bot (ω : I) :
    IsSemiregularAt (⊥ : Subgroup (Equiv.Perm I)) ω := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro σ _hσ
  exact Subsingleton.elim σ 1

/-- The trivial permutation subgroup is semiregular. -/
theorem isSemiregularPermutationSubgroup_bot :
    IsSemiregularPermutationSubgroup (⊥ : Subgroup (Equiv.Perm I)) :=
  isSemiregularAt_bot

end LisiSabatini
