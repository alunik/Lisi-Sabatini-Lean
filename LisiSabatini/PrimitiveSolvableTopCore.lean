import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Primitive permutation action core

Only the regular-action predicate and the elementary action lemmas consumed
by the odd-order proof are kept in this module. The solvable-group
consequences remain available from `PrimitiveSolvableTop`.
-/

noncomputable section

namespace LisiSabatini

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ}
variable [Group G] [MulAction G Ω]

/-- A subgroup action is regular: it is transitive and semiregular. -/
def IsRegularSubgroupAction (N : Subgroup G) (Ω : Type uΩ)
    [MulAction G Ω] : Prop :=
  MulAction.IsPretransitive N Ω ∧ IsCancelSMul N Ω

namespace PrimitiveSolvableTop

/-- In a faithful action, a nontrivial subgroup cannot fix every point. -/
theorem fixedPoints_ne_univ_of_ne_bot
    [FaithfulSMul G Ω] {N : Subgroup G} (hN : N ≠ ⊥) :
    MulAction.fixedPoints N Ω ≠ Set.univ := by
  intro hfixed
  apply hN
  apply N.eq_bot_iff_forall.mpr
  intro n hn
  apply FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := Ω)
  intro ω
  rw [one_smul]
  exact Set.eq_univ_iff_forall.mp hfixed ω ⟨n, hn⟩

/-- Every nontrivial normal subgroup of a faithful primitive action is
transitive. -/
theorem isPretransitive_of_normal_of_ne_bot
    [FaithfulSMul G Ω] [MulAction.IsPreprimitive G Ω]
    {N : Subgroup G} [N.Normal] (hN : N ≠ ⊥) :
    MulAction.IsPretransitive N Ω := by
  exact MulAction.IsQuasiPreprimitive.isPretransitive_of_normal
    (fixedPoints_ne_univ_of_ne_bot hN)

/-- An abelian transitive subgroup of a faithful ambient action acts
semiregularly. -/
theorem isCancelSMul_of_isMulCommutative_of_isPretransitive
    [FaithfulSMul G Ω] [Nonempty Ω]
    (N : Subgroup G) [IsMulCommutative N]
    [MulAction.IsPretransitive N Ω] :
    IsCancelSMul N Ω := by
  rw [isCancelSMul_iff_eq_one_of_smul_eq]
  intro n ω hnω
  have hnω' : (n : G) • ω = ω := hnω
  apply Subtype.ext
  change (n : G) = 1
  apply FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := Ω)
  intro ω'
  obtain ⟨m, rfl⟩ := MulAction.exists_smul_eq N ω ω'
  simp only [MulAction.subgroup_smul_def, one_smul]
  calc
    (n : G) • ((m : G) • ω) = ((n : G) * (m : G)) • ω :=
      smul_smul _ _ _
    _ = ((m : G) * (n : G)) • ω := by
      rw [show (n : G) * m = m * n by
        exact congrArg Subtype.val (mul_comm n m)]
    _ = (m : G) • ((n : G) • ω) := (smul_smul _ _ _).symm
    _ = (m : G) • ω := congrArg ((m : G) • ·) hnω'

/-- The ambient centralizer of an abelian transitive subgroup in a faithful
action is contained in that subgroup. -/
theorem centralizer_le_of_isMulCommutative_of_isPretransitive
    [FaithfulSMul G Ω] [Nonempty Ω]
    (N : Subgroup G) [IsMulCommutative N]
    [MulAction.IsPretransitive N Ω] :
    Subgroup.centralizer (N : Set G) ≤ N := by
  intro g hg
  let ω : Ω := Classical.choice inferInstance
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N ω (g • ω)
  have hn' : (n : G) • ω = g • ω := hn
  have hgn : g = (n : G) := by
    apply FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := Ω)
    intro ω'
    obtain ⟨m, rfl⟩ := MulAction.exists_smul_eq N ω ω'
    change g • ((m : G) • ω) = (n : G) • ((m : G) • ω)
    calc
      g • ((m : G) • ω) = (g * (m : G)) • ω := smul_smul _ _ _
      _ = ((m : G) * g) • ω := by rw [hg (m : G) m.property]
      _ = (m : G) • (g • ω) := (smul_smul _ _ _).symm
      _ = (m : G) • ((n : G) • ω) := congrArg ((m : G) • ·) hn'.symm
      _ = ((m : G) * (n : G)) • ω := smul_smul _ _ _
      _ = ((n : G) * (m : G)) • ω := by
        rw [show (m : G) * (n : G) = n * m by
          exact congrArg Subtype.val (mul_comm m n)]
      _ = (n : G) • ((m : G) • ω) := (smul_smul _ _ _).symm
  rw [hgn]
  exact n.property

/-- An abelian transitive subgroup of a faithful action is
self-centralizing in the ambient group. -/
theorem centralizer_eq_of_isMulCommutative_of_isPretransitive
    [FaithfulSMul G Ω] [Nonempty Ω]
    (N : Subgroup G) [IsMulCommutative N]
    [MulAction.IsPretransitive N Ω] :
    Subgroup.centralizer (N : Set G) = N := by
  apply le_antisymm
  · exact centralizer_le_of_isMulCommutative_of_isPretransitive
      (Ω := Ω) N
  · exact Subgroup.le_centralizer N

end PrimitiveSolvableTop

end LisiSabatini
