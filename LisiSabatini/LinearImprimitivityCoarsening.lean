module

public import LisiSabatini.LinearImprimitivitySystem
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Data.Fintype.EquivFin

/-!
# Equivariant coarsening of linear systems of imprimitivity

A coarsest nontrivial linear block system has primitive permutation top.
Using that observation in the recursive NCAS argument requires a concrete
operation that groups a finer internal direct sum along the fibres of an
equivariant quotient of its block set.

This file supplies that operation.  `EquivariantBlockIndexQuotient` records a
surjective map of finite block indices together with the induced permutation
action.  The coarse block over `j` is the internal sum of all fine blocks in
the fibre over `j`.  The main theorem proves that these sums are again
nonzero, internal, and permuted exactly by the given quotient action.

No primitivity or irreducibility is assumed here.  Those are selection
properties of a particular quotient; this module proves the previously
missing linear-algebraic coarsening step once that finite quotient is chosen.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uJ uR uV

variable {I : Type uI} {J : Type uJ} {R : Type uR} {V : Type uV}
variable [Ring R] [AddCommGroup V] [Module R V]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

/-- A finite equivariant quotient of the block indices of a linear system of
imprimitivity. -/
structure EquivariantBlockIndexQuotient
    (S : LinearImprimitivitySystem (I := I) K) where
  /-- The coarse block containing each fine block. -/
  indexMap : I → J
  /-- Every coarse block has at least one fine constituent. -/
  indexMap_surjective : Function.Surjective indexMap
  /-- The induced action on coarse blocks. -/
  blockPerm : K →* Equiv.Perm J
  /-- The quotient map intertwines the fine and coarse permutation actions. -/
  indexMap_equivariant : ∀ (g : K) (i : I),
    indexMap (S.blockPerm g i) = blockPerm g (indexMap i)

namespace EquivariantBlockIndexQuotient

variable {S : LinearImprimitivitySystem (I := I) K}

/-- The coarse submodule is the supremum of the fine blocks in one fibre. -/
def coarseBlock (Q : EquivariantBlockIndexQuotient (J := J) S)
    (j : J) : Submodule R V :=
  ⨆ i, ⨆ (_ : Q.indexMap i = j), S.block i

omit [Fintype J] [DecidableEq J] in
/-- Each fine block lies in its prescribed coarse block. -/
theorem block_le_coarseBlock
    (Q : EquivariantBlockIndexQuotient (J := J) S) (i : I) :
    S.block i ≤ Q.coarseBlock (Q.indexMap i) := by
  exact le_iSup_of_le i (le_iSup_of_le rfl le_rfl)

omit [Fintype J] [DecidableEq J] in
/-- Surjectivity and nondegeneracy of the fine system make every coarse block
nonzero. -/
theorem coarseBlock_ne_bot
    (Q : EquivariantBlockIndexQuotient (J := J) S) (j : J) :
    Q.coarseBlock j ≠ ⊥ := by
  obtain ⟨i, hi⟩ := Q.indexMap_surjective j
  intro hj
  apply S.block_ne_bot i
  apply le_antisymm
  · have hle : S.block i ≤ Q.coarseBlock j := by
      simpa [hi] using Q.block_le_coarseBlock i
    simpa [hj] using hle
  · exact bot_le

omit [Fintype J] [DecidableEq J] in
/-- The grouped fibre sums remain independent. -/
theorem iSupIndep_coarseBlock
    (Q : EquivariantBlockIndexQuotient (J := J) S) :
    iSupIndep Q.coarseBlock := by
  rw [iSupIndep_def]
  intro j
  let A : Set I := {i | Q.indexMap i = j}
  let B : Set I := {i | Q.indexMap i ≠ j}
  have hAB : Disjoint A B := by
    rw [Set.disjoint_left]
    intro i hiA hiB
    exact hiB hiA
  have hAfinite : A.Finite := Set.toFinite A
  have hdisjoint :
      Disjoint (⨆ i ∈ A, S.block i) (⨆ i ∈ B, S.block i) :=
    S.iSupIndep_block.disjoint_biSup_biSup' hAB hAfinite
  have hright :
      (⨆ k, ⨆ (_ : k ≠ j), Q.coarseBlock k) ≤
        ⨆ i ∈ B, S.block i := by
    refine iSup_le fun k ↦ iSup_le fun hkj ↦ ?_
    refine iSup_le fun i ↦ iSup_le fun hik ↦ ?_
    have hij : Q.indexMap i ≠ j := by
      intro hij
      exact hkj (hik.symm.trans hij)
    exact le_iSup_of_le i (le_iSup_of_le hij le_rfl)
  exact hdisjoint.mono_right hright

omit [Fintype J] [DecidableEq J] in
/-- The coarse blocks still span the whole ambient module. -/
theorem iSup_coarseBlock_eq_top
    (Q : EquivariantBlockIndexQuotient (J := J) S) :
    ⨆ j, Q.coarseBlock j = ⊤ := by
  apply le_antisymm
  · exact le_top
  · rw [← S.iSup_block_eq_top]
    refine iSup_le fun i ↦ ?_
    exact le_iSup_of_le (Q.indexMap i) (Q.block_le_coarseBlock i)

omit [Fintype J] in
/-- The fibre sums form an internal direct sum. -/
theorem coarseBlock_internal
    (Q : EquivariantBlockIndexQuotient (J := J) S) :
    DirectSum.IsInternal Q.coarseBlock :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    Q.iSupIndep_coarseBlock Q.iSup_coarseBlock_eq_top

omit [Fintype J] [DecidableEq J] in
/-- A group element maps a coarse block onto the coarse block prescribed by
the quotient permutation action. -/
theorem map_coarseBlock
    (Q : EquivariantBlockIndexQuotient (J := J) S)
    (g : K) (j : J) :
    (Q.coarseBlock j).map
        (g.1.toLinearEquiv : V →ₗ[R] V) =
      Q.coarseBlock (Q.blockPerm g j) := by
  apply le_antisymm
  · rw [coarseBlock, Submodule.map_iSup]
    refine iSup_le fun i ↦ ?_
    rw [Submodule.map_iSup]
    refine iSup_le fun hij ↦ ?_
    rw [S.map_block]
    exact le_iSup_of_le (S.blockPerm g i)
      (le_iSup_of_le (by simpa [hij] using Q.indexMap_equivariant g i)
        le_rfl)
  · rw [coarseBlock]
    refine iSup_le fun k ↦ iSup_le fun hk ↦ ?_
    let i : I := (S.blockPerm g).symm k
    have hi : Q.indexMap i = j := by
      apply (Q.blockPerm g).injective
      calc
        Q.blockPerm g (Q.indexMap i) =
            Q.indexMap (S.blockPerm g i) :=
          (Q.indexMap_equivariant g i).symm
        _ = Q.indexMap k := by simp [i]
        _ = Q.blockPerm g j := hk
    have hle : S.block i ≤ Q.coarseBlock j := by
      exact le_iSup_of_le i (le_iSup_of_le hi le_rfl)
    have hmap :
        (S.block i).map (g.1.toLinearEquiv : V →ₗ[R] V) ≤
          (Q.coarseBlock j).map (g.1.toLinearEquiv : V →ₗ[R] V) :=
      Submodule.map_mono hle
    rw [S.map_block] at hmap
    simpa [i] using hmap

/-- **Equivariant block coarsening.**  Grouping the fine blocks along the
fibres of an equivariant finite quotient canonically produces another linear
system of imprimitivity. -/
def coarsen
    (Q : EquivariantBlockIndexQuotient (J := J) S) :
    LinearImprimitivitySystem (I := J) K where
  block := Q.coarseBlock
  block_ne_bot := Q.coarseBlock_ne_bot
  internal := Q.coarseBlock_internal
  blockPerm := Q.blockPerm
  map_block := Q.map_coarseBlock

@[simp]
theorem coarsen_block
    (Q : EquivariantBlockIndexQuotient (J := J) S) (j : J) :
    Q.coarsen.block j = Q.coarseBlock j :=
  rfl

@[simp]
theorem coarsen_blockPerm
    (Q : EquivariantBlockIndexQuotient (J := J) S) :
    Q.coarsen.blockPerm = Q.blockPerm :=
  rfl

omit [DecidableEq J] in
/-- The number of coarse blocks cannot exceed the number of fine blocks. -/
theorem fintypeCard_le
    (Q : EquivariantBlockIndexQuotient (J := J) S) :
    Fintype.card J ≤ Fintype.card I :=
  Fintype.card_le_of_surjective Q.indexMap Q.indexMap_surjective

omit [DecidableEq J] in
/-- A genuinely nontrivial coarsening strictly decreases the number of
blocks. -/
theorem fintypeCard_lt_of_not_injective
    (Q : EquivariantBlockIndexQuotient (J := J) S)
    (h : ¬ Function.Injective Q.indexMap) :
    Fintype.card J < Fintype.card I := by
  have hle := Q.fintypeCard_le
  exact lt_of_le_of_ne hle (by
    intro heq
    apply h
    exact Fintype.bijective_iff_surjective_and_card Q.indexMap |>.2
      ⟨Q.indexMap_surjective, heq.symm⟩ |>.injective)

end EquivariantBlockIndexQuotient

end LisiSabatini
