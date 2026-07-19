import Mathlib.Algebra.DirectSum.Module
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Linear systems of imprimitivity

This file bundles the elementary linear-algebraic data of a system of
imprimitivity.  The ambient linear group permutes a finite family of nonzero
submodules whose sum is internal.  Unlike `MulAction.IsBlock`, this definition
uses submodules rather than disjoint subsets: distinct linear blocks always
meet at zero.

The principal structural result below is that an irreducible action is
transitive on the blocks of any such system.  No field or finite-dimensional
hypothesis is needed for that argument.
-/

noncomputable section

namespace LisiSabatini

universe uI uR uV

variable {I : Type uI} {R : Type uR} {V : Type uV}
variable [Semiring R] [AddCommMonoid V] [Module R V]

/-- A finite linear system of imprimitivity for a concrete linear group.

`blockPerm g` sends the source block indexed by `i` to the target block
indexed by `blockPerm g i`.  The equality `map_block` records this convention
directly at the level of submodules.
-/
structure LinearImprimitivitySystem
    [Fintype I] [DecidableEq I]
    (K : Subgroup (LinearMap.GeneralLinearGroup R V)) where
  /-- The submodule belonging to each block index. -/
  block : I → Submodule R V
  /-- Degenerate zero summands are excluded. -/
  block_ne_bot : ∀ i, block i ≠ ⊥
  /-- The blocks form an internal direct sum equal to the whole module. -/
  internal : DirectSum.IsInternal block
  /-- The permutation induced by each element of the linear group. -/
  blockPerm : K →* Equiv.Perm I
  /-- Each group element maps a source block onto its prescribed target. -/
  map_block : ∀ (g : K) (i : I),
    (block i).map
        (g.1.toLinearEquiv : V →ₗ[R] V) =
      block (blockPerm g i)

namespace LinearImprimitivitySystem

variable [Fintype I] [DecidableEq I]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

/-- A field-independent irreducibility predicate for a concrete linear
action on an arbitrary module. -/
def IsIrreducible
    (K : Subgroup (LinearMap.GeneralLinearGroup R V)) : Prop :=
  ∀ U : Submodule R V,
    (∀ g : K, ∀ v ∈ U,
      (g.1 : LinearMap.GeneralLinearGroup R V) • v ∈ U) →
    U = ⊥ ∨ U = ⊤

/-- The internal direct sum spans the ambient module. -/
theorem iSup_block_eq_top
    (S : LinearImprimitivitySystem (I := I) K) :
    ⨆ i, S.block i = ⊤ :=
  S.internal.submodule_iSup_eq_top

/-- The summand family of a linear imprimitivity system is independent. -/
theorem iSupIndep_block
    (S : LinearImprimitivitySystem (I := I) K) :
    iSupIndep S.block :=
  S.internal.submodule_iSupIndep

/-- Coordinates in the external direct sum supplied canonically by an
internal system of imprimitivity. -/
def linearEquivDirectSum
    (S : LinearImprimitivitySystem (I := I) K) :
    V ≃ₗ[R] DirectSum I (fun i => S.block i) :=
  (LinearEquiv.ofBijective (DirectSum.coeLinearMap S.block) S.internal).symm

/-- The action on block indices obtained by pulling back the natural action
of `Equiv.Perm I` along `blockPerm`. -/
abbrev indexAction
    (S : LinearImprimitivitySystem (I := I) K) : MulAction K I :=
  MulAction.compHom I S.blockPerm

/-- Explicit, instance-free formulation of transitivity of the induced
action on block indices. -/
def IsIndexPretransitive
    (S : LinearImprimitivitySystem (I := I) K) : Prop :=
  ∀ i j : I, ∃ g : K, S.blockPerm g i = j

/-- Irreducibility forces transitivity on the nonzero summands of a linear
system of imprimitivity. -/
theorem isIndexPretransitive_of_irreducible
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) :
    S.IsIndexPretransitive := by
  intro i j
  let orbit : Set I := Set.range (fun g : K => S.blockPerm g i)
  let U : Submodule R V := ⨆ k ∈ orbit, S.block k
  have hU_invariant : ∀ h : K, ∀ v ∈ U,
      (h.1 : LinearMap.GeneralLinearGroup R V) • v ∈ U := by
    intro h v hv
    have hmap : U.map
        (h.1.toLinearEquiv : V →ₗ[R] V) ≤ U := by
      dsimp only [U]
      rw [Submodule.map_iSup]
      refine iSup_le fun k => ?_
      rw [Submodule.map_iSup]
      refine iSup_le fun hk => ?_
      rw [S.map_block]
      rcases hk with ⟨g, rfl⟩
      refine le_biSup S.block ?_
      exact ⟨h * g, by simp⟩
    apply hmap
    exact Submodule.mem_map_of_mem hv
  have hU_ne_bot : U ≠ ⊥ := by
    intro hU
    apply S.block_ne_bot i
    apply le_antisymm
    · have hle : S.block i ≤ U := by
        refine le_biSup S.block ?_
        exact ⟨1, by simp⟩
      simpa [hU] using hle
    · exact bot_le
  have hU_top : U = ⊤ := by
    rcases hirr U hU_invariant with hbot | htop
    · exact (hU_ne_bot hbot).elim
    · exact htop
  have hj : j ∈ orbit :=
    S.iSupIndep_block.mem_of_biSup_eq_top hU_top (S.block_ne_bot j)
  exact hj

/-- Class-valued form of `isIndexPretransitive_of_irreducible`, for use by
the permutation-group block and primitivity APIs. -/
theorem indexAction_isPretransitive_of_irreducible
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) :
    @MulAction.IsPretransitive K I S.indexAction.toSMul := by
  exact @MulAction.IsPretransitive.mk K I S.indexAction.toSMul
    (fun i j => S.isIndexPretransitive_of_irreducible hirr i j)

/-- The concrete permutation image is pretransitive on the block set.  This
is the form consumed by the block and primitive-action APIs. -/
theorem blockPerm_range_isPretransitive_of_irreducible
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) :
    MulAction.IsPretransitive S.blockPerm.range I := by
  refine ⟨fun i j => ?_⟩
  obtain ⟨g, hg⟩ := S.isIndexPretransitive_of_irreducible hirr i j
  exact ⟨⟨S.blockPerm g, ⟨g, rfl⟩⟩, hg⟩

end LinearImprimitivitySystem

end LisiSabatini
