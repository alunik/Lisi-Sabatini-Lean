module

public import LisiSabatini.LinearImprimitivityExtraction
public import LisiSabatini.ImprimitiveStructuralCore
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# From a submodule-orbit witness to a recursive primitive presentation

`LinearImprimitivityExtraction` constructs a finite internal block system
from one nonzero proper submodule orbit, and
`LinearImprimitivityOrbitCoarsening` selects a maximal coarsening with
primitive top.  This file closes the remaining interface gap to
`PrimeFieldPrimitiveInternalImprimitivityPresentation`.

There are three steps.

* A finite linear imprimitivity system can be reindexed along any equivalence;
  its concrete permutation top is conjugated and primitivity is preserved.
* The actual coarse orbit-block type is reindexed canonically by `Fin b`.
* Transitivity transports one coordinate equivalence on one distinguished
  coarse block to all coarse blocks.  Thus one local-coordinate choice is the
  only coordinate input.  Over a finite-dimensional prime field even that
  choice is made canonically from `Module.finBasis`.

Legacy adapters from the extracted presentation to recursive certificate
interfaces live in `LinearImprimitivityPresentationExtraction.lean`.  Keeping
them out of this core module prevents downstream structural consumers from
importing an unrelated proof architecture.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uJ uR uV

variable {I : Type uI} {J : Type uJ} {R : Type uR} {V : Type uV}
variable [Ring R] [AddCommGroup V] [Module R V]
variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

/-! ## Reindexing finite linear imprimitivity systems -/

namespace LinearImprimitivitySystem

/-- Reindex a finite internal block system along an equivalence of its block
types.  The new permutation representation is conjugation by the index
equivalence. -/
def reindex (S : LinearImprimitivitySystem (I := I) K) (e : I ≃ J) :
    LinearImprimitivitySystem (I := J) K where
  block := fun j => S.block (e.symm j)
  block_ne_bot := fun j => S.block_ne_bot (e.symm j)
  internal := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (S.iSupIndep_block.comp e.symm.injective)
    (by
      calc
        (⨆ j, S.block (e.symm j)) = ⨆ i, S.block i :=
          e.symm.iSup_comp
        _ = ⊤ := S.iSup_block_eq_top)
  blockPerm := e.permCongrHom.toMonoidHom.comp S.blockPerm
  map_block := by
    intro g j
    rw [S.map_block]
    simp [Equiv.permCongr_apply]

@[simp]
theorem reindex_block
    (S : LinearImprimitivitySystem (I := I) K) (e : I ≃ J) (j : J) :
    (S.reindex e).block j = S.block (e.symm j) :=
  rfl

@[simp]
theorem reindex_blockPerm_apply
    (S : LinearImprimitivitySystem (I := I) K) (e : I ≃ J)
    (g : K) (j : J) :
    (S.reindex e).blockPerm g j = e (S.blockPerm g (e.symm j)) :=
  rfl

/-- Conjugating the block labels gives an isomorphism between the concrete
old and new permutation tops. -/
def reindexTopEquiv
    (S : LinearImprimitivitySystem (I := I) K) (e : I ≃ J) :
    S.blockPerm.range ≃* (S.reindex e).blockPerm.range where
  toFun σ := ⟨e.permCongr σ.1, by
    rcases σ.2 with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    change e.permCongr (S.blockPerm g) = e.permCongr σ.1
    exact congrArg e.permCongr hg⟩
  invFun τ := ⟨e.symm.permCongr τ.1, by
    rcases τ.2 with ⟨g, hg⟩
    refine ⟨g, ?_⟩
    apply Equiv.Perm.ext
    intro i
    have h := Equiv.Perm.congr_fun hg (e i)
    apply e.injective
    simpa using h⟩
  left_inv σ := by
    apply Subtype.ext
    ext i
    simp
  right_inv τ := by
    apply Subtype.ext
    ext j
    simp
  map_mul' σ τ := by
    apply Subtype.ext
    exact e.permCongrHom.map_mul σ.1 τ.1

/-- Primitivity of the concrete permutation top is invariant under block
reindexing. -/
theorem reindex_top_preprimitive
    (S : LinearImprimitivitySystem (I := I) K) (e : I ≃ J)
    (hprim : MulAction.IsPreprimitive S.blockPerm.range I) :
    MulAction.IsPreprimitive (S.reindex e).blockPerm.range J := by
  let φ := S.reindexTopEquiv e
  let f : I →ₑ[φ] J := {
    toFun := e
    map_smul' := by
      intro σ i
      change e (σ.1 i) = e.permCongr σ.1 (e i)
      simp [Equiv.permCongr_apply]
  }
  exact (MulAction.isPreprimitive_congr
    (f := f) φ.surjective e.bijective).mp hprim

end LinearImprimitivitySystem

/-! ## Packaging a maximal primitive coarsening -/

/-- A selected maximal proper permutation block in the fine system extracted
from one submodule orbit.  All coarse-system and presentation data below are
derived from these two fields. -/
structure ExtractedPrimitiveCoarsening
    (W : LinearImprimitivityExtractionWitness K) where
  selectedBlock : MulAction.BlockMem
    W.toLinearImprimitivitySystem.fineTop W.baseIndex
  selectedBlock_isCoatom : IsCoatom selectedBlock

namespace ExtractedPrimitiveCoarsening

variable {W : LinearImprimitivityExtractionWitness K}

/-- Maximal-block selection supplies an extracted primitive coarsening. -/
theorem nonempty (W : LinearImprimitivityExtractionWitness K) :
    Nonempty (ExtractedPrimitiveCoarsening W) := by
  obtain ⟨C, hC, _⟩ := W.exists_maximalPrimitiveCoarsening
  exact ⟨⟨C, hC⟩⟩

/-- A canonical classical choice of maximal coarse block. -/
def canonical (W : LinearImprimitivityExtractionWitness K) :
    ExtractedPrimitiveCoarsening W :=
  Classical.choice (nonempty W)

abbrev fineSystem (W : LinearImprimitivityExtractionWitness K) :=
  W.toLinearImprimitivitySystem

/-- The actual orbit of the selected maximal permutation block. -/
abbrev CoarseIndex (P : ExtractedPrimitiveCoarsening W) :=
  (fineSystem W).OrbitBlockIndex P.selectedBlock.1

/-- The internal linear system obtained by grouping fine summands along the
selected maximal permutation-block orbit. -/
def coarseSystem (P : ExtractedPrimitiveCoarsening W) :
    LinearImprimitivitySystem (I := P.CoarseIndex) K :=
  (fineSystem W).coarsenAlongOrbitBlockOfIrreducible
    P.selectedBlock.1 W.irreducible P.selectedBlock.2.2
    ⟨W.baseIndex, P.selectedBlock.2.1⟩

/-- The selected block itself, as the distinguished coarse index. -/
def distinguishedCoarseIndex (P : ExtractedPrimitiveCoarsening W) :
    P.CoarseIndex :=
  (fineSystem W).baseOrbitBlock P.selectedBlock.1

theorem selectedBlock_ne_univ (P : ExtractedPrimitiveCoarsening W) :
    P.selectedBlock.1 ≠ Set.univ := by
  intro h
  apply P.selectedBlock_isCoatom.ne_top
  apply Subtype.ext
  exact h

/-- A proper selected block has at least two distinct translates. -/
theorem coarseIndex_nontrivial (P : ExtractedPrimitiveCoarsening W) :
    Nontrivial P.CoarseIndex := by
  exact (fineSystem W).orbitBlockIndex_nontrivial_of_ne_univ
    P.selectedBlock.1 W.extractedTop_isPretransitive
    P.selectedBlock.2.2 ⟨W.baseIndex, P.selectedBlock.2.1⟩
    P.selectedBlock_ne_univ

/-- The number of actual coarse blocks. -/
def blockCount (P : ExtractedPrimitiveCoarsening W) : ℕ :=
  Fintype.card P.CoarseIndex

/-- Canonical finite reindexing of the actual coarse block type. -/
def indexEquiv (P : ExtractedPrimitiveCoarsening W) :
    P.CoarseIndex ≃ Fin P.blockCount :=
  Fintype.equivFin P.CoarseIndex

/-- The primitive coarse internal system with the `Fin b` labels required by
the structural bridge. -/
def finSystem (P : ExtractedPrimitiveCoarsening W) :
    LinearImprimitivitySystem (I := Fin P.blockCount) K :=
  P.coarseSystem.reindex P.indexEquiv

/-- The `Fin b` label of the selected maximal block. -/
def distinguishedFinIndex (P : ExtractedPrimitiveCoarsening W) :
    Fin P.blockCount :=
  P.indexEquiv P.distinguishedCoarseIndex

theorem blockCount_one_lt (P : ExtractedPrimitiveCoarsening W) :
    1 < P.blockCount := by
  letI : Nontrivial P.CoarseIndex := P.coarseIndex_nontrivial
  exact Fintype.one_lt_card_iff_nontrivial.2 inferInstance

/-- Maximality makes the actual coarse permutation top primitive. -/
theorem coarse_top_preprimitive (P : ExtractedPrimitiveCoarsening W) :
    MulAction.IsPreprimitive P.coarseSystem.blockPerm.range P.CoarseIndex := by
  unfold coarseSystem LinearImprimitivitySystem.coarsenAlongOrbitBlockOfIrreducible
  exact (fineSystem W)
    |>.coarsenAlongOrbitBlock_blockPerm_range_isPreprimitive_of_isCoatom
      P.selectedBlock.1 W.extractedTop_isPretransitive
      P.selectedBlock.2.2 ⟨W.baseIndex, P.selectedBlock.2.1⟩
      P.selectedBlock.2.1 P.selectedBlock_isCoatom

/-- The canonically `Fin`-reindexed coarse permutation top is primitive. -/
theorem fin_top_preprimitive (P : ExtractedPrimitiveCoarsening W) :
    MulAction.IsPreprimitive P.finSystem.blockPerm.range (Fin P.blockCount) := by
  exact P.coarseSystem.reindex_top_preprimitive P.indexEquiv
    P.coarse_top_preprimitive

end ExtractedPrimitiveCoarsening

/-! ## Common local coordinates and the internal primitive presentation -/

namespace ExtractedPrimitiveCoarsening

variable {r : ℕ}
variable {V : Type uV} [AddCommGroup V] [Module (ZMod r) V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
variable {W : LinearImprimitivityExtractionWitness K}

/-- A coherently chosen group element carrying the distinguished block to
the block labelled by `i`.  Existence follows from irreducibility and the
internal system, not from an extra transitivity field. -/
def transporter (P : ExtractedPrimitiveCoarsening W)
    (i : Fin P.blockCount) : K :=
  Classical.choose
    (P.finSystem.isIndexPretransitive_of_irreducible W.irreducible
      P.distinguishedFinIndex i)

@[simp]
theorem transporter_maps (P : ExtractedPrimitiveCoarsening W)
    (i : Fin P.blockCount) :
    P.finSystem.blockPerm (P.transporter i) P.distinguishedFinIndex = i :=
  Classical.choose_spec
    (P.finSystem.isIndexPretransitive_of_irreducible W.irreducible
      P.distinguishedFinIndex i)

/-- The selected transporter restricts to a linear equivalence from the
distinguished coarse block to any other coarse block. -/
def distinguishedBlockEquiv (P : ExtractedPrimitiveCoarsening W)
    (i : Fin P.blockCount) :
    P.finSystem.block P.distinguishedFinIndex ≃ₗ[ZMod r]
      P.finSystem.block i :=
  (P.transporter i).1.toLinearEquiv.ofSubmodules
    (P.finSystem.block P.distinguishedFinIndex) (P.finSystem.block i)
    ((P.finSystem.map_block (P.transporter i) P.distinguishedFinIndex).trans
      (congrArg P.finSystem.block (P.transporter_maps i)))

/-- One coordinate choice on the distinguished block transports to a common
local model on every coarse block. -/
def localCoordinates (P : ExtractedPrimitiveCoarsening W) {e : ℕ}
    (c₀ : P.finSystem.block P.distinguishedFinIndex ≃ₗ[ZMod r]
      (Fin e → ZMod r)) (i : Fin P.blockCount) :
    P.finSystem.block i ≃ₗ[ZMod r] (Fin e → ZMod r) :=
  (P.distinguishedBlockEquiv i).symm.trans c₀

/-- A nonzero block cannot be linearly equivalent to the zero-dimensional
coordinate space. -/
theorem localDimension_pos (P : ExtractedPrimitiveCoarsening W) {e : ℕ}
    (c₀ : P.finSystem.block P.distinguishedFinIndex ≃ₗ[ZMod r]
      (Fin e → ZMod r)) :
    0 < e := by
  by_contra he
  have he0 : e = 0 := Nat.eq_zero_of_not_pos he
  subst e
  apply P.finSystem.block_ne_bot P.distinguishedFinIndex
  apply le_antisymm
  · intro x hx
    let y : P.finSystem.block P.distinguishedFinIndex := ⟨x, hx⟩
    have hcy : c₀ y = 0 := by
      ext i
      exact Fin.elim0 i
    have hy : y = 0 := c₀.injective (by simpa using hcy)
    simpa [y] using congrArg Subtype.val hy
  · exact bot_le

/-- **Adapter to the existing structural bridge.**  A prime and one local
coordinate equivalence turn the extracted maximal coarse system into the
exact internal primitive presentation consumed by
`ImprimitiveStructuralBridge`. -/
def toInternalPresentation (P : ExtractedPrimitiveCoarsening W)
    (hr : Nat.Prime r) {e : ℕ}
    (c₀ : P.finSystem.block P.distinguishedFinIndex ≃ₗ[ZMod r]
      (Fin e → ZMod r)) :
    PrimeFieldPrimitiveInternalImprimitivityPresentation
      r P.blockCount e V K where
  field_prime := hr
  irreducible := W.irreducible
  blockCount_one_lt := P.blockCount_one_lt
  localDimension_pos := P.localDimension_pos c₀
  system := P.finSystem
  localCoordinates := P.localCoordinates c₀
  top_preprimitive := P.fin_top_preprimitive

/-! ### Automatic finite-dimensional normalization -/

section FiniteDimensional

variable [Fact (Nat.Prime r)]
variable [FiniteDimensional (ZMod r) V]

/-- In finite dimension over the prime field, a basis of the distinguished
block supplies the sole local coordinate choice automatically. -/
def finiteDimensionalInternalPresentation
    (W : LinearImprimitivityExtractionWitness K) :
    PrimeFieldPrimitiveInternalImprimitivityPresentation
      r (canonical W).blockCount
        (Module.finrank (ZMod r)
          ((canonical W).finSystem.block
            (canonical W).distinguishedFinIndex)) V K :=
  (canonical W).toInternalPresentation (Fact.out : Nat.Prime r)
    (Module.finBasis (ZMod r)
      ((canonical W).finSystem.block
        (canonical W).distinguishedFinIndex)).equivFun

/-- A sigma-packaged version when the concrete values of `b` and `e` should
remain abstract to the caller. -/
def internalPresentationSigmaOfFiniteDimensional
    (W : LinearImprimitivityExtractionWitness K) :
    Σ b e : ℕ,
      PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K :=
  ⟨(canonical W).blockCount,
    Module.finrank (ZMod r)
      ((canonical W).finSystem.block (canonical W).distinguishedFinIndex),
    finiteDimensionalInternalPresentation W⟩

end FiniteDimensional

end ExtractedPrimitiveCoarsening

end LisiSabatini
