module

public import LisiSabatini.LinearImprimitivityOrbitCoarsening
public import Mathlib.Algebra.Module.Submodule.Pointwise

/-!
# Extracting a linear imprimitivity system from one submodule orbit

For a concrete irreducible linear group, the usual witness of imprimitivity
is one nonzero proper submodule whose distinct translates form a direct
family.  This file turns precisely that witness into the labelled finite
`LinearImprimitivitySystem` used by the recursive synchronization machinery.

The block index type is not supplied independently.  It is the actual orbit
of the chosen submodule.  The permutation representation is induced by
left translation on that orbit, and `map_block` is consequently a theorem of
the construction rather than additional input.

Finiteness is assumed only for the orbit, not for the ambient linear group.
Irreducibility forces the direct orbit family to span the whole module.  The
last theorem then feeds the extracted system into the maximal orbit-block
construction of `LinearImprimitivityOrbitCoarsening`: a maximal coarse block
system exists and its concrete permutation top is primitive.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe uR uV

variable {R : Type uR} {V : Type uV}
variable [Ring R] [AddCommGroup V] [Module R V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

/-! ## The actual orbit of a submodule -/

/-- The image of a submodule under an element of the concrete linear group.

This compatibility spelling is the pointwise action on submodules supplied
by mathlib. -/
abbrev linearSubmoduleImage (g : K) (U : Submodule R V) : Submodule R V :=
  g • U

@[simp]
theorem linearSubmoduleImage_one (U : Submodule R V) :
    linearSubmoduleImage (K := K) 1 U = U :=
  one_smul K U

/-- Linear images compose in the same order as multiplication in the
general linear group. -/
@[simp]
theorem linearSubmoduleImage_mul (g h : K) (U : Submodule R V) :
    linearSubmoduleImage (g * h) U =
      linearSubmoduleImage g (linearSubmoduleImage h U) :=
  mul_smul g h U

/-- The genuine orbit of `U` under `K`, with equal translates identified. -/
abbrev SubmoduleOrbitIndex
    (K : Subgroup (LinearMap.GeneralLinearGroup R V))
    (U : Submodule R V) :=
  MulAction.orbit K U

/-- Left translation by `g` on the actual submodule orbit. -/
abbrev mapSubmoduleOrbitIndex (U : Submodule R V) (g : K) :
    SubmoduleOrbitIndex K U → SubmoduleOrbitIndex K U :=
  fun W ↦ g • W

@[simp]
theorem mapSubmoduleOrbitIndex_coe (U : Submodule R V) (g : K)
    (W : SubmoduleOrbitIndex K U) :
    (mapSubmoduleOrbitIndex U g W).1 = linearSubmoduleImage g W.1 :=
  rfl

/-- Left translation is an equivalence of the submodule orbit. -/
abbrev submoduleOrbitEquiv (U : Submodule R V) (g : K) :
    SubmoduleOrbitIndex K U ≃ SubmoduleOrbitIndex K U :=
  MulAction.toPermHom K (SubmoduleOrbitIndex K U) g

@[simp]
theorem submoduleOrbitEquiv_coe (U : Submodule R V) (g : K)
    (W : SubmoduleOrbitIndex K U) :
    (submoduleOrbitEquiv U g W).1 = linearSubmoduleImage g W.1 :=
  rfl

/-- The permutation representation induced on the actual submodule orbit. -/
abbrev submoduleOrbitPerm (U : Submodule R V) :
    K →* Equiv.Perm (SubmoduleOrbitIndex K U) :=
  MulAction.toPermHom K (SubmoduleOrbitIndex K U)

@[simp]
theorem submoduleOrbitPerm_apply_coe (U : Submodule R V) (g : K)
    (W : SubmoduleOrbitIndex K U) :
    (submoduleOrbitPerm U g W).1 = linearSubmoduleImage g W.1 :=
  rfl

/-! ## The minimal extraction witness -/

/-- A natural one-submodule witness for linear imprimitivity of a concrete
irreducible action.

`orbit_iSupIndep` is the directness condition on the *actual* orbit, so equal
translates have already been identified.  No spanning field is included:
the span is a nonzero invariant submodule and hence is all of `V` by
`irreducible`.  `orbit_finite` is automatic when `K` is finite, but retaining
only orbit finiteness makes the construction slightly more general. -/
structure LinearImprimitivityExtractionWitness
    (K : Subgroup (LinearMap.GeneralLinearGroup R V)) where
  /-- The concrete action is irreducible. -/
  irreducible : LinearImprimitivitySystem.IsIrreducible K
  /-- One proposed block submodule. -/
  base : Submodule R V
  /-- The proposed block is nonzero. -/
  base_ne_bot : base ≠ ⊥
  /-- The proposed block is proper. -/
  base_ne_top : base ≠ ⊤
  /-- Only finitely many distinct translates occur. -/
  orbit_finite :
    (MulAction.orbit K base).Finite
  /-- The distinct translates are an independent family of submodules. -/
  orbit_iSupIndep :
    iSupIndep (fun W : SubmoduleOrbitIndex K base => W.1)

namespace LinearImprimitivityExtractionWitness

/-- For a finite concrete group, finiteness of the submodule orbit is
automatic. -/
def ofFiniteGroup [Finite K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (U : Submodule R V) (hUne : U ≠ ⊥) (hUproper : U ≠ ⊤)
    (hind : iSupIndep (fun W : SubmoduleOrbitIndex K U => W.1)) :
    LinearImprimitivityExtractionWitness K where
  irreducible := hirr
  base := U
  base_ne_bot := hUne
  base_ne_top := hUproper
  orbit_finite := Set.finite_range _
  orbit_iSupIndep := hind

/-- The explicit finite type structure on the actual submodule orbit. -/
noncomputable instance orbitIndexFintype
    (W : LinearImprimitivityExtractionWitness K) :
    Fintype (SubmoduleOrbitIndex K W.base) :=
  W.orbit_finite.fintype

noncomputable instance orbitIndexDecidableEq
    (W : LinearImprimitivityExtractionWitness K) :
    DecidableEq (SubmoduleOrbitIndex K W.base) :=
  Classical.decEq _

/-- The original submodule as the distinguished point of its orbit. -/
def baseIndex (W : LinearImprimitivityExtractionWitness K) :
    SubmoduleOrbitIndex K W.base :=
  ⟨W.base, MulAction.mem_orbit_self W.base⟩

@[simp]
theorem baseIndex_coe (W : LinearImprimitivityExtractionWitness K) :
    W.baseIndex.1 = W.base :=
  rfl

/-- The span of all distinct translates of the base submodule. -/
def orbitSpan (W : LinearImprimitivityExtractionWitness K) :
    Submodule R V :=
  ⨆ C : SubmoduleOrbitIndex K W.base, C.1

/-- The base submodule lies in the orbit span. -/
theorem base_le_orbitSpan (W : LinearImprimitivityExtractionWitness K) :
    W.base ≤ W.orbitSpan := by
  exact le_iSup_of_le W.baseIndex le_rfl

/-- The span of the submodule orbit is invariant under the concrete action. -/
theorem orbitSpan_invariant (W : LinearImprimitivityExtractionWitness K) :
    ∀ g : K, ∀ v ∈ W.orbitSpan,
      (g.1 : LinearMap.GeneralLinearGroup R V) • v ∈ W.orbitSpan := by
  intro g v hv
  have hmap : W.orbitSpan.map
      (g.1.toLinearEquiv : V →ₗ[R] V) ≤ W.orbitSpan := by
    rw [orbitSpan, Submodule.map_iSup]
    refine iSup_le fun C => ?_
    exact le_iSup_of_le (mapSubmoduleOrbitIndex W.base g C) le_rfl
  exact hmap (Submodule.mem_map_of_mem hv)

/-- The orbit span is nonzero because it contains the nonzero base block. -/
theorem orbitSpan_ne_bot (W : LinearImprimitivityExtractionWitness K) :
    W.orbitSpan ≠ ⊥ := by
  intro hbot
  apply W.base_ne_bot
  apply le_antisymm
  · simpa [hbot] using W.base_le_orbitSpan
  · exact bot_le

/-- Irreducibility supplies the spanning half of the direct-sum
decomposition. -/
theorem orbit_iSup_eq_top (W : LinearImprimitivityExtractionWitness K) :
    ⨆ C : SubmoduleOrbitIndex K W.base, C.1 = ⊤ := by
  change W.orbitSpan = ⊤
  rcases W.irreducible W.orbitSpan W.orbitSpan_invariant with hbot | htop
  · exact (W.orbitSpan_ne_bot hbot).elim
  · exact htop

/-- The independent orbit family is therefore an internal direct sum equal
to the whole module. -/
theorem orbit_internal (W : LinearImprimitivityExtractionWitness K) :
    DirectSum.IsInternal
      (fun C : SubmoduleOrbitIndex K W.base => C.1) :=
  DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    W.orbit_iSupIndep W.orbit_iSup_eq_top

/-- A nonzero proper block in an irreducible action has at least one distinct
translate; equivalently, the actual orbit index type is nontrivial. -/
theorem orbitIndex_nontrivial (W : LinearImprimitivityExtractionWitness K) :
    Nontrivial (SubmoduleOrbitIndex K W.base) := by
  rw [nontrivial_iff]
  by_contra h
  push Not at h
  have hle :
      (⨆ C : SubmoduleOrbitIndex K W.base, C.1) ≤ W.base := by
    refine iSup_le fun C => ?_
    rw [h C W.baseIndex]
    exact le_rfl
  have htop : (⊤ : Submodule R V) ≤ W.base := by
    rw [← W.orbit_iSup_eq_top]
    exact hle
  exact W.base_ne_top (top_unique htop)

/-- The actual orbit has more than one block. -/
theorem blockCount_one_lt (W : LinearImprimitivityExtractionWitness K) :
    1 < Fintype.card (SubmoduleOrbitIndex K W.base) := by
  exact Fintype.one_lt_card_iff_nontrivial.2 W.orbitIndex_nontrivial

/-! ## Extraction and primitive maximal coarsening -/

/-- **Orbit extraction.**  The actual finite orbit of the witness submodule,
with its induced permutation representation, is a linear system of
imprimitivity.  In particular, neither block labels nor `map_block` are
additional hypotheses. -/
def toLinearImprimitivitySystem
    (W : LinearImprimitivityExtractionWitness K) :
    LinearImprimitivitySystem
      (I := SubmoduleOrbitIndex K W.base) K where
  block := fun C => C.1
  block_ne_bot := by
    intro C
    rcases C.2 with ⟨g, hg⟩
    rw [← hg]
    change W.base.map
      (DistribMulAction.toLinearEquiv R V g : V →ₗ[R] V) ≠ ⊥
    exact Submodule.map_ne_bot_iff.mpr W.base_ne_bot
  internal := W.orbit_internal
  blockPerm := submoduleOrbitPerm W.base
  map_block := by
    intro g C
    rfl

@[simp]
theorem toLinearImprimitivitySystem_block
    (W : LinearImprimitivityExtractionWitness K)
    (C : SubmoduleOrbitIndex K W.base) :
    W.toLinearImprimitivitySystem.block C = C.1 :=
  rfl

@[simp]
theorem toLinearImprimitivitySystem_base_block
    (W : LinearImprimitivityExtractionWitness K) :
    W.toLinearImprimitivitySystem.block W.baseIndex = W.base :=
  rfl

@[simp]
theorem toLinearImprimitivitySystem_blockPerm
    (W : LinearImprimitivityExtractionWitness K) :
    W.toLinearImprimitivitySystem.blockPerm =
      submoduleOrbitPerm W.base :=
  rfl

/-- The extracted concrete permutation top is transitive. -/
theorem extractedTop_isPretransitive
    (W : LinearImprimitivityExtractionWitness K) :
    MulAction.IsPretransitive
      W.toLinearImprimitivitySystem.blockPerm.range
      (SubmoduleOrbitIndex K W.base) :=
  W.toLinearImprimitivitySystem
    |>.blockPerm_range_isPretransitive_of_irreducible W.irreducible

/-- **Primitive endpoint of orbit extraction.**  Starting only from the
one-submodule orbit witness, there is a maximal proper block of the extracted
fine permutation action whose canonical orbit-block coarsening has primitive
concrete top.

This is the direct interface to the recursive imprimitive NCAS machinery:
the fine internal decomposition is constructed above, while maximal-block
selection and primitivity are supplied by
`LinearImprimitivityOrbitCoarsening`. -/
theorem exists_maximalPrimitiveCoarsening
    (W : LinearImprimitivityExtractionWitness K) :
    ∃ C : MulAction.BlockMem
        W.toLinearImprimitivitySystem.fineTop W.baseIndex,
      IsCoatom C ∧
        MulAction.IsPreprimitive
          (W.toLinearImprimitivitySystem
            |>.coarsenAlongOrbitBlockOfIrreducible C.1 W.irreducible
              C.2.2 ⟨W.baseIndex, C.2.1⟩).blockPerm.range
          (W.toLinearImprimitivitySystem.OrbitBlockIndex C.1) := by
  letI : Nontrivial (SubmoduleOrbitIndex K W.base) :=
    W.orbitIndex_nontrivial
  exact W.toLinearImprimitivitySystem
    |>.exists_primitiveCoarsening_of_irreducible W.baseIndex W.irreducible

end LinearImprimitivityExtractionWitness

end LisiSabatini
