module

public import LisiSabatini.ImprimitiveReductionCore
public import LisiSabatini.NCASLinearEquiv
public import LisiSabatini.LinearImprimitivitySystem
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Structural bridge to imprimitive action data

Mathlib currently has a developed theory of blocks for permutation actions
and a developed theory of internal direct sums of submodules, but no bundled
linear system of imprimitivity and no theorem extracting a minimal block
decomposition from an irreducible linear representation.

This file formalizes the constructive part of that missing bridge.  A
coordinate block system records how the group acts only on vectors supported
in one block.  Linearity and the finite sum of coordinate injections then
derive the full monomial action formula required by
`ImprimitiveLinearActionData`; that formula is not assumed.

For an arbitrary prime-field module `V`, a primitive imprimitivity
presentation consists of a linear change of coordinates together with such a
block system for the conjugated action.  It packages the honest witness whose
existence must eventually be extracted from representation-theoretic
imprimitivity.  The final theorem transports recursive imprimitive NCAS back
to the original action.

There is deliberately no claim that one block system simultaneously has a
primitive top and a primitive local action.  A coarsest nontrivial system has
primitive top, while its local action may remain imprimitive and is precisely
the object handled recursively.  `LinearImprimitivityCoarsening.lean` and
`LinearImprimitivityOrbitCoarsening.lean` now construct that coarsening and
prove that a maximal proper permutation block gives a primitive coarse top.
Primitivity is retained below as explicit presentation data so this bridge can
be used independently of the particular maximal-block construction.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uJ uR uV uW

variable {I : Type uI} {R : Type uR} {V : Type uV} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-! ## A coordinate system of linear imprimitivity -/

/-- Data saying that a linear group permutes the coordinate blocks.

Only the action on a vector supported in one block is specified.  The local
factor is indexed by the target block, matching the convention of
`ImprimitiveLinearActionData`. -/
structure CoordinateLinearBlockSystem
    [Fintype I] [DecidableEq I]
    (K : Subgroup
      (LinearMap.GeneralLinearGroup R (I → W))) where
  blockPerm : K →* Equiv.Perm I
  blockLinear : K → I → LinearMap.GeneralLinearGroup R W
  action_single : ∀ (g : K) (j : I) (w : W),
    g.1 • (Pi.single j w : I → W) =
      (Pi.single (blockPerm g j)
        ((blockLinear g (blockPerm g j)).1 • w) : I → W)

namespace CoordinateLinearBlockSystem

variable [Fintype I] [DecidableEq I]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup R (I → W))}

/-- The single-block action determines the full imprimitive action formula.
Thus a coordinate linear block system canonically produces
`ImprimitiveLinearActionData`, with no additional cocycle or arbitrary-vector
compatibility axiom. -/
def imprimitiveLinearActionData
    (S : CoordinateLinearBlockSystem K) :
    ImprimitiveLinearActionData K
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W)) where
  blockPerm := S.blockPerm
  blockLinear g i := ⟨S.blockLinear g i, trivial⟩
  action_apply g x i := by
    classical
    calc
      (g.1 • x) i =
          (g.1 • (∑ j, (Pi.single j (x j) : I → W))) i := by
        rw [LinearMap.sum_single_apply (fun _ : I ↦ W) x]
      _ = (∑ j,
          (g.1 : LinearMap.GeneralLinearGroup R (I → W)).toLinearEquiv
            (Pi.single j (x j) : I → W)) i := by
        change
          ((g.1 : LinearMap.GeneralLinearGroup R (I → W)).toLinearEquiv
            (∑ j, (Pi.single j (x j) : I → W))) i = _
        rw [map_sum]
      _ = (∑ j, (Pi.single (S.blockPerm g j)
          ((S.blockLinear g (S.blockPerm g j)).1 • x j) : I → W)) i := by
        apply congrArg (fun y : I → W ↦ y i)
        apply Finset.sum_congr rfl
        intro j _
        exact S.action_single g j (x j)
      _ = (Pi.single
          (S.blockPerm g ((S.blockPerm g).symm i))
          ((S.blockLinear g
            (S.blockPerm g ((S.blockPerm g).symm i))).1 •
              x ((S.blockPerm g).symm i)) : I → W) i := by
        rw [Finset.sum_apply]
        apply Finset.sum_eq_single
          (s := Finset.univ) ((S.blockPerm g).symm i)
        · intro j _ hj
          have htarget : S.blockPerm g j ≠ i := by
            intro heq
            apply hj
            apply (S.blockPerm g).injective
            simpa using heq
          exact Pi.single_eq_of_ne htarget.symm _
        · intro hnot
          exact (hnot (Finset.mem_univ _)).elim
      _ = (S.blockLinear g i).1 • x ((S.blockPerm g).symm i) := by
        rw [Equiv.apply_symm_apply, Pi.single_eq_same]

@[simp]
theorem imprimitiveLinearActionData_blockPerm
    (S : CoordinateLinearBlockSystem K) :
    S.imprimitiveLinearActionData.blockPerm = S.blockPerm :=
  rfl

@[simp]
theorem imprimitiveLinearActionData_blockLinear_coe
    (S : CoordinateLinearBlockSystem K) (g : K) (i : I) :
    ((S.imprimitiveLinearActionData.blockLinear g i :
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W))) :
        LinearMap.GeneralLinearGroup R W) = S.blockLinear g i :=
  rfl

end CoordinateLinearBlockSystem

/-! ## From internal submodules to block coordinates -/

namespace LinearImprimitivitySystem

variable [AddCommGroup V] [Module R V]
variable [Fintype I] [DecidableEq I]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

/-- Canonical coordinates in the product of the actual block submodules. -/
def blockProductCoordinates
    (S : LinearImprimitivitySystem (I := I) K) :
    V ≃ₗ[R] (∀ i, S.block i) :=
  S.linearEquivDirectSum.trans
    (DirectSum.linearEquivFunOnFintype R I (fun i ↦ S.block i))

/-- Choosing one common model `W` for all block submodules turns the
canonical block decomposition into ordinary product coordinates. -/
def productCoordinates
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) : V ≃ₗ[R] (I → W) :=
  S.blockProductCoordinates.trans (LinearEquiv.piCongrRight c)

/-- A vector lying in one internal summand has exactly one nonzero block
coordinate. -/
theorem blockProductCoordinates_coe_block
    (S : LinearImprimitivitySystem (I := I) K)
    (i : I) (x : S.block i) :
    S.blockProductCoordinates (x : V) = Pi.single i x := by
  classical
  ext j
  by_cases hji : j = i
  · subst j
    simp [blockProductCoordinates, linearEquivDirectSum,
      S.internal.ofBijective_coeLinearMap_of_mem x.property]
  · rw [Pi.single_eq_of_ne hji]
    simpa [blockProductCoordinates, linearEquivDirectSum] using
      S.internal.ofBijective_coeLinearMap_of_mem_ne (Ne.symm hji) x.property

/-- The corresponding one-block formula after identifying each block with
the common model `W`. -/
theorem productCoordinates_coe_block
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (i : I) (x : S.block i) :
    S.productCoordinates c (x : V) = Pi.single i (c i x) := by
  classical
  rw [productCoordinates, LinearEquiv.trans_apply,
    S.blockProductCoordinates_coe_block]
  ext j
  by_cases hji : j = i
  · subst j
    simp [LinearEquiv.piCongrRight_apply]
  · rw [LinearEquiv.piCongrRight_apply, Pi.single_eq_of_ne hji,
      Pi.single_eq_of_ne hji]
    simp

/-- The local linear factor attached to a source block. -/
def sourceLocalEquiv
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (g : K) (j : I) : W ≃ₗ[R] W :=
  (c j).symm |>.trans
    (g.1.toLinearEquiv.ofSubmodules
      (S.block j) (S.block (S.blockPerm g j)) (S.map_block g j)) |>.trans
    (c (S.blockPerm g j))

/-- The same local factor indexed by its target block, matching the
convention of `ImprimitiveLinearActionData`. -/
def targetLocalEquiv
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (g : K) (i : I) : W ≃ₗ[R] W :=
  S.sourceLocalEquiv c g ((S.blockPerm g).symm i)

theorem targetLocalEquiv_at_image
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (g : K) (j : I) :
    S.targetLocalEquiv c g (S.blockPerm g j) =
      S.sourceLocalEquiv c g j := by
  exact congrArg (S.sourceLocalEquiv c g) (Equiv.symm_apply_apply _ _)

/-- The original group written in the canonical common-block coordinates.
-/
abbrev coordinateSubgroup
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) :
    Subgroup (LinearMap.GeneralLinearGroup R (I → W)) :=
  K.map (LinearMap.GeneralLinearGroup.congrLinearEquiv
    (S.productCoordinates c)).toMonoidHom

/-- The canonical group isomorphism implementing the coordinate change. -/
def coordinateSubgroupEquiv
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) :
    K ≃* S.coordinateSubgroup c :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv
    (S.productCoordinates c)).subgroupMap K

@[simp]
theorem coordinateSubgroupEquiv_coe
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (g : K) :
    ((S.coordinateSubgroupEquiv c g : S.coordinateSubgroup c) :
      LinearMap.GeneralLinearGroup R (I → W)) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv
        (S.productCoordinates c) g :=
  rfl

/-- **Internal submodule systems produce coordinate block systems.**

The proof uses the canonical equivalence from internal direct-sum
coordinates and derives the action on a coordinate injection from
`map_block`. -/
def coordinateLinearBlockSystem
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) :
    CoordinateLinearBlockSystem (S.coordinateSubgroup c) where
  blockPerm :=
    S.blockPerm.comp (S.coordinateSubgroupEquiv c).symm.toMonoidHom
  blockLinear g i := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (S.targetLocalEquiv c ((S.coordinateSubgroupEquiv c).symm g) i)
  action_single g j w := by
    classical
    let k : K := (S.coordinateSubgroupEquiv c).symm g
    let x : S.block j := (c j).symm w
    let target : I := S.blockPerm k j
    have hg : (g : LinearMap.GeneralLinearGroup R (I → W)) =
        LinearMap.GeneralLinearGroup.congrLinearEquiv
          (S.productCoordinates c) k := by
      have h := congrArg Subtype.val
        ((S.coordinateSubgroupEquiv c).apply_symm_apply g)
      exact h.symm
    have hxcoord :
        S.productCoordinates c (x : V) = Pi.single j w := by
      simpa [x] using S.productCoordinates_coe_block c j x
    let y : S.block target :=
      (k.1.toLinearEquiv.ofSubmodules
        (S.block j) (S.block target) (S.map_block k j)) x
    have hycoord : S.productCoordinates c (y : V) =
        Pi.single target (c target y) :=
      S.productCoordinates_coe_block c target y
    calc
      g.1 • (Pi.single j w : I → W) =
          g.1 • S.productCoordinates c (x : V) := by rw [hxcoord]
      _ = S.productCoordinates c (k.1 • (x : V)) := by
        rw [hg]
        change S.productCoordinates c
          (k.1.toLinearEquiv ((S.productCoordinates c).symm
            (S.productCoordinates c (x : V)))) =
          S.productCoordinates c (k.1.toLinearEquiv (x : V))
        rw [(S.productCoordinates c).symm_apply_apply]
      _ = S.productCoordinates c (y : V) := by rfl
      _ = Pi.single target (c target y) := hycoord
      _ = Pi.single
          ((S.blockPerm.comp
            (S.coordinateSubgroupEquiv c).symm.toMonoidHom) g j)
          ((LinearMap.GeneralLinearGroup.ofLinearEquiv
            (S.targetLocalEquiv c ((S.coordinateSubgroupEquiv c).symm g)
              ((S.blockPerm.comp
                (S.coordinateSubgroupEquiv c).symm.toMonoidHom) g j))).1 • w) := by
        change Pi.single target (c target y) =
          (Pi.single target
            ((LinearMap.GeneralLinearGroup.ofLinearEquiv
              (S.targetLocalEquiv c k target)).1 • w) : I → W)
        simp only [target]
        rw [S.targetLocalEquiv_at_image]
        rfl

/-- Conjugating into block coordinates does not change the concrete
permutation image on block indices. -/
theorem coordinateLinearBlockSystem_blockPerm_range
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) :
    (S.coordinateLinearBlockSystem c).blockPerm.range =
      S.blockPerm.range := by
  ext q
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(S.coordinateSubgroupEquiv c).symm g, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨S.coordinateSubgroupEquiv c g, ?_⟩
    simp [coordinateLinearBlockSystem]

/-- The complete imprimitive action data extracted from an internal linear
system and common coordinates on its blocks. -/
abbrev imprimitiveLinearActionData
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) :
    ImprimitiveLinearActionData (S.coordinateSubgroup c)
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W)) :=
  (S.coordinateLinearBlockSystem c).imprimitiveLinearActionData

end LinearImprimitivitySystem

/-! ## Primitive top presentations -/

/-- A coordinate block system chosen coarsely enough that its induced top is
primitive.  Finiteness and faithfulness of the concrete top range are
automatic for finite `I`; the only nonformal structural input is
preprimitivity. -/
structure PrimitiveCoordinateLinearBlockSystem
    [Fintype I] [DecidableEq I]
    (K : Subgroup
      (LinearMap.GeneralLinearGroup R (I → W))) where
  toCoordinateLinearBlockSystem : CoordinateLinearBlockSystem K
  top_preprimitive :
    MulAction.IsPreprimitive toCoordinateLinearBlockSystem.blockPerm.range I

namespace PrimitiveCoordinateLinearBlockSystem

variable [Fintype I] [DecidableEq I]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup R (I → W))}

/-- The imprimitive data extracted from a primitive coordinate block system.
-/
abbrev imprimitiveLinearActionData
    (S : PrimitiveCoordinateLinearBlockSystem K) :
    ImprimitiveLinearActionData K
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W)) :=
  S.toCoordinateLinearBlockSystem.imprimitiveLinearActionData

end PrimitiveCoordinateLinearBlockSystem

namespace LinearImprimitivitySystem

variable [AddCommGroup V] [Module R V]
variable [Fintype I] [DecidableEq I]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

/-- A primitive top certificate on an internal submodule system is
preserved by the canonical change to common block coordinates. -/
def primitiveCoordinateLinearBlockSystem
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W)
    (hprimitive : MulAction.IsPreprimitive S.blockPerm.range I) :
    PrimitiveCoordinateLinearBlockSystem (S.coordinateSubgroup c) where
  toCoordinateLinearBlockSystem := S.coordinateLinearBlockSystem c
  top_preprimitive := by
    rw [S.coordinateLinearBlockSystem_blockPerm_range]
    exact hprimitive

end LinearImprimitivitySystem

/-! ## Arbitrary prime-field actions -/

variable {r : ℕ}
variable [AddCommGroup V] [Module (ZMod r) V]

/-- Representation-independent irreducibility for an arbitrary concrete
linear action.  This is the arbitrary-module analogue of
`IsIrreducibleLinearAction`. -/
def IsIrreducibleLinearActionOn
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ U : Submodule (ZMod r) V,
    (∀ k : K, ∀ v ∈ U,
      (k : LinearMap.GeneralLinearGroup (ZMod r) V) • v ∈ U) →
    U = ⊥ ∨ U = ⊤

/-- An explicit primitive imprimitive presentation of an arbitrary
prime-field linear action.

The inequalities `1 < b` and `0 < e` certify that this is genuinely
imprimitive rather than the one-block or zero-local-space degeneration.
Irreducibility is retained as part of the intended input, although the
construction of action data itself needs only the block witness. -/
structure PrimeFieldPrimitiveImprimitivityPresentation
    (r b e : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) where
  field_prime : Nat.Prime r
  irreducible : IsIrreducibleLinearActionOn K
  blockCount_one_lt : 1 < b
  localDimension_pos : 0 < e
  coordinates : V ≃ₗ[ZMod r] (Fin b → (Fin e → ZMod r))
  system : PrimitiveCoordinateLinearBlockSystem
    (NCASLinearEquiv.conjugateSubgroup coordinates K)

namespace PrimeFieldPrimitiveImprimitivityPresentation

variable {b e : ℕ}
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}

/-- The common action in block coordinates. -/
abbrev blockAction
    (P : PrimeFieldPrimitiveImprimitivityPresentation r b e V K) :=
  NCASLinearEquiv.conjugateSubgroup P.coordinates K

/-- The imprimitive action data canonically extracted on the conjugated
block-coordinate action. -/
abbrev imprimitiveLinearActionData
    (P : PrimeFieldPrimitiveImprimitivityPresentation r b e V K) :
    ImprimitiveLinearActionData P.blockAction
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup (ZMod r)
        (Fin e → ZMod r))) :=
  P.system.imprimitiveLinearActionData

/-- The presentation certifies that the original module is finite. -/
theorem finite_space
    (P : PrimeFieldPrimitiveImprimitivityPresentation r b e V K) :
    Finite V := by
  letI : NeZero r := ⟨P.field_prime.ne_zero⟩
  exact Finite.of_injective P.coordinates P.coordinates.injective

/-- Consequently the presented common linear group is finite as well. -/
theorem finite_action
    (P : PrimeFieldPrimitiveImprimitivityPresentation r b e V K) :
    Finite K := by
  letI : Finite V := P.finite_space
  let f : K → (V → V) := fun g v ↦ g.1 • v
  apply Finite.of_injective f
  intro g h hgh
  apply Subtype.ext
  ext v
  exact congrFun hgh v

/-- The extracted top is finite. -/
theorem top_finite
    (P : PrimeFieldPrimitiveImprimitivityPresentation r b e V K) :
    Finite P.imprimitiveLinearActionData.blockPerm.range := by
  infer_instance

/-- The extracted top acts faithfully on the block set. -/
theorem top_faithful
    (P : PrimeFieldPrimitiveImprimitivityPresentation r b e V K) :
    FaithfulSMul P.imprimitiveLinearActionData.blockPerm.range (Fin b) := by
  infer_instance

/-- The extracted top is primitive by the presentation's coarseness
certificate. -/
theorem top_preprimitive
    (P : PrimeFieldPrimitiveImprimitivityPresentation r b e V K) :
    MulAction.IsPreprimitive
      P.imprimitiveLinearActionData.blockPerm.range (Fin b) :=
  P.system.top_preprimitive

end PrimeFieldPrimitiveImprimitivityPresentation

/-! ## Internal-submodule prime-field presentations -/

/-- A primitive imprimitive presentation stated entirely in the original
module, using actual invariant submodule blocks.

Unlike `PrimeFieldPrimitiveImprimitivityPresentation`, global product
coordinates are not supplied: they are constructed canonically from the
internal direct sum.  The only coordinate choices identify the individual
blocks with one common local model.  `top_preprimitive` records the endpoint
that the maximal-block construction in
`LinearImprimitivityOrbitCoarsening.lean` can now supply. -/
structure PrimeFieldPrimitiveInternalImprimitivityPresentation
    (r b e : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) where
  field_prime : Nat.Prime r
  irreducible : LinearImprimitivitySystem.IsIrreducible K
  blockCount_one_lt : 1 < b
  localDimension_pos : 0 < e
  system : LinearImprimitivitySystem (I := Fin b) K
  localCoordinates : ∀ i, system.block i ≃ₗ[ZMod r] (Fin e → ZMod r)
  top_preprimitive :
    MulAction.IsPreprimitive system.blockPerm.range (Fin b)

namespace PrimeFieldPrimitiveInternalImprimitivityPresentation

variable {b e : ℕ}
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}

/-- The canonical global coordinate change extracted from internality. -/
abbrev coordinates
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K) :
    V ≃ₗ[ZMod r] (Fin b → (Fin e → ZMod r)) :=
  P.system.productCoordinates P.localCoordinates

/-- The original common action conjugated by the canonical product
coordinates. -/
abbrev blockAction
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K) :=
  P.system.coordinateSubgroup P.localCoordinates

/-- The complete imprimitive action data extracted from the internal
submodule system. -/
abbrev imprimitiveLinearActionData
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K) :
    ImprimitiveLinearActionData P.blockAction
      (⊤ : Subgroup (LinearMap.GeneralLinearGroup (ZMod r)
        (Fin e → ZMod r))) :=
  P.system.imprimitiveLinearActionData P.localCoordinates

/-- Irreducibility forces transitivity of the chosen block system before
any primitivity certificate is used. -/
theorem top_pretransitive
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K) :
    MulAction.IsPretransitive P.system.blockPerm.range (Fin b) :=
  P.system.blockPerm_range_isPretransitive_of_irreducible P.irreducible

/-- Forgetting the internal origin of the coordinates gives the earlier
coordinate-level presentation. -/
def toPrimitiveImprimitivityPresentation
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K) :
    PrimeFieldPrimitiveImprimitivityPresentation r b e V K where
  field_prime := P.field_prime
  irreducible := by
    intro U hU
    exact P.irreducible U hU
  blockCount_one_lt := P.blockCount_one_lt
  localDimension_pos := P.localDimension_pos
  coordinates := P.coordinates
  system := P.system.primitiveCoordinateLinearBlockSystem
    P.localCoordinates P.top_preprimitive

/-- An internal primitive presentation certifies finiteness of the original
space. -/
theorem finite_space
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K) :
    Finite V :=
  P.toPrimitiveImprimitivityPresentation.finite_space

/-- Hence its concrete common group is finite. -/
theorem finite_action
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation r b e V K) :
    Finite K :=
  P.toPrimitiveImprimitivityPresentation.finite_action

end PrimeFieldPrimitiveInternalImprimitivityPresentation

end LisiSabatini
