module

public import LisiSabatini.CliffordImprimitivity
public import LisiSabatini.BlockStabilizerLocalAction
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.RepresentationTheory.Invariants

/-!
# Specified prime-index blocks for translated regularity

The nilpotent translated-orbit induction must split over an explicitly chosen
odd Sylow subgroup. An arbitrary imprimitivity system need not do this: its
permutation top could have order two. This file retains the centralizer of
the chosen normal subgroup throughout the Clifford extraction.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra Pointwise

namespace Clifford

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- An element centralizing the restricted subgroup induces the identity
automorphism of its group algebra. -/
theorem restrictionConjugationRingEquiv_eq_refl_of_mem_centralizer
    (B : Subgroup G) [B.Normal] (g : G)
    (hg : g ∈ Subgroup.centralizer (B : Set G)) :
    restrictionConjugationRingEquiv (k := k) B g = RingEquiv.refl _ := by
  have hconj : MulAut.conjNormal g = MulEquiv.refl B := by
    ext b
    change g * (b : G) * g⁻¹ = b
    have hc : (b : G) * g = g * b :=
      Subgroup.mem_centralizer_iff.mp hg b b.2
    rw [← hc, mul_assoc, mul_inv_cancel, mul_one]
  simp only [restrictionConjugationRingEquiv, hconj, MonoidAlgebra.domCongr_refl]
  rfl

/-- A centralizing ambient element acts linearly over the restricted group
algebra, so every isotypic component is invariant under it. -/
def centralizerRestrictionEnd
    (rho : Representation k G V) (B : Subgroup G) [B.Normal]
    (tau : Representation k B V) (htau : ∀ b : B, tau b = rho b.1)
    (g : G) (hg : g ∈ Subgroup.centralizer (B : Set G)) :
    Module.End k[B] (RestrictionModule B tau) where
  toFun v := (restrictionModuleEquiv B tau).symm
    (rho g (restrictionModuleEquiv B tau v))
  map_add' x y := by simp
  map_smul' a v := by
    simpa only [restrictionConjugationRingEquiv_eq_refl_of_mem_centralizer
      B g hg, RingEquiv.refl_apply, RingHom.id_apply] using
      restriction_conjugation_smul rho B tau htau g a v

variable {K : Subgroup (LinearMap.GeneralLinearGroup k V)}

/-- The centralizer of a normal subgroup preserves the underlying subspace
of each of its isotypic components, not merely the set of components. -/
theorem linearSubmoduleImage_underlyingRestrictionComponent_eq_of_mem_centralizer
    (B : Subgroup K) [B.Normal]
    (C : isotypicComponents k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B)))
    (g : K) (hg : g ∈ Subgroup.centralizer (B : Set K)) :
    linearSubmoduleImage g
      (underlyingRestrictionComponent B (concreteRestrictionRepresentation B) C.1) =
      underlyingRestrictionComponent B (concreteRestrictionRepresentation B) C.1 := by
  let U := underlyingRestrictionComponent B (concreteRestrictionRepresentation B) C.1
  have hle (a : K) (ha : a ∈ Subgroup.centralizer (B : Set K)) :
      linearSubmoduleImage a U ≤ U := by
    intro x hx
    change x ∈ U.map (linearSubgroupRepresentation K a) at hx
    rcases hx with ⟨y, hy, rfl⟩
    rcases hy with ⟨z, hz, rfl⟩
    refine ⟨centralizerRestrictionEnd (linearSubgroupRepresentation K) B
      (concreteRestrictionRepresentation B)
      (concreteRestrictionRepresentation_apply B) a ha z, ?_, ?_⟩
    · exact Submodule.IsFullyInvariant.of_mem_isotypicComponents C.2 _ hz
    · rfl
  apply le_antisymm (hle g hg)
  have hinv := hle g⁻¹ (Subgroup.inv_mem _ hg)
  have hmap :
      linearSubmoduleImage g (linearSubmoduleImage g⁻¹ U) ≤
        linearSubmoduleImage g U := Submodule.map_mono hinv
  simpa only [← linearSubmoduleImage_mul, mul_inv_cancel,
    linearSubmoduleImage_one] using hmap

/-- Clifford extraction retaining the specified normal subgroup. In
particular, its centralizer fixes the extracted base block setwise. -/
theorem exists_linearImprimitivityExtractionWitness_centralizer_fixes
    [FiniteDimensional k V] [Finite K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (B : Subgroup K) [B.Normal]
    (hnotiso : ¬ IsIsotypic k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B))) :
    ∃ W : LinearImprimitivityExtractionWitness K,
      ∀ g ∈ Subgroup.centralizer (B : Set K),
        linearSubmoduleImage g W.base = W.base := by
  have hMnontrivial : Nontrivial
      (RestrictionModule B (concreteRestrictionRepresentation B)) := by
    by_contra htriv
    have : Subsingleton
        (RestrictionModule B (concreteRestrictionRepresentation B)) :=
      not_nontrivial_iff_subsingleton.mp htriv
    exact hnotiso (IsIsotypic.of_subsingleton k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B)))
  have : Nontrivial V := hMnontrivial
  have hrhoirr : (linearSubgroupRepresentation K).IsIrreducible :=
    linearSubgroupRepresentation_isIrreducible_of_project hirr
  have : IsSemisimpleModule k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B)) :=
    Representation.isSemisimpleModule_normalRestriction
      (linearSubgroupRepresentation K) B hrhoirr
  obtain ⟨S, hSsimple⟩ :=
    IsSemisimpleModule.exists_simple_submodule k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B))
  let C : isotypicComponents k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B)) :=
    ⟨isotypicComponent k[B]
        (RestrictionModule B (concreteRestrictionRepresentation B)) S,
      ⟨S, hSsimple, rfl⟩⟩
  have hCtop : C.1 ≠ ⊤ := by
    intro htop
    apply hnotiso
    apply Submodule.topEquiv.isIsotypic_iff.mp
    rw [← htop]
    exact IsIsotypic.isotypicComponents C.2
  refine ⟨LinearImprimitivityExtractionWitness.ofFiniteGroup hirr
    (underlyingRestrictionComponent B
      (concreteRestrictionRepresentation B) C.1)
    (underlyingRestrictionComponent_ne_bot B C)
    (underlyingRestrictionComponent_ne_top B C hCtop)
    (orbit_underlyingRestrictionComponent_iSupIndep B C), ?_⟩
  exact fun g hg =>
    linearSubmoduleImage_underlyingRestrictionComponent_eq_of_mem_centralizer B C g hg

end Clifford

namespace LinearImprimitivitySystem

variable {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
  [Fintype I] [DecidableEq I]
  {K : Subgroup (LinearMap.GeneralLinearGroup k V)}

/-- The faithful local image of a block stabilizer inherits nilpotency. -/
theorem blockStabilizerLocalImage_isNilpotent
    [Group.IsNilpotent K]
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    Group.IsNilpotent (S.blockStabilizerLocalImage i) :=
  Group.nilpotent_of_surjective (S.blockStabilizerLocalRangeHom i)
    (S.blockStabilizerLocalRangeHom_surjective i)

/-- A nontrivial normal subgroup fixing all blocks has nontrivial image on
every block. Otherwise its fixed space contains one nonzero block, and
normality and irreducibility force the fixed space to be the whole module.
This retains active prime support in the local induction. -/
theorem componentBaseImageInBlockStabilizerLocal_ne_bot
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (P : Subgroup K) [P.Normal]
    (hPker : P ≤ S.blockPerm.ker) (hPne : P ≠ ⊥) (i : I) :
    S.componentBaseImageInBlockStabilizerLocal P i ≠ ⊥ := by
  intro hlocal
  have hmap : S.componentBaseInBlockStabilizer P i ≤
      (S.blockStabilizerLocalRangeHom i).ker :=
    (Subgroup.map_eq_bot_iff _).mp hlocal
  let U := _root_.Representation.invariants
    ((linearSubgroupRepresentation K).comp P.subtype)
  have hblock : S.block i ≤ U := by
    intro x hx p
    have hfix : S.blockPerm p.1 i = i :=
      congrArg (fun f : Equiv.Perm I => f i) (hPker p.2)
    let g : S.blockStabilizer i :=
      ⟨p.1, (S.mem_blockStabilizer_iff i p.1).mpr hfix⟩
    have hg : g ∈ S.componentBaseInBlockStabilizer P i := ⟨p.2, hPker p.2⟩
    have hhom : S.blockStabilizerLocalHom i g = 1 :=
      congrArg Subtype.val (hmap hg)
    have hpoint := congrArg
      (fun a : LinearMap.GeneralLinearGroup k (S.block i) =>
        ((a • (⟨x, hx⟩ : S.block i) : S.block i) : V)) hhom
    simp only [S.blockStabilizerLocalHom_apply_coe, one_smul] at hpoint
    exact hpoint
  have hUinv : ∀ g : K, ∀ v ∈ U, g.1 • v ∈ U := by
    intro g v hv
    exact _root_.Representation.le_comap_invariants
      (linearSubgroupRepresentation K) P g hv
  have hUtop : U = ⊤ := by
    rcases hirr U hUinv with hbot | htop
    · exact (S.block_ne_bot i (bot_unique (hblock.trans_eq hbot))).elim
    · exact htop
  apply hPne
  apply le_antisymm _ bot_le
  intro p hp
  rw [Subgroup.mem_bot]
  apply linearSubgroupRepresentation_faithful K
  apply LinearMap.ext
  intro x
  have hx : x ∈ U := by rw [hUtop]; trivial
  rw [map_one, Module.End.one_apply]
  exact hx (⟨p, hp⟩ : P)

/-- If a prescribed normal subgroup of prime index fixes one block, it is
exactly every block stabilizer and the permutation kernel. Thus the top is
the prescribed prime quotient, rather than an arbitrarily chosen top. -/
theorem prime_index_normal_block_structure
    [Nontrivial I]
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K)
    (H : Subgroup K) [H.Normal] {q : ℕ} (hq : q.Prime)
    (hindex : H.index = q) (i₀ : I)
    (hfix : H ≤ S.blockStabilizer i₀) :
    Nat.card I = q ∧ (∀ i, S.blockStabilizer i = H) ∧ S.blockPerm.ker = H := by
  let : MulAction K I := S.indexAction
  have : MulAction.IsPretransitive K I :=
    S.indexAction_isPretransitive_of_irreducible hirr
  have hbridge (i : I) : MulAction.stabilizer K i = S.blockStabilizer i := by
    ext g
    rfl
  have hproper : S.blockStabilizer i₀ ≠ ⊤ := by
    intro htop
    obtain ⟨j, hj⟩ := exists_ne i₀
    obtain ⟨g, hg⟩ := S.isIndexPretransitive_of_irreducible hirr i₀ j
    have hm : g ∈ S.blockStabilizer i₀ := by simp [htop]
    exact hj (hg.symm.trans ((S.mem_blockStabilizer_iff i₀ g).mp hm))
  have hstabindex : (S.blockStabilizer i₀).index = q := by
    have hdvd : (S.blockStabilizer i₀).index ∣ q := by
      rw [← hindex]
      exact Subgroup.index_dvd_of_le hfix
    rcases (Nat.dvd_prime hq).mp hdvd with h | h
    · exact (hproper (Subgroup.index_eq_one.mp h)).elim
    · exact h
  have hbase : S.blockStabilizer i₀ = H := by
    have hmul := Subgroup.relIndex_mul_index hfix
    rw [hstabindex, hindex] at hmul
    have hrel : H.relIndex (S.blockStabilizer i₀) = 1 :=
      Nat.eq_of_mul_eq_mul_right hq.pos (by simpa using hmul)
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hrel) hfix
  have hstabs (i : I) : S.blockStabilizer i = H := by
    obtain ⟨g, hg⟩ := S.isIndexPretransitive_of_irreducible hirr i₀ i
    have hsmul : g • i₀ = i := hg
    rw [← hbridge i, ← hsmul,
      MulAction.stabilizer_smul_eq_stabilizer_map_conj, hbridge i₀, hbase]
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.Normal.map_conj_eq H g
  refine ⟨?_, hstabs, ?_⟩
  · calc
      Nat.card I = (MulAction.stabilizer K i₀).index :=
        (MulAction.index_stabilizer_of_transitive K i₀).symm
      _ = H.index := by rw [hbridge i₀, hbase]
      _ = q := hindex
  · ext g
    constructor
    · intro hg
      rw [← hbase, S.mem_blockStabilizer_iff]
      exact congrArg (fun f : Equiv.Perm I => f i₀) hg
    · intro hg
      apply Equiv.ext
      intro i
      exact (S.mem_blockStabilizer_iff i g).mp (by rwa [hstabs i])

end LinearImprimitivitySystem

namespace Clifford

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  {K : Subgroup (LinearMap.GeneralLinearGroup k V)}

/-- A faithful coprime representation of a finite noncyclic abelian group
over a finite field cannot be isotypic. This supplies the Clifford input
for the chosen elementary abelian subgroup of rank two. -/
theorem not_isotypic_concreteRestriction_of_noncyclic
    [Finite k] [Finite V] [Finite K]
    (B : Subgroup K) [NeZero (Nat.card B : k)]
    (hcomm : ∀ a b : B, Commute a b) (hncyclic : ¬ IsCyclic B) :
    ¬ IsIsotypic k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B)) := by
  intro hiso
  apply hncyclic
  exact isCyclic_of_faithful_isIsotypic_of_commuting
    (concreteRestrictionRepresentation B) hiso hcomm
    ((linearSubgroupRepresentation_faithful K).comp B.subtype_injective)

/-- The specified-centralizer Clifford decomposition. The hypotheses expose
the two independent structural inputs: the chosen restriction is not
isotypic, and the chosen centralizer has the desired prime index.
The resulting local concrete images act faithfully by construction and are
irreducible; their defining restriction maps need not be faithful. -/
theorem exists_prime_index_centralizer_blocks
    [FiniteDimensional k V] [Finite K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (B : Subgroup K) [B.Normal]
    (hnotiso : ¬ IsIsotypic k[B]
      (RestrictionModule B (concreteRestrictionRepresentation B)))
    {q : ℕ} (hq : q.Prime)
    (hindex : (Subgroup.centralizer (B : Set K)).index = q) :
    ∃ W : LinearImprimitivityExtractionWitness K,
      Nat.card (SubmoduleOrbitIndex K W.base) = q ∧
      (∀ i, W.toLinearImprimitivitySystem.blockStabilizer i =
        Subgroup.centralizer (B : Set K)) ∧
      W.toLinearImprimitivitySystem.blockPerm.ker =
        Subgroup.centralizer (B : Set K) ∧
      ∀ i, LinearImprimitivitySystem.IsIrreducible
        (W.toLinearImprimitivitySystem.blockStabilizerLocalImage i) := by
  obtain ⟨W, hfix⟩ :=
    exists_linearImprimitivityExtractionWitness_centralizer_fixes hirr B hnotiso
  have : Nontrivial (SubmoduleOrbitIndex K W.base) := W.orbitIndex_nontrivial
  have hfix' : Subgroup.centralizer (B : Set K) ≤
      W.toLinearImprimitivitySystem.blockStabilizer W.baseIndex := by
    intro g hg
    rw [LinearImprimitivitySystem.mem_blockStabilizer_iff]
    apply Subtype.ext
    exact hfix g hg
  obtain ⟨hcard, hstabs, hker⟩ :=
    W.toLinearImprimitivitySystem.prime_index_normal_block_structure W.irreducible
      (Subgroup.centralizer (B : Set K)) hq hindex W.baseIndex hfix'
  exact ⟨W, hcard, hstabs, hker, fun i =>
    W.toLinearImprimitivitySystem.blockStabilizerLocalImage_isIrreducible W.irreducible i⟩

end Clifford

/-- All prime-power subgroups at primes different from the chosen prime
lie in a normal subgroup of that prime index. This is the reason the
2-component fixes every block in the odd-top induction. -/
theorem isPGroup_le_normal_of_distinct_prime_index
    {G : Type*} [Group G] [Finite G]
    (H P : Subgroup G) [H.Normal] {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hne : p ≠ q)
    (hP : IsPGroup p P) (hindex : H.index = q) : P ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hcop : H.index.Coprime (Nat.card P) := by
    rw [hindex, hn]
    exact ((Nat.coprime_primes hq hp).mpr hne.symm).pow_right n
  rw [← Subgroup.relIndex_eq_one]
  exact Nat.eq_one_of_dvd_coprimes hcop
    (H.relIndex_dvd_index_of_normal P) (Subgroup.relIndex_dvd_card H P)

end LisiSabatini
