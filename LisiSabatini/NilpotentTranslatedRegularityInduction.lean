module

public import LisiSabatini.NilpotentTranslatedRegularitySylowReduction
public import LisiSabatini.NilpotentTranslatedRegularityBlocks
public import LisiSabatini.NilpotentTranslatedRegularityComposition
public import LisiSabatini.NilpotentTranslatedRegularityCoordinates
public import LisiSabatini.NilpotentTranslatedRegularityAbelianOddHall
public import LisiSabatini.RegularAbelianTop
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The structural odd-top step for nilpotent translated regularity

This file proves the mixed-prime irreducible translated-orbit theorem by
strong induction on dimension. The noncyclic odd-Sylow branch uses the
specified-centralizer Clifford decomposition, retaining every active local
Sylow subgroup and strictly decreasing the dimension. The central odd
component branch uses the scalar palette. The resulting theorem retains
literal containment of the distinguished 2-stabilizer and avoids any
prescribed orbit of any selected odd Sylow subgroup.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

namespace LinearImprimitivitySystem

variable {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
  [Fintype I] [DecidableEq I]
  {K : Subgroup (LinearMap.GeneralLinearGroup k V)}

/-- A nonzero member of a nontrivial internal block family is proper. -/
theorem block_ne_top_of_nontrivial [Nontrivial I]
    (S : LinearImprimitivitySystem (I := I) K) (i : I) : S.block i ≠ ⊤ := by
  intro htop
  obtain ⟨j, hji⟩ := exists_ne i
  have hdisj : Disjoint (S.block j) (S.block i) :=
    S.iSupIndep_block.pairwiseDisjoint hji
  rw [htop, disjoint_top] at hdisj
  exact S.block_ne_bot j hdisj

/-- Every block is a strictly smaller positive-dimensional local problem. -/
theorem block_finrank_pos_lt [FiniteDimensional k V] [Nontrivial I]
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    0 < Module.finrank k (S.block i) ∧
      Module.finrank k (S.block i) < Module.finrank k V := by
  constructor
  · have : Nontrivial (S.block i) := Submodule.nontrivial_iff_ne_bot.mpr (S.block_ne_bot i)
    exact Module.finrank_pos
  · simpa only [finrank_top] using
      Submodule.finrank_lt_finrank_of_lt
        (lt_top_iff_ne_top.mpr (S.block_ne_top_of_nontrivial i))

/-- If all block stabilizers are the permutation kernel, the concrete top
acts regularly. This avoids any choice of a cyclic generator. -/
theorem blockPerm_range_semiregular_of_stabilizers_eq_kernel
    (S : LinearImprimitivitySystem (I := I) K)
    (hstab : ∀ i, S.blockStabilizer i = S.blockPerm.ker) :
    IsSemiregularPermutationSubgroup S.blockPerm.range := by
  intro i
  apply (Subgroup.eq_bot_iff_forall _).mpr
  rintro ⟨g, hg⟩ hfix
  obtain ⟨a, rfl⟩ := hg
  apply Subtype.ext
  have ha : a ∈ S.blockStabilizer i :=
    (S.mem_blockStabilizer_iff i a).mpr (MulAction.mem_stabilizer_iff.mp hfix)
  rw [hstab] at ha
  exact ha

/-- The prime-index quotient is exactly the image of its Sylow subgroup. -/
theorem sylow_map_blockPerm_eq_range_of_prime_kernel_index
    [Finite K] (S : LinearImprimitivitySystem (I := I) K)
    {q : ℕ} (hq : q.Prime) (hindex : S.blockPerm.ker.index = q)
    (Q : Sylow q K) : (Q : Subgroup K).map S.blockPerm = S.blockPerm.range := by
  let : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card S.blockPerm.range = q := (Subgroup.index_ker S.blockPerm).symm.trans hindex
  have hpg : IsPGroup q S.blockPerm.range := IsPGroup.of_card (by simpa using hcard :
    Nat.card S.blockPerm.range = q ^ 1)
  let Q' := Q.mapSurjective S.blockPerm.rangeRestrict_surjective
  have htop : (Q' : Subgroup S.blockPerm.range) = ⊤ :=
    top_unique ((hpg.to_subgroup ⊤).le_sylow_of_normal Q')
  have hm := congrArg (fun U : Subgroup S.blockPerm.range ↦ U.map S.blockPerm.range.subtype) htop
  simpa only [Q', Sylow.mapSurjective, Subgroup.map_map,
    MonoidHom.subtype_comp_rangeRestrict, ← MonoidHom.range_eq_map, Subgroup.range_subtype] using hm

/-- A prime component different from the chosen top prime fixes every block. -/
theorem map_blockPerm_eq_bot_of_distinct_prime_kernel_index
    [Finite K] (S : LinearImprimitivitySystem (I := I) K)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (P : Subgroup K) (hP : IsPGroup p P) (hindex : S.blockPerm.ker.index = q) :
    P.map S.blockPerm = ⊥ := by
  exact (P.map_eq_bot_iff).mpr
    (isPGroup_le_normal_of_distinct_prime_index S.blockPerm.ker P hp hq hpq hP hindex)

/-- The local base image only depends on the intersection with the
permutation kernel. -/
theorem componentBaseImage_inf_kernel
    (S : LinearImprimitivitySystem (I := I) K) (P : Subgroup K) (i : I) :
    S.componentBaseImageInBlockStabilizerLocal (P ⊓ S.blockPerm.ker) i =
      S.componentBaseImageInBlockStabilizerLocal P i := by
  simp only [componentBaseImageInBlockStabilizerLocal, componentBaseInBlockStabilizer,
    inf_assoc, inf_idem]

/-- A nontrivial normal part in the permutation kernel remains active in
every faithful local image, including the chosen top-prime component. -/
theorem componentBaseImage_ne_bot_of_inf_kernel_ne_bot
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (P : Subgroup K) [P.Normal]
    (hne : P ⊓ S.blockPerm.ker ≠ ⊥) (i : I) :
    S.componentBaseImageInBlockStabilizerLocal P i ≠ ⊥ := by
  have h := S.componentBaseImageInBlockStabilizerLocal_ne_bot hirr
    (P ⊓ S.blockPerm.ker) inf_le_right hne i
  rwa [S.componentBaseImage_inf_kernel] at h

/-- All active Sylow components survive locally. For the top prime, the
specified nontrivial normal subgroup inside the kernel supplies survival;
for every other prime the whole Sylow subgroup lies in that kernel. -/
theorem sylow_componentBaseImage_ne_bot
    [Finite K] [Group.IsNilpotent K]
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) {q : ℕ} (hq : q.Prime)
    (hindex : S.blockPerm.ker.index = q)
    (B : Subgroup K) [B.Normal] (hBq : IsPGroup q B)
    (hBne : B ≠ ⊥) (hBker : B ≤ S.blockPerm.ker)
    {p : ℕ} (hp : p.Prime) (P : Sylow p K)
    (hPne : (P : Subgroup K) ≠ ⊥) (i : I) :
    S.componentBaseImageInBlockStabilizerLocal (P : Subgroup K) i ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  apply S.componentBaseImage_ne_bot_of_inf_kernel_ne_bot hirr
  by_cases hpq : p = q
  · subst p
    have hBP : B ≤ (P : Subgroup K) := hBq.le_sylow_of_normal P
    exact fun hbot ↦ hBne (bot_unique ((le_inf hBP hBker).trans_eq hbot))
  · have hPker : (P : Subgroup K) ≤ S.blockPerm.ker :=
      isPGroup_le_normal_of_distinct_prime_index S.blockPerm.ker
        (P : Subgroup K) hp hq hpq P.isPGroup' hindex
    rwa [inf_eq_left.mpr hPker]

/-- When the block stabilizers equal the permutation kernel, the local
base images of global Sylow subgroups are precisely local Sylow subgroups.
Thus the induction retains Sylow maximality, not only prime-power order. -/
theorem exists_localSylow_eq_componentBaseImage
    [Finite K] [Group.IsNilpotent K]
    (S : LinearImprimitivitySystem (I := I) K)
    (hstab : ∀ i, S.blockStabilizer i = S.blockPerm.ker)
    {p : ℕ} (hp : p.Prime) (P : Sylow p K) (i : I) :
    ∃ Q : Sylow p (S.blockStabilizerLocalImage i),
      (Q : Subgroup (S.blockStabilizerLocalImage i)) =
        S.componentBaseImageInBlockStabilizerLocal (P : Subgroup K) i := by
  let : Fact p.Prime := ⟨hp⟩
  let : Unique (Sylow p K) := P.unique_of_normal inferInstance
  let R : Sylow p (S.blockStabilizer i) := default
  obtain ⟨P', hP'⟩ := R.exists_comap_subtype_eq
  have hPR : (P : Subgroup K).comap (S.blockStabilizer i).subtype =
      (R : Subgroup (S.blockStabilizer i)) := by
    rwa [Subsingleton.elim P' P] at hP'
  have hbase : S.componentBaseInBlockStabilizer (P : Subgroup K) i =
      (R : Subgroup (S.blockStabilizer i)) := by
    rw [← hPR]
    apply Subgroup.ext
    intro g
    change (g.1 ∈ (P : Subgroup K) ∧ g.1 ∈ S.blockPerm.ker) ↔ g.1 ∈ (P : Subgroup K)
    constructor
    · exact And.left
    · intro hg
      exact ⟨hg, (hstab i).le g.2⟩
  refine ⟨R.mapSurjective (S.blockStabilizerLocalRangeHom_surjective i), ?_⟩
  change (R : Subgroup (S.blockStabilizer i)).map (S.blockStabilizerLocalRangeHom i) = _
  rw [← hbase]
  rfl

/-- The local faithful image inherits cross characteristic from the ambient
group, so the same scalar and Clifford branches apply recursively. -/
theorem blockStabilizerLocalImage_coprime
    (S : LinearImprimitivitySystem (I := I) K) {r : ℕ}
    (hcop : r.Coprime (Nat.card K)) (i : I) :
    r.Coprime (Nat.card (S.blockStabilizerLocalImage i)) :=
  hcop.of_dvd_right
    ((Subgroup.card_range_dvd (S.blockStabilizerLocalHom i)).trans
      (S.blockStabilizer i).card_subgroup_dvd_card)

end LinearImprimitivitySystem


/-- Verified structural data for the odd-top dimension induction. The block
set is the actual orbit of one Clifford constituent. Every active global
Sylow subgroup induces a nontrivial local Sylow subgroup. -/
structure OddPrimeCliffordDescent
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (K : Subgroup (LinearMap.GeneralLinearGroup k V)) (q : ℕ) where
  witness : LinearImprimitivityExtractionWitness K
  blockCount : Nat.card (SubmoduleOrbitIndex K witness.base) = q
  topCard : Nat.card witness.toLinearImprimitivitySystem.blockPerm.range = q
  topRegular : IsSemiregularPermutationSubgroup witness.toLinearImprimitivitySystem.blockPerm.range
  topSylow : ∀ Q : Sylow q K,
    (Q : Subgroup K).map witness.toLinearImprimitivitySystem.blockPerm =
      witness.toLinearImprimitivitySystem.blockPerm.range
  otherTop : ∀ {p : ℕ}, p.Prime → p ≠ q → ∀ P : Subgroup K, IsPGroup p P →
    P.map witness.toLinearImprimitivitySystem.blockPerm = ⊥
  stabilizers : ∀ i, witness.toLinearImprimitivitySystem.blockStabilizer i =
    witness.toLinearImprimitivitySystem.blockPerm.ker
  dimension : ∀ i,
    0 < Module.finrank k (witness.toLinearImprimitivitySystem.block i) ∧
    Module.finrank k (witness.toLinearImprimitivitySystem.block i) < Module.finrank k V
  localNilpotent : ∀ i, Group.IsNilpotent
    (witness.toLinearImprimitivitySystem.blockStabilizerLocalImage i)
  localIrreducible : ∀ i, LinearImprimitivitySystem.IsIrreducible
    (witness.toLinearImprimitivitySystem.blockStabilizerLocalImage i)
  localSylow : ∀ {p : ℕ}, p.Prime → ∀ P : Sylow p K, ∀ i,
    ∃ Q : Sylow p (witness.toLinearImprimitivitySystem.blockStabilizerLocalImage i),
      (Q : Subgroup _) =
        witness.toLinearImprimitivitySystem.componentBaseImageInBlockStabilizerLocal
          (P : Subgroup K) i
  localActive : ∀ {p : ℕ}, p.Prime → ∀ P : Sylow p K, (P : Subgroup K) ≠ ⊥ → ∀ i,
    witness.toLinearImprimitivitySystem.componentBaseImageInBlockStabilizerLocal
      (P : Subgroup K) i ≠ ⊥

/-- The full structural branch from an odd noncyclic Sylow subgroup. All
prime-top, strict descent, local irreducibility, nilpotence, maximality and
activity conditions used by the recursive step are proved here. -/
theorem exists_oddPrimeCliffordDescent_of_cyclic_center
    {r : ℕ} [Fact r.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [FiniteDimensional (ZMod r) V] [Finite V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Finite K] [Group.IsNilpotent K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (hcop : r.Coprime (Nat.card K)) (hcenter : IsCyclic (Subgroup.center K))
    {q : ℕ} (hq : q.Prime) (hqOdd : Odd q) (Q : Sylow q K) (hQ : ¬ IsCyclic Q) :
    Nonempty (OddPrimeCliffordDescent K q) := by
  obtain ⟨B, hBn, hBQ, hBcard, hBc, hBexp, hBnoncyclic, hBindex⟩ :=
    exists_normal_primeSquare_of_noncyclic_odd_sylow hq hqOdd Q hQ hcenter
  let : B.Normal := hBn
  have hBcop : r.Coprime (Nat.card B) := hcop.of_dvd_right B.card_subgroup_dvd_card
  have hBchar : (Nat.card B : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Fact.out : r.Prime).coprime_iff_not_dvd.mp hBcop
  let : NeZero (Nat.card B : ZMod r) := ⟨hBchar⟩
  have hnotiso := Clifford.not_isotypic_concreteRestriction_of_noncyclic B
    (fun a b ↦ hBc.is_comm.comm a b) hBnoncyclic
  obtain ⟨W, hcard, hstabs, hker, hirrlocal⟩ :=
    Clifford.exists_prime_index_centralizer_blocks hirr B hnotiso hq hBindex
  let S := W.toLinearImprimitivitySystem
  have hstab : ∀ i, S.blockStabilizer i = S.blockPerm.ker := by
    intro i
    exact (hstabs i).trans hker.symm
  have hindex : S.blockPerm.ker.index = q := by
    rw [show S.blockPerm.ker = Subgroup.centralizer (B : Set K) from hker]
    exact hBindex
  have hBne : B ≠ ⊥ := by
    intro hbot
    apply hBnoncyclic
    rw [hbot]
    infer_instance
  have hBker : B ≤ S.blockPerm.ker := by
    rw [show S.blockPerm.ker = Subgroup.centralizer (B : Set K) from hker]
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (hBc.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩)
  have : Nontrivial (SubmoduleOrbitIndex K W.base) := W.orbitIndex_nontrivial
  refine ⟨⟨W, hcard, (Subgroup.index_ker S.blockPerm).symm.trans hindex,
    S.blockPerm_range_semiregular_of_stabilizers_eq_kernel hstab,
    S.sylow_map_blockPerm_eq_range_of_prime_kernel_index hq hindex,
    ?_, hstab, S.block_finrank_pos_lt, S.blockStabilizerLocalImage_isNilpotent,
    hirrlocal, ?_, ?_⟩⟩
  · intro p hp hpq P hP
    exact S.map_blockPerm_eq_bot_of_distinct_prime_kernel_index hp hq hpq P hP hindex
  · intro p hp P i
    exact S.exists_localSylow_eq_componentBaseImage hstab hp P i
  · intro p hp P hPne i
    exact S.sylow_componentBaseImage_ne_bot hirr hq hindex B
      (IsPGroup.of_card hBcard) hBne hBker hp P hPne i


set_option backward.isDefEq.respectTransparency false in
/-- An abelian Sylow subgroup of a finite nilpotent group is central. This
is the scalar branch complementary to the noncyclic odd-Sylow descent. -/
theorem sylow_le_center_of_nilpotent_of_abelian
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hP : IsMulCommutative P) :
    (P : Subgroup G) ≤ Subgroup.center G := by
  intro x hx
  apply map_sylow_center_le_center_of_nilpotent P
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  change (⟨x, hx⟩ : (P : Subgroup G)) ∈ Subgroup.center (P : Subgroup G)
  rw [Subgroup.mem_center_iff]
  intro y
  exact hP.is_comm.comm y ⟨x, hx⟩

/-- Irreducibility supplies the cyclic-center hypothesis automatically.
The resulting descent has no independent block, top or local-activity
assumptions. -/
theorem exists_oddPrimeCliffordDescent
    {r : ℕ} [Fact r.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [FiniteDimensional (ZMod r) V] [Finite V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Finite K] [Group.IsNilpotent K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (hcop : r.Coprime (Nat.card K))
    {q : ℕ} (hq : q.Prime) (hqOdd : Odd q) (Q : Sylow q K) (hQ : ¬ IsCyclic Q) :
    Nonempty (OddPrimeCliffordDescent K q) :=
  exists_oddPrimeCliffordDescent_of_cyclic_center K hirr hcop
    (center_isCyclic_of_irreducibleOn (Fact.out : r.Prime) hirr) hq hqOdd Q hQ


namespace OddPrimeCliffordDescent

/-- The specified odd-prime Clifford descent composes the local translated
orbit statement into the global statement. Every top hypothesis required
by the combinatorial construction follows from the descent data. -/
theorem exists_translate_of_local
    {r : ℕ} [Fact r.Prime] {V J : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite J]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hodd : ∀ j, p j ≠ 2)
    (hinj : Function.Injective p) (P : ∀ j, Sylow (p j) K)
    (T : Sylow 2 K) (jactive : J)
    (X : OddPrimeCliffordDescent K (p jactive))
    (a b : V) (t : J → V)
    (hlocal : ∀ i jparent c, ∃ w : X.witness.base,
      (MulAction.stabilizer
        ((X.witness.coordinateLocalComponent (T : Subgroup K) i).map
          (X.witness.coordinateLocalGroup i).subtype)
        (w + X.witness.blockCoordinates b i) ≤
       MulAction.stabilizer
        ((X.witness.coordinateLocalComponent (T : Subgroup K) i).map
          (X.witness.coordinateLocalGroup i).subtype)
        (X.witness.blockCoordinates a i)) ∧
      (∀ j, MulAction.stabilizer
        ((X.witness.coordinateLocalComponent (P j : Subgroup K) i).map
          (X.witness.coordinateLocalGroup i).subtype)
        (w + X.witness.blockCoordinates (t j) i) = ⊥) ∧
      ¬ SameBlockOrbit
        ((X.witness.coordinateLocalComponent (P jparent : Subgroup K) i).map
          (X.witness.coordinateLocalGroup i).subtype)
        (w + X.witness.blockCoordinates (t jparent) i) c)
    (jparent : J) (c : V) :
    ∃ v : V,
      (MulAction.stabilizer ((T : Subgroup K).map K.subtype) (v + b) ≤
        MulAction.stabilizer ((T : Subgroup K).map K.subtype) a) ∧
      (∀ j, MulAction.stabilizer ((P j : Subgroup K).map K.subtype) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit ((P jparent : Subgroup K).map K.subtype) (v + t jparent) c := by
  classical
  let : Fintype J := Fintype.ofFinite J
  let W := X.witness
  let D := W.blockCoordinateAction
  let H : J → Subgroup W.blockCoordinateGroup := fun j ↦ W.coordinateComponent (P j : Subgroup K)
  let Tc := W.coordinateComponent (T : Subgroup K)
  have : Nonempty (SubmoduleOrbitIndex K W.base) := ⟨W.baseIndex⟩
  have hTtop : (D.restrictComponent Tc).blockPerm.range = ⊥ := by
    rw [W.coordinateComponent_top_range]
    exact X.otherTop Nat.prime_two (hodd jactive).symm (T : Subgroup K) T.isPGroup'
  have htop : ∀ j, j ≠ jactive → (D.restrictComponent (H j)).blockPerm.range = ⊥ := by
    intro j hj
    rw [W.coordinateComponent_top_range]
    exact X.otherTop (hp j) (hinj.ne hj) (P j : Subgroup K) (P j).isPGroup'
  have hactive : (D.restrictComponent (H jactive)).blockPerm.range =
      W.toLinearImprimitivitySystem.blockPerm.range := by
    rw [W.coordinateComponent_top_range]
    exact X.topSylow (P jactive)
  have hcard : Nat.card (D.restrictComponent (H jactive)).blockPerm.range =
      Fintype.card (SubmoduleOrbitIndex K W.base) := by
    rw [hactive, X.topCard, ← Nat.card_eq_fintype_card]
    exact X.blockCount.symm
  have htopOdd : Odd (Nat.card (D.restrictComponent (H jactive)).blockPerm.range) := by
    rw [hactive, X.topCard]
    exact (hp jactive).odd_of_ne_two (hodd jactive)
  have hthree : 3 ≤ Nat.card (D.restrictComponent (H jactive)).blockPerm.range := by
    rw [hactive, X.topCard]
    have := (hp jactive).two_le
    have := hodd jactive
    omega
  have hsemi : IsSemiregularPermutationSubgroup
      (D.restrictComponent (H jactive)).blockPerm.range := by
    rw [hactive]
    exact X.topRegular
  have hlocal' : ∀ i jparent c, ∃ w : W.base,
      (MulAction.stabilizer (D.componentBaseImageInCommonLocalGL Tc i)
        (w + W.blockCoordinates b i) ≤
       MulAction.stabilizer (D.componentBaseImageInCommonLocalGL Tc i)
        (W.blockCoordinates a i)) ∧
      (∀ j, MulAction.stabilizer (D.componentBaseImageInCommonLocalGL (H j) i)
        (w + W.blockCoordinates (t j) i) = ⊥) ∧
      ¬ SameBlockOrbit (D.componentBaseImageInCommonLocalGL (H jparent) i)
        (w + W.blockCoordinates (t jparent) i) c := by
    intro i jparent c
    obtain ⟨w, hT, hP, horbit⟩ := hlocal i jparent c
    refine ⟨w, ?_, ?_, ?_⟩
    · exact (congrArg (fun U : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) W.base) ↦
        MulAction.stabilizer U (w + W.blockCoordinates b i) ≤
        MulAction.stabilizer U (W.blockCoordinates a i))
        (W.coordinateLocalComponent_map_eq (T : Subgroup K) i)).mp hT
    · intro j
      exact (congrArg (fun U : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) W.base) ↦
        MulAction.stabilizer U (w + W.blockCoordinates (t j) i) = ⊥)
        (W.coordinateLocalComponent_map_eq (P j : Subgroup K) i)).mp (hP j)
    · exact (congrArg (fun U : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) W.base) ↦
        ¬ SameBlockOrbit U (w + W.blockCoordinates (t jparent) i) c)
        (W.coordinateLocalComponent_map_eq (P jparent : Subgroup K) i)).mp horbit
  obtain ⟨v, hvT, hvP, hvOrbit⟩ :=
    D.exists_regular_translate_preserving_stabilizer_avoidingOrbit_of_regularOddTop
      Tc hTtop H (W.blockCoordinates a) (W.blockCoordinates b)
      (fun j ↦ W.blockCoordinates (t j)) hlocal' jactive htop hcard
      htopOdd hthree hsemi jparent (W.blockCoordinates c)
  refine ⟨W.blockCoordinates.symm v, ?_, ?_, ?_⟩
  · apply (W.coordinateComponent_stabilizer_le_iff (T : Subgroup K)
      (W.blockCoordinates.symm v + b) a).mp
    simpa only [map_add, LinearEquiv.apply_symm_apply] using hvT
  · intro j
    apply (W.coordinateComponent_stabilizer_eq_bot_iff (P j : Subgroup K)
      (W.blockCoordinates.symm v + t j)).mp
    simpa only [map_add, LinearEquiv.apply_symm_apply] using hvP j
  · intro h
    apply hvOrbit
    have h' := (W.coordinateComponent_sameBlockOrbit_iff (P jparent : Subgroup K)
      (W.blockCoordinates.symm v + t jparent) c).mpr h
    simpa only [map_add, LinearEquiv.apply_symm_apply] using h'

end OddPrimeCliffordDescent


/-- Mixed-prime irreducible translated regularity, with the stronger
invariant needed for induction: literal containment of the 2-stabilizer
and avoidance of any prescribed orbit of any selected odd Sylow subgroup.
The selected odd Sylows need not exhaust the odd prime divisors of K. -/
theorem exists_translated_regular_sylows_of_irreducible_mixed
    {r : ℕ} [Fact r.Prime] {V J : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    [FiniteDimensional (ZMod r) V] [Nontrivial V] [Fintype J]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Finite K] [Group.IsNilpotent K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (hcop : r.Coprime (Nat.card K))
    (p : J → ℕ) (hp : ∀ j, (p j).Prime) (hodd : ∀ j, p j ≠ 2)
    (hinj : Function.Injective p) (P : ∀ j, Sylow (p j) K)
    (hPne : ∀ j, (P j : Subgroup K) ≠ ⊥)
    (T : Sylow 2 K) (hsupport : (T : Subgroup K) ≠ ⊥ ∨ 2 ≤ Fintype.card J)
    (a b : V) (t : J → V) (jparent : J) (c : V) :
    ∃ v : V,
      (MulAction.stabilizer ((T : Subgroup K).map K.subtype) (v + b) ≤
        MulAction.stabilizer ((T : Subgroup K).map K.subtype) a) ∧
      (∀ j, MulAction.stabilizer ((P j : Subgroup K).map K.subtype) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit ((P jparent : Subgroup K).map K.subtype) (v + t jparent) c := by
  classical
  induction hdim : Module.finrank (ZMod r) V using Nat.strong_induction_on
      generalizing V jparent with
  | h n ih =>
    by_cases hcyclic : ∀ j, IsCyclic (P j)
    · have hcentral : ∀ j, (P j : Subgroup K) ≤ Subgroup.center K := by
        intro j
        let : Fact (p j).Prime := ⟨hp j⟩
        let : IsCyclic (P j) := hcyclic j
        exact sylow_le_center_of_nilpotent_of_abelian (P j) IsCyclic.isMulCommutative
      obtain ⟨v, hvT, hvP, hvOrbit⟩ :=
        exists_regular_translates_preserving_stabilizer_of_central_oddComponents
          hirr hcop.symm (T : Subgroup K) T.isPGroup' p hp hodd hinj
          (fun j ↦ (P j : Subgroup K)) (fun j ↦ (P j).isPGroup') hPne
          hcentral hsupport a b t jparent c
      refine ⟨v, hvT, hvP, ?_⟩
      rintro ⟨g, hg⟩
      apply hvOrbit
      exact MulAction.mem_orbit_iff.mpr ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
    · push Not at hcyclic
      obtain ⟨jactive, hactive⟩ := hcyclic
      obtain ⟨X⟩ := exists_oddPrimeCliffordDescent K hirr hcop
        (hp jactive) ((hp jactive).odd_of_ne_two (hodd jactive)) (P jactive) hactive
      apply X.exists_translate_of_local p hp hodd hinj P T jactive a b t ?_ jparent c
      intro i jmark cmark
      let W := X.witness
      let L := W.coordinateLocalGroup i
      have : Finite L := W.coordinateLocalGroup_finite i
      have : Group.IsNilpotent L := W.coordinateLocalGroup_nilpotent i
      have : Nontrivial W.base := Submodule.nontrivial_iff_ne_bot.mpr W.base_ne_bot
      have hlt : Module.finrank (ZMod r) W.base < n := W.base_finrank_lt.trans_eq hdim
      obtain ⟨Tl, hTl⟩ := W.coordinateLocalComponent_isSylow Nat.prime_two
        (T : Subgroup K) i (X.localSylow Nat.prime_two T i)
      have hPl : ∀ j, ∃ Q : Sylow (p j) L,
          (Q : Subgroup L) = W.coordinateLocalComponent (P j : Subgroup K) i :=
        fun j ↦ W.coordinateLocalComponent_isSylow (hp j)
          (P j : Subgroup K) i (X.localSylow (hp j) (P j) i)
      choose Pl hPl using hPl
      have hPlne : ∀ j, (Pl j : Subgroup L) ≠ ⊥ := by
        intro j
        rw [hPl j]
        exact (W.coordinateLocalComponent_ne_bot_iff (P j : Subgroup K) i).mpr
          (X.localActive (hp j) (P j) (hPne j) i)
      have hsupp : (Tl : Subgroup L) ≠ ⊥ ∨ 2 ≤ Fintype.card J := by
        rcases hsupport with hTne | hcard
        · left
          rw [hTl]
          exact (W.coordinateLocalComponent_ne_bot_iff (T : Subgroup K) i).mpr
            (X.localActive Nat.prime_two T hTne i)
        · exact Or.inr hcard
      have hrec := ih (Module.finrank (ZMod r) W.base) hlt L
        (W.coordinateLocalGroup_irreducible i) (W.coordinateLocalGroup_coprime hcop i)
        Pl hPlne Tl hsupp (W.blockCoordinates a i) (W.blockCoordinates b i)
        (fun j ↦ W.blockCoordinates (t j) i) jmark cmark rfl
      let LocalResult (U : Subgroup L) (A : J → Subgroup L) : Prop :=
        ∃ w : W.base,
          (MulAction.stabilizer (U.map L.subtype) (w + W.blockCoordinates b i) ≤
            MulAction.stabilizer (U.map L.subtype) (W.blockCoordinates a i)) ∧
          (∀ j, MulAction.stabilizer ((A j).map L.subtype)
            (w + W.blockCoordinates (t j) i) = ⊥) ∧
          ¬ SameBlockOrbit ((A jmark).map L.subtype)
            (w + W.blockCoordinates (t jmark) i) cmark
      have hresult : LocalResult (Tl : Subgroup L) (fun j ↦ (Pl j : Subgroup L)) := hrec
      rw [hTl, funext hPl] at hresult
      exact hresult

end LisiSabatini
