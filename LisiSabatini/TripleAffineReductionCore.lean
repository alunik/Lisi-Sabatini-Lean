import LisiSabatini.AffineTwoBaseTranslates
import LisiSabatini.MixedAffineReductionCore
import LisiSabatini.ThreeConjugatesSynchronization

/-!
# Three-row affine chief-factor reduction

This file contains the exact group-theoretic reduction needed to lift three
independently prescribed Sylow rows through an elementary-abelian normal
section.  A three-row quotient witness does not in general give either of
the corresponding two-row quotient witnesses.  Consequently the proof works
directly with the two point stabilizers which arise from the second and third
rows.

No linear existence theorem is asserted here.  The final lift takes
`CommonAffineTwoBaseTranslates` as an explicit hypothesis.
-/

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe uA uG uI uR uV

/-! ## The generic two-point action bridge -/

variable {A : Type uA} [Group A]
variable {R₀ : Type uR} [Semiring R₀]
variable {V : Type uV} [AddCommMonoid V] [Module R₀ V]

/-- The common stabilizer of two points in the source of a linear action is
the action kernel exactly when the common stabilizer in the action image is
trivial. -/
theorem actionPointStabilizer_inf_eq_ker_iff_range_stabilizer_inf_eq_bot
    (ρ : A →* LinearMap.GeneralLinearGroup R₀ V) (v w : V) :
    actionPointStabilizer ρ v ⊓ actionPointStabilizer ρ w = ρ.ker ↔
      MulAction.stabilizer ρ.range v ⊓
          MulAction.stabilizer ρ.range w =
        ⊥ := by
  constructor
  · intro hker
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp g.2
    have hav : a ∈ actionPointStabilizer ρ v := by
      rw [mem_actionPointStabilizer, ha]
      exact hg.1
    have haw : a ∈ actionPointStabilizer ρ w := by
      rw [mem_actionPointStabilizer, ha]
      exact hg.2
    have haKer : a ∈ ρ.ker := hker ▸ ⟨hav, haw⟩
    apply Subtype.ext
    exact ha.symm.trans (MonoidHom.mem_ker.mp haKer)
  · intro himage
    apply le_antisymm
    · intro a ha
      rw [MonoidHom.mem_ker]
      let g : ρ.range := ⟨ρ a, ⟨a, rfl⟩⟩
      have hg : g ∈
          MulAction.stabilizer ρ.range v ⊓
            MulAction.stabilizer ρ.range w := by
        exact ⟨ha.1, ha.2⟩
      have hgOne : g = 1 :=
        (Subgroup.eq_bot_iff_forall _).mp himage g hg
      exact congrArg Subtype.val hgOne
    · exact le_inf
        (action_ker_le_pointStabilizer ρ v)
        (action_ker_le_pointStabilizer ρ w)

variable {G : Type uG} [Group G]

namespace ElementaryAbelianSection

/-- Mapping the two source point stabilizers into the ambient group gives
exactly the intersection of a complement with its two translates. -/
theorem map_inf_actionPointStabilizers_eq_triple_inf_conjugates
    (S : ElementaryAbelianSection G) (A₀ : Subgroup G)
    (hAN : Disjoint A₀ S.N) (n m : S.N) :
    (actionPointStabilizer (S.restrictedConjugation A₀)
          (S.coordinates (Additive.ofMul n)) ⊓
        actionPointStabilizer (S.restrictedConjugation A₀)
          (S.coordinates (Additive.ofMul m))).map A₀.subtype =
      (A₀ ⊓ (MulAut.conj (n : G) • A₀)) ⊓
        (MulAut.conj (m : G) • A₀) := by
  ext g
  constructor
  · rintro ⟨a, ha, rfl⟩
    have han :
        (a : G) ∈ MulAut.conj (n : G) • A₀ := by
      have han' :
          a ∈ (MulAut.conj (n : G) • A₀).comap A₀.subtype := by
        rw [S.conjugate_complement_comap_eq_actionPointStabilizer
          A₀ hAN n]
        exact ha.1
      exact han'
    have ham :
        (a : G) ∈ MulAut.conj (m : G) • A₀ := by
      have ham' :
          a ∈ (MulAut.conj (m : G) • A₀).comap A₀.subtype := by
        rw [S.conjugate_complement_comap_eq_actionPointStabilizer
          A₀ hAN m]
        exact ha.2
      exact ham'
    exact ⟨⟨a.2, han⟩, ham⟩
  · rintro ⟨⟨hgA, hgn⟩, hgm⟩
    let a : A₀ := ⟨g, hgA⟩
    refine ⟨a, ?_, rfl⟩
    constructor
    · rw [← S.conjugate_complement_comap_eq_actionPointStabilizer
        A₀ hAN n]
      exact hgn
    · rw [← S.conjugate_complement_comap_eq_actionPointStabilizer
        A₀ hAN m]
      exact hgm

/-- Generic affine two-point bridge.  Equality of the three complement
intersection with the ambient copy of the action kernel is equivalent to
trivial common stabilizer in the faithful action image. -/
theorem triple_inf_conjugates_eq_map_ker_iff_range_stabilizers_inf_eq_bot
    (S : ElementaryAbelianSection G) (A₀ : Subgroup G)
    (hAN : Disjoint A₀ S.N) (n m : S.N) :
    (A₀ ⊓ (MulAut.conj (n : G) • A₀)) ⊓
          (MulAut.conj (m : G) • A₀) =
        (S.restrictedConjugation A₀).ker.map A₀.subtype ↔
      MulAction.stabilizer (S.restrictedConjugation A₀).range
            (S.coordinates (Additive.ofMul n)) ⊓
          MulAction.stabilizer (S.restrictedConjugation A₀).range
            (S.coordinates (Additive.ofMul m)) =
        ⊥ := by
  let ρ := S.restrictedConjugation A₀
  let v := S.coordinates (Additive.ofMul n)
  let w := S.coordinates (Additive.ofMul m)
  have hmap :
      (actionPointStabilizer ρ v ⊓
          actionPointStabilizer ρ w).map A₀.subtype =
        (A₀ ⊓ (MulAut.conj (n : G) • A₀)) ⊓
          (MulAut.conj (m : G) • A₀) :=
    S.map_inf_actionPointStabilizers_eq_triple_inf_conjugates
      A₀ hAN n m
  constructor
  · intro h
    apply
      (actionPointStabilizer_inf_eq_ker_iff_range_stabilizer_inf_eq_bot
        ρ v w).mp
    exact Subgroup.map_subtype_inj.mp (hmap.trans h)
  · intro h
    have hsource :
        actionPointStabilizer ρ v ⊓ actionPointStabilizer ρ w = ρ.ker :=
      (actionPointStabilizer_inf_eq_ker_iff_range_stabilizer_inf_eq_bot
        ρ v w).mpr h
    exact hmap.symm.trans
      (congrArg (fun K : Subgroup A₀ ↦ K.map A₀.subtype) hsource)

/-- Version of the generic bridge after the action kernel has been
identified with the ambient `p`-core. -/
theorem triple_inf_conjugates_eq_pCore_iff_range_stabilizers_inf_eq_bot
    {p : ℕ} (S : ElementaryAbelianSection G) (A₀ : Subgroup G)
    (hAN : Disjoint A₀ S.N) (n m : S.N)
    (hcore :
      pCore p G = (S.restrictedConjugation A₀).ker.map A₀.subtype) :
    (A₀ ⊓ (MulAut.conj (n : G) • A₀)) ⊓
          (MulAut.conj (m : G) • A₀) =
        pCore p G ↔
      MulAction.stabilizer (S.restrictedConjugation A₀).range
            (S.coordinates (Additive.ofMul n)) ⊓
          MulAction.stabilizer (S.restrictedConjugation A₀).range
            (S.coordinates (Additive.ofMul m)) =
        ⊥ := by
  rw [hcore]
  exact
    S.triple_inf_conjugates_eq_map_ker_iff_range_stabilizers_inf_eq_bot
      A₀ hAN n m

end ElementaryAbelianSection

/-! ## Exact triple quotient transport -/

/-- A quotient map preserves a mixed three-row intersection exactly when
its kernel lies in all three rows. -/
theorem mixedSylowTripleInter_map_quotient_mk'
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q R : Sylow p G) (x y : G)
    (hNP : N ≤ (P : Subgroup G))
    (hNQx : N ≤ ((x • Q : Sylow p G) : Subgroup G))
    (hNRy : N ≤ ((y • R : Sylow p G) : Subgroup G)) :
    (mixedSylowTripleInter P Q R x y).map (QuotientGroup.mk' N) =
      mixedSylowTripleInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective N))
        (R.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  rw [mixedSylowTripleInter, mixedSylowTripleInter,
    map_inf_quotient_mk' N _ _ (le_inf hNP hNQx) hNRy,
    map_inf_quotient_mk' N _ _ hNP hNQx,
    map_sylow_smul_quotient N Q x,
    map_sylow_smul_quotient N R y]
  rfl

/-- Pulling back the corresponding quotient triple recovers the original
mixed intersection when the kernel lies in all three rows. -/
theorem mixedSylowTripleInter_comap_quotient_mk'
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q R : Sylow p G) (x y : G)
    (hNP : N ≤ (P : Subgroup G))
    (hNQx : N ≤ ((x • Q : Sylow p G) : Subgroup G))
    (hNRy : N ≤ ((y • R : Sylow p G) : Subgroup G)) :
    (mixedSylowTripleInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective N))
        (R.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) (QuotientGroup.mk' N y)).comap
          (QuotientGroup.mk' N) =
      mixedSylowTripleInter P Q R x y := by
  rw [← mixedSylowTripleInter_map_quotient_mk'
    N P Q R x y hNP hNQx hNRy]
  exact Subgroup.comap_map_eq_self <| by
    rw [QuotientGroup.ker_mk']
    exact le_inf (le_inf hNP hNQx) hNRy

/-- At the characteristic prime of a normal section, an exact quotient
three-row equality lifts directly to the ambient `p`-core. -/
theorem mixedSylowTripleInter_eq_pCore_of_quotient_eq
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (hNp : IsPGroup p N)
    (P Q R : Sylow p G) (x y : G)
    (hquot :
      mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective N))
          (R.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) =
        pCore p (G ⧸ N)) :
    mixedSylowTripleInter P Q R x y = pCore p G := by
  have hNP : N ≤ (P : Subgroup G) :=
    normalPSubgroup_le_sylow hNp inferInstance P
  have hNQx : N ≤ ((x • Q : Sylow p G) : Subgroup G) :=
    normalPSubgroup_le_sylow hNp inferInstance (x • Q)
  have hNRy : N ≤ ((y • R : Sylow p G) : Subgroup G) :=
    normalPSubgroup_le_sylow hNp inferInstance (y • R)
  calc
    mixedSylowTripleInter P Q R x y =
        (mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective N))
          (R.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x) (QuotientGroup.mk' N y)).comap
            (QuotientGroup.mk' N) :=
      (mixedSylowTripleInter_comap_quotient_mk'
        N P Q R x y hNP hNQx hNRy).symm
    _ = (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) := by rw [hquot]
    _ = pCore p G := pCore_comap_quotient_mk' N hNp

/-- Exact quotient-fibre invariance for two independently shifted
conjugators. -/
theorem mixedSylowTripleInter_quotient_left_mul
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q R : Sylow p G)
    (x y n m : G) (hn : n ∈ N) (hm : m ∈ N) :
    mixedSylowTripleInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective N))
        (R.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N (n * x))
        (QuotientGroup.mk' N (m * y)) =
      mixedSylowTripleInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective N))
        (R.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) := by
  have hmn : QuotientGroup.mk' N n = 1 :=
    (QuotientGroup.eq_one_iff n).mpr hn
  have hmm : QuotientGroup.mk' N m = 1 :=
    (QuotientGroup.eq_one_iff m).mpr hm
  simp only [map_mul, hmn, hmm, one_mul]

/-- A three-row quotient-core equality forces every pair of lifts in its two
fibres to have ambient triple intersection inside the pullback of that
quotient core. -/
theorem mixedSylowTripleInter_le_comap_quotient_pCore_of_quotient_eq
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q R : Sylow p G) (x y : G)
    (hquot :
      mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective N))
          (R.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) =
        pCore p (G ⧸ N))
    {n m : G} (hn : n ∈ N) (hm : m ∈ N) :
    mixedSylowTripleInter P Q R (n * x) (m * y) ≤
      (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  intro g hg
  change QuotientGroup.mk' N g ∈ pCore p (G ⧸ N)
  rw [← hquot]
  have hgP :
      QuotientGroup.mk' N g ∈
        (P.mapSurjective (QuotientGroup.mk'_surjective N) :
          Subgroup (G ⧸ N)) :=
    ⟨g, hg.1.1, rfl⟩
  have hgQshift :
      QuotientGroup.mk' N g ∈
        (((QuotientGroup.mk' N (n * x)) •
          Q.mapSurjective (QuotientGroup.mk'_surjective N) :
            Sylow p (G ⧸ N)) : Subgroup (G ⧸ N)) := by
    rw [← map_sylow_smul_quotient N Q (n * x)]
    exact ⟨g, hg.1.2, rfl⟩
  have hgRshift :
      QuotientGroup.mk' N g ∈
        (((QuotientGroup.mk' N (m * y)) •
          R.mapSurjective (QuotientGroup.mk'_surjective N) :
            Sylow p (G ⧸ N)) : Subgroup (G ⧸ N)) := by
    rw [← map_sylow_smul_quotient N R (m * y)]
    exact ⟨g, hg.2, rfl⟩
  have hmn : QuotientGroup.mk' N n = 1 :=
    (QuotientGroup.eq_one_iff n).mpr hn
  have hmm : QuotientGroup.mk' N m = 1 :=
    (QuotientGroup.eq_one_iff m).mpr hm
  exact ⟨⟨hgP, by simpa [map_mul, hmn] using hgQshift⟩,
    by simpa [map_mul, hmm] using hgRshift⟩

/-! ## Complement sections and the exact affine fibre model -/

/-- Any two Sylow sections over the same quotient `p`-core are conjugate by
an element of the quotient kernel.  Unlike the two-row predecessor, this
form assumes the two image containments separately and therefore applies to
a genuine three-row quotient witness. -/
theorem exists_kernel_conjugator_quotientCore_sections_of_le_maps
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (hNr : IsPGroup r N) (hpr : p ≠ r)
    (P Q : Sylow p G)
    (himageP : pCore p (G ⧸ N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' N))
    (himageQ : pCore p (G ⧸ N) ≤
      (Q : Subgroup G).map (QuotientGroup.mk' N)) :
    ∃ t ∈ N,
      ((Q : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) =
        MulAut.conj t •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) := by
  let L := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)
  let A₀ : Subgroup G := (P : Subgroup G) ⊓ L
  let B₀ : Subgroup G := (Q : Subgroup G) ⊓ L
  let PA : Sylow p L :=
    quotientCoreSectionSylow N hNr hpr P himageP
  let PB : Sylow p L :=
    quotientCoreSectionSylow N hNr hpr Q himageQ
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L PA PB
  have hlsub : MulAut.conj l • (PA : Subgroup L) = (PB : Subgroup L) := by
    change (((l • PA : Sylow p L) : Subgroup L)) = (PB : Subgroup L)
    exact congrArg (fun T : Sylow p L ↦ (T : Subgroup L)) hl
  have hlsections :
      MulAut.conj l • A₀.subgroupOf L = B₀.subgroupOf L := by
    simpa [PA, PB, A₀, B₀, L] using hlsub
  have hlambient : MulAut.conj (l : G) • A₀ = B₀ := by
    have hmap :=
      congrArg (fun K : Subgroup L ↦ K.map L.subtype) hlsections
    simpa [map_conj_smul, Subgroup.map_subgroupOf_eq_of_le,
      A₀, B₀, L] using hmap
  obtain ⟨a, haP, haeq⟩ := himageP l.2
  have haL : a ∈ L := by
    change QuotientGroup.mk' N a ∈ pCore p (G ⧸ N)
    rw [haeq]
    exact l.2
  have haA : a ∈ A₀ := ⟨haP, haL⟩
  let t : G := (l : G) * a⁻¹
  have htN : t ∈ N := by
    apply (QuotientGroup.eq_one_iff t).mp
    change QuotientGroup.mk' N ((l : G) * a⁻¹) = 1
    rw [map_mul, map_inv, haeq, mul_inv_cancel]
  refine ⟨t, htN, ?_⟩
  change B₀ = MulAut.conj t • A₀
  calc
    B₀ = MulAut.conj (l : G) • A₀ := hlambient.symm
    _ = MulAut.conj (t * a) • A₀ := by
      congr 2
      simp [t]
    _ = MulAut.conj t • (MulAut.conj a • A₀) := by
      rw [← mul_smul, map_mul]
    _ = MulAut.conj t • A₀ := by
      rw [Subgroup.conj_smul_eq_self_of_mem haA]

/-- If a triple intersection is already contained in a normal subgroup,
all three factors can be cut down to that subgroup. -/
theorem triple_inf_conj_smul_eq_sections_of_le
    (P₀ B₀ C₀ L : Subgroup G) (hL : L.Normal) (n m : G)
    (hle :
      (P₀ ⊓ (MulAut.conj n • B₀)) ⊓
          (MulAut.conj m • C₀) ≤
        L) :
    (P₀ ⊓ (MulAut.conj n • B₀)) ⊓
          (MulAut.conj m • C₀) =
      ((P₀ ⊓ L) ⊓ (MulAut.conj n • (B₀ ⊓ L))) ⊓
        (MulAut.conj m • (C₀ ⊓ L)) := by
  letI : L.Normal := hL
  ext g
  constructor
  · intro hg
    have hgL : g ∈ L := hle hg
    refine ⟨⟨⟨hg.1.1, hgL⟩, ?_⟩, ?_⟩
    · rw [Subgroup.smul_inf, Subgroup.Normal.conj_smul_eq_self n L]
      exact ⟨hg.1.2, hgL⟩
    · rw [Subgroup.smul_inf, Subgroup.Normal.conj_smul_eq_self m L]
      exact ⟨hg.2, hgL⟩
  · intro hg
    have hgn := hg.1.2
    have hgm := hg.2
    rw [Subgroup.smul_inf, Subgroup.Normal.conj_smul_eq_self n L] at hgn
    rw [Subgroup.smul_inf, Subgroup.Normal.conj_smul_eq_self m L] at hgm
    exact ⟨⟨hg.1.1.1, hgn.1⟩, hgm.1⟩

/-- Exact group-theoretic fibre model for independently prescribed second
and third Sylow rows. -/
theorem mixedSylowTripleInter_left_mul_eq_complement_two_translates
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q R : Sylow p G) (x y : G)
    (hquot :
      mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective N))
          (R.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x) (QuotientGroup.mk' N y) =
        pCore p (G ⧸ N))
    (t u : G)
    (hconjQ :
      (((x • Q : Sylow p G) : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) =
        MulAut.conj t •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)))
    (hconjR :
      (((y • R : Sylow p G) : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) =
        MulAut.conj u •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)))
    {n m : G} (hn : n ∈ N) (hm : m ∈ N) :
    mixedSylowTripleInter P Q R (n * x) (m * y) =
      (((P : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) ⊓
        (MulAut.conj (n * t) •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)))) ⊓
        (MulAut.conj (m * u) •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N))) := by
  let L := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)
  have hL : L.Normal := inferInstance
  have hraw :
      ((P : Subgroup G) ⊓
          (MulAut.conj n • (((x • Q : Sylow p G) : Subgroup G)))) ⊓
          (MulAut.conj m • (((y • R : Sylow p G) : Subgroup G))) ≤
        L := by
    intro g hg
    apply mixedSylowTripleInter_le_comap_quotient_pCore_of_quotient_eq
      N P Q R x y hquot hn hm
    simpa [mixedSylowTripleInter, mul_smul,
      Sylow.coe_subgroup_smul] using hg
  calc
    mixedSylowTripleInter P Q R (n * x) (m * y) =
        ((P : Subgroup G) ⊓
          (MulAut.conj n • (((x • Q : Sylow p G) : Subgroup G)))) ⊓
          (MulAut.conj m • (((y • R : Sylow p G) : Subgroup G))) := by
      simp [mixedSylowTripleInter, mul_smul, Sylow.coe_subgroup_smul]
    _ = ((((P : Subgroup G) ⊓ L) ⊓
          (MulAut.conj n •
            ((((x • Q : Sylow p G) : Subgroup G)) ⊓ L))) ⊓
          (MulAut.conj m •
            ((((y • R : Sylow p G) : Subgroup G)) ⊓ L))) :=
      triple_inf_conj_smul_eq_sections_of_le _ _ _ L hL n m hraw
    _ = ((((P : Subgroup G) ⊓ L) ⊓
          (MulAut.conj n •
            (MulAut.conj t • ((P : Subgroup G) ⊓ L)))) ⊓
          (MulAut.conj m •
            (MulAut.conj u • ((P : Subgroup G) ⊓ L)))) := by
      rw [hconjQ, hconjR]
    _ = ((((P : Subgroup G) ⊓ L) ⊓
          (MulAut.conj (n * t) • ((P : Subgroup G) ⊓ L))) ⊓
          (MulAut.conj (m * u) • ((P : Subgroup G) ⊓ L))) := by
      rw [← mul_smul, map_mul, ← mul_smul, map_mul]

namespace ElementaryAbelianSection

/-- An exact quotient triple contains the quotient core in the image of the
first prescribed Sylow row. -/
theorem quotientCore_le_first_sylow_map_of_mixedSylowTripleInter_eq
    (S : ElementaryAbelianSection G) [S.N.Normal] [Finite G]
    {p : ℕ} [Fact p.Prime] (P Q R : Sylow p G) (x y : G)
    (hquot :
      mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (R.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N x) (QuotientGroup.mk' S.N y) =
        pCore p (G ⧸ S.N)) :
    pCore p (G ⧸ S.N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' S.N) := by
  intro z hz
  have hz' : z ∈
      mixedSylowTripleInter
        (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
        (R.mapSurjective (QuotientGroup.mk'_surjective S.N))
        (QuotientGroup.mk' S.N x) (QuotientGroup.mk' S.N y) := by
    rw [hquot]
    exact hz
  exact hz'.1.1

/-- Exact cross-characteristic affine fibre reduction for three
independently prescribed rows.  The quotient witness supplies two fixed
translations, and every pair of fibre shifts is then equivalent to a
translated two-base condition in the common local action. -/
theorem exists_translations_mixedSylowTripleInter_eq_pCore_iff_twoBase
    {p : ℕ} [Fact p.Prime] [Finite G]
    (S : ElementaryAbelianSection G) [S.N.Normal]
    (P Q R : Sylow p G) (x y : G) (hpr : p ≠ S.r)
    (hquot :
      mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (R.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N x) (QuotientGroup.mk' S.N y) =
        pCore p (G ⧸ S.N)) :
    ∃ t u : S.N, ∀ n m : S.N,
      mixedSylowTripleInter P Q R
          ((n : G) * x) ((m : G) * y) =
          pCore p G ↔
        MulAction.stabilizer
              (S.restrictedConjugation
                ((P : Subgroup G) ⊓
                  (pCore p (G ⧸ S.N)).comap
                    (QuotientGroup.mk' S.N))).range
              (S.coordinates (Additive.ofMul (n * t))) ⊓
            MulAction.stabilizer
              (S.restrictedConjugation
                ((P : Subgroup G) ⊓
                  (pCore p (G ⧸ S.N)).comap
                    (QuotientGroup.mk' S.N))).range
              (S.coordinates (Additive.ofMul (m * u))) =
          ⊥ := by
  letI : Fact S.r.Prime := ⟨S.prime⟩
  let L := (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N)
  let A₀ : Subgroup G := (P : Subgroup G) ⊓ L
  have himageP : pCore p (G ⧸ S.N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' S.N) :=
    S.quotientCore_le_first_sylow_map_of_mixedSylowTripleInter_eq
      P Q R x y hquot
  have himageQ : pCore p (G ⧸ S.N) ≤
      (((x • Q : Sylow p G) : Subgroup G).map
        (QuotientGroup.mk' S.N)) := by
    intro z hz
    have hz' : z ∈
        mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (R.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N x) (QuotientGroup.mk' S.N y) := by
      rw [hquot]
      exact hz
    rw [map_sylow_smul_quotient S.N Q x]
    exact hz'.1.2
  have himageR : pCore p (G ⧸ S.N) ≤
      (((y • R : Sylow p G) : Subgroup G).map
        (QuotientGroup.mk' S.N)) := by
    intro z hz
    have hz' : z ∈
        mixedSylowTripleInter
          (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (R.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N x) (QuotientGroup.mk' S.N y) := by
      rw [hquot]
      exact hz
    rw [map_sylow_smul_quotient S.N R y]
    exact hz'.2
  obtain ⟨t, htN, ht⟩ :=
    exists_kernel_conjugator_quotientCore_sections_of_le_maps
      S.N S.isPGroup_N hpr P (x • Q) himageP himageQ
  obtain ⟨u, huN, hu⟩ :=
    exists_kernel_conjugator_quotientCore_sections_of_le_maps
      S.N S.isPGroup_N hpr P (y • R) himageP himageR
  let tN : S.N := ⟨t, htN⟩
  let uN : S.N := ⟨u, huN⟩
  have hcore :
      pCore p G =
        (S.restrictedConjugation A₀).ker.map A₀.subtype :=
    S.pCore_eq_map_restrictedConjugation_ker_quotientCore
      P hpr himageP
  have hAN : Disjoint A₀ S.N :=
    pSubgroups_disjoint_of_ne hpr
      P.isPGroup'.to_inf_left S.isPGroup_N
  refine ⟨tN, uN, fun n m ↦ ?_⟩
  rw [mixedSylowTripleInter_left_mul_eq_complement_two_translates
    S.N P Q R x y hquot t u ht hu n.2 m.2]
  exact S.triple_inf_conjugates_eq_pCore_iff_range_stabilizers_inf_eq_bot
    (p := p) A₀ hAN (n * tN) (m * uN) hcore

/-- Elementary-abelian three-row lift from the explicitly supplied common
affine two-base statement.  Every cross-characteristic prime, including
`2`, is sent through `CommonAffineTwoBaseTranslates`; only the section
characteristic is handled by the direct quotient-core identity. -/
theorem mixedThreeSylowCoreSynchronization_lift_commonAffineTwoBaseTranslates
    (S : ElementaryAbelianSection G) [S.N.Normal] [Finite G]
    (hquot :
      HasMixedThreeSylowCoreSynchronization.{uG, uI} (G ⧸ S.N))
    (hCATB : CommonAffineTwoBaseTranslates.{uI}
      S.r S.d S.commonAction) :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G := by
  intro I _ p hp hinj P Q R
  let Pbar : ∀ i, Sylow (p i) (G ⧸ S.N) := fun i ↦ by
    letI : Fact (p i).Prime := ⟨hp i⟩
    exact (P i).mapSurjective (QuotientGroup.mk'_surjective S.N)
  let Qbar : ∀ i, Sylow (p i) (G ⧸ S.N) := fun i ↦ by
    letI : Fact (p i).Prime := ⟨hp i⟩
    exact (Q i).mapSurjective (QuotientGroup.mk'_surjective S.N)
  let Rbar : ∀ i, Sylow (p i) (G ⧸ S.N) := fun i ↦ by
    letI : Fact (p i).Prime := ⟨hp i⟩
    exact (R i).mapSurjective (QuotientGroup.mk'_surjective S.N)
  obtain ⟨xbar, ybar, hxybar⟩ := hquot p hp hinj Pbar Qbar Rbar
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective S.N xbar
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective S.N ybar
  have hxyquot (i : I) :
      mixedSylowTripleInter (Pbar i) (Qbar i) (Rbar i)
          (QuotientGroup.mk' S.N x) (QuotientGroup.mk' S.N y) =
        pCore (p i) (G ⧸ S.N) := by
    rw [hx, hy]
    exact hxybar i
  let J := {i : I // p i ≠ S.r}
  let H : J → Subgroup S.commonAction := fun j ↦
    S.normalComponent (P j.1)
  let localData := fun j : J ↦ by
    letI : Fact (p j.1).Prime := ⟨hp j.1⟩
    exact
      S.exists_translations_mixedSylowTripleInter_eq_pCore_iff_twoBase
        (P j.1) (Q j.1) (R j.1) x y j.2 (hxyquot j.1)
  choose t u htu using localData
  have himage (j : J) : pCore (p j.1) (G ⧸ S.N) ≤
      (P j.1 : Subgroup G).map (QuotientGroup.mk' S.N) := by
    letI : Fact (p j.1).Prime := ⟨hp j.1⟩
    exact
      S.quotientCore_le_first_sylow_map_of_mixedSylowTripleInter_eq
        (P j.1) (Q j.1) (R j.1) x y (hxyquot j.1)
  have hpJ (j : J) : Nat.Prime (p j.1) := hp j.1
  have hinjJ : Function.Injective (fun j : J ↦ p j.1) := by
    intro i j hij
    apply Subtype.ext
    exact hinj hij
  have hnormal (j : J) : (H j).Normal := by
    dsimp [H]
    exact S.localImage_normal (P j.1) (himage j)
  have hHp (j : J) : IsPGroup (p j.1) (H j) := by
    dsimp [H]
    exact S.localImage_isPGroup (P j.1)
  obtain ⟨v, w, hvw⟩ := hCATB (fun j : J ↦ p j.1) hpJ hinjJ
    (fun j ↦ j.2) H hnormal hHp
    (fun j ↦ S.coordinates (Additive.ofMul (t j)))
    (fun j ↦ S.coordinates (Additive.ofMul (u j)))
  let n : S.N := Additive.toMul (S.coordinates.symm v)
  let m : S.N := Additive.toMul (S.coordinates.symm w)
  refine ⟨(n : G) * x, (m : G) * y, fun i ↦ ?_⟩
  by_cases hiSection : p i = S.r
  · letI : Fact (p i).Prime := ⟨hp i⟩
    have hNp : IsPGroup (p i) S.N := by
      simpa [hiSection] using S.isPGroup_N
    apply mixedSylowTripleInter_eq_pCore_of_quotient_eq
      S.N hNp (P i) (Q i) (R i) ((n : G) * x) ((m : G) * y)
    exact (mixedSylowTripleInter_quotient_left_mul
      S.N (P i) (Q i) (R i) x y n m n.2 m.2).trans (hxyquot i)
  · let j : {i : I // p i ≠ S.r} := ⟨i, hiSection⟩
    apply (htu j n m).mpr
    have hvwj := hvw j
    dsimp [H] at hvwj
    rw [S.localImage_ambient_eq_restrictedConjugation_range
      (P j.1)] at hvwj
    simpa [n, m, quotientCoreComplement,
      quotientCorePullback] using hvwj

end ElementaryAbelianSection

end LisiSabatini
