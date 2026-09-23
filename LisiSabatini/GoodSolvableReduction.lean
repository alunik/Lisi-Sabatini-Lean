module

public import LisiSabatini.ChiefFactorCore
public import LisiSabatini.CoreAttainmentAffineReduction
public import LisiSabatini.RegularNormalComponentSynchronization

/-!
# Reduction of the good solvable case to translated regularity

The elementary-abelian lift below allows all primes. The ambient group need
not be solvable: individual core attainment, the strong quotient conclusion,
and the stated linear synchronization hypothesis suffice.

The final cardinality induction assumes
`RegularNormalComponentSynchronization` explicitly. It is a reduction of the
paper's solvable theorem, not an unconditional proof of that theorem. In
particular, the linear input is not introduced as an axiom.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped IsMulCommutative

universe uG uI


namespace ElementaryAbelianSection

/-- Parity-free elementary-kernel lifting. Individual Sylow-core attainment
provides the regular-vector hypotheses for the actual normal components. -/
theorem strongLisiSabatini_lift_of_regularNormalComponentSynchronization
    {G : Type uG} [Group G] [Finite G]
    (S : ElementaryAbelianSection G) [S.N.Normal]
    (hstar : SylowCoreAttainment G)
    (hquot : StrongLisiSabatini.{uG, uI} (G ⧸ S.N))
    (hlinear : RegularNormalComponentSynchronizationOn.{uI}
      S.r (Fin S.d → ZMod S.r) S.commonAction) :
    StrongLisiSabatini.{uG, uI} G := by
  classical
  intro I _ p hp hinj P
  let Pbar : ∀ i, Sylow (p i) (G ⧸ S.N) := fun i ↦ by
    let : Fact (p i).Prime := ⟨hp i⟩
    exact (P i).mapSurjective (QuotientGroup.mk'_surjective S.N)
  obtain ⟨xbar, hxbar⟩ := hquot p hp hinj Pbar
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective S.N xbar
  have hxquot (i : I) :
      sylowInter (Pbar i) (QuotientGroup.mk' S.N x) =
        pCore (p i) (G ⧸ S.N) := by
    rw [hx]
    exact hxbar i
  let J := {i : I // p i ≠ S.r}
  let H : J → Subgroup S.commonAction := fun j ↦
    S.normalComponent (P j.1)
  let localData := fun j : J ↦ by
    let : Fact (p j.1).Prime := ⟨hp j.1⟩
    exact S.exists_translation_sylowInter_eq_pCore_iff_regular
      (P j.1) x j.2 (hxquot j.1)
  let t : J → S.N := fun j ↦ Classical.choose (localData j)
  have ht (j : J) := Classical.choose_spec (localData j)
  have himage (j : J) : pCore (p j.1) (G ⧸ S.N) ≤
      (P j.1 : Subgroup G).map (QuotientGroup.mk' S.N) := by
    let : Fact (p j.1).Prime := ⟨hp j.1⟩
    exact S.quotientCore_le_sylow_map_of_sylowInter_eq
      (P j.1) x (hxquot j.1)
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
  have hregular (j : J) : ∃ w : Fin S.d → ZMod S.r,
      MulAction.stabilizer ((H j).map S.commonAction.subtype) w = ⊥ := by
    let : Fact (p j.1).Prime := ⟨hp j.1⟩
    exact S.exists_regular_normalComponent_of_sylowCoreAttainment
      (P j.1) j.2 (hstar (p j.1) (hp j.1))
  obtain ⟨v, hv⟩ := hlinear (fun j : J ↦ p j.1) hpJ hinjJ
    (fun j ↦ j.2) H hnormal hHp hregular
    (fun j ↦ S.coordinates (Additive.ofMul (t j)))
  let n : S.N := Additive.toMul (S.coordinates.symm v)
  refine ⟨(n : G) * x, fun i ↦ ?_⟩
  by_cases hiSection : p i = S.r
  · let : Fact (p i).Prime := ⟨hp i⟩
    have hNp : IsPGroup (p i) S.N := by
      simpa [hiSection] using S.isPGroup_N
    apply sylowInter_eq_pCore_of_quotient_eq S.N hNp (P i) ((n : G) * x)
    have hmn : QuotientGroup.mk' S.N (n : G) = 1 :=
      (QuotientGroup.eq_one_iff (n : G)).mpr n.2
    simpa [map_mul, hmn] using hxquot i
  · let j : J := ⟨i, hiSection⟩
    apply (ht j n).mpr
    have hvj := hv j
    dsimp [H] at hvj
    rw [S.localImage_ambient_eq_restrictedConjugation_range (P j.1)] at hvj
    change MulAction.stabilizer
      (S.restrictedConjugation (S.quotientCoreComplement (P i))).range
      (S.coordinates (S.coordinates.symm v + Additive.ofMul (t j))) = ⊥
    rw [map_add, S.coordinates.apply_symm_apply]
    exact hvj

end ElementaryAbelianSection

/-- Conditional reduction of the paper's solvable theorem to the global
translated regularity theorem. Every normal quotient must satisfy (*). -/
theorem strongLisiSabatini_of_quotientStar_of_linearSynchronization
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hlinear : RegularNormalComponentSynchronization.{uI})
    (hstar : QuotientSylowCoreAttainment G) :
    StrongLisiSabatini.{uG, uI} G := by
  classical
  by_cases hsubsingleton : Subsingleton G
  · let : Subsingleton G := hsubsingleton
    exact strongLisiSabatini_of_subsingleton
  · let : Nontrivial G := not_subsingleton_iff_nontrivial.mp hsubsingleton
    obtain ⟨N, hN⟩ := exists_minimalNormal (G := G)
    let : N.Normal := hN.normal
    obtain ⟨C, hCN⟩ := hN.exists_chiefElementaryAbelianSection
    subst N
    let : Fact C.r.Prime := ⟨C.prime⟩
    exact C.elementarySection.strongLisiSabatini_lift_of_regularNormalComponentSynchronization
      hstar.self
      (strongLisiSabatini_of_quotientStar_of_linearSynchronization
        hlinear (hstar.quotient_closed C.N))
      (hlinear C.r C.d C.elementarySection.commonAction)
termination_by Nat.card G
decreasing_by
  rw [← C.N.index_eq_card, ← C.N.index_mul_card]
  exact lt_mul_of_one_lt_right
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (C.N.one_lt_card_iff_ne_bot.mpr C.minimal.ne_bot)

/-- Original inclusion-minimal formulation of the same conditional
solvable reduction. -/
theorem hasLisiSabatini_of_quotientStar_of_linearSynchronization
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hlinear : RegularNormalComponentSynchronization.{uI})
    (hstar : QuotientSylowCoreAttainment G) :
    HasLisiSabatini.{uG, uI} G :=
  StrongLisiSabatini.hasLisiSabatini
    (strongLisiSabatini_of_quotientStar_of_linearSynchronization
      hlinear hstar)

end LisiSabatini
