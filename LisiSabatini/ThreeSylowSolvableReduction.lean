import LisiSabatini.TripleAffineReductionCore
import LisiSabatini.ChiefActionCore
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Solvable three-Sylow reduction to common affine two-base translates

Every nontrivial finite solvable group has an elementary-abelian minimal
normal subgroup.  The exact three-row affine lift therefore gives an
induction on group order, provided common affine two-base translates are
available for every chief conjugation action which can occur in the
recursion.

The required linear statement is an explicit hypothesis below.  This file
does not assert it, does not add an axiom, and in particular does not claim
an unconditional three-Sylow theorem.
-/

noncomputable section

namespace LisiSabatini

universe uG uI

/-! ## Elementary-abelian coordinates for an abelian chief factor -/

/-- A finite abelian minimal normal subgroup admits a chief
elementary-abelian section.  This construction is independent of ambient
solvability. -/
theorem MinimalNormal.exists_chiefElementaryAbelianSection_of_isMulCommutative
    {G : Type uG} [Group G] [Finite G]
    {N : Subgroup G} (hN : MinimalNormal N)
    (hcomm : IsMulCommutative N) :
    ∃ C : ChiefElementaryAbelianSection G, C.N = N := by
  letI : N.Normal := hN.normal
  obtain ⟨p, hp, hpg⟩ := hN.exists_prime_isPGroup hcomm
  have hpow : ∀ x : N, x ^ p = 1 :=
    hN.pow_prime_eq_one hcomm hp hpg
  letI : IsMulCommutative N := hcomm
  letI : Fact p.Prime := ⟨hp⟩
  letI zmodModule : Module (ZMod p) (Additive N) :=
    AddCommGroup.zmodModule fun x ↦ by
      simpa using congrArg Additive.ofMul (hpow x.toMul)
  letI finiteModule : Module.Finite (ZMod p) (Additive N) :=
    Module.Finite.of_finite
  letI freeModule : Module.Free (ZMod p) (Additive N) :=
    @Module.Free.of_divisionRing (ZMod p) (Additive N)
      (inferInstance) (inferInstance) zmodModule
  let d := Module.finrank (ZMod p) (Additive N)
  let basis : Module.Basis (Fin d) (ZMod p) (Additive N) :=
    @Module.finBasis (ZMod p) (Additive N)
      (inferInstance) (inferInstance) (inferInstance)
      zmodModule freeModule finiteModule
  let coordinates : Additive N ≃+ (Fin d → ZMod p) :=
    basis.equivFun.toAddEquiv
  let S : ElementaryAbelianSection G :=
    ElementaryAbelianSection.ofCoordinates N hN.normal p d hp coordinates
  let C : ChiefElementaryAbelianSection G :=
    ChiefElementaryAbelianSection.ofSection S hN
  exact ⟨C, rfl⟩

/-- A minimal normal subgroup of a finite solvable group is abelian, hence
admits the preceding elementary-abelian chief section. -/
theorem MinimalNormal.exists_chiefElementaryAbelianSection
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    {N : Subgroup G} (hN : MinimalNormal N) :
    ∃ C : ChiefElementaryAbelianSection G, C.N = N :=
  hN.exists_chiefElementaryAbelianSection_of_isMulCommutative
    hN.isMulCommutative

/-! ## The explicit global linear hypothesis -/

/-- `CommonAffineTwoBaseTranslates` for every chief conjugation action of
every finite solvable group in the recursion universe.

Quantifying over the intermediate group is essential: quotient induction
must apply the hypothesis again to chief factors of successive quotients.
This predicate is only an assumption interface; no inhabitant is constructed
in this file. -/
def AllSolvableChiefActionsCommonAffineTwoBaseTranslates : Prop :=
  ∀ (H : Type uG) [Group H] [Finite H] [IsSolvable H],
    ∀ C : ChiefElementaryAbelianSection H,
      CommonAffineTwoBaseTranslates.{uI}
        C.r C.d C.chiefAction

/-! ## Solvable induction -/

/-- **Exact solvable reduction for three independently prescribed Sylow
rows.**

Under common affine two-base translates for all finite solvable chief
actions, every finite solvable group has mixed three-row Sylow-core
synchronization.  The proof treats the chief characteristic by exact
quotient transport and sends all cross-characteristic primes, including
`2`, through the CATB hypothesis. -/
theorem mixedThreeSylowCoreSynchronization_of_solvable_of_allChiefActionsCATB
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hCATB :
      AllSolvableChiefActionsCommonAffineTwoBaseTranslates.{uG, uI}) :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G := by
  classical
  by_cases hsubsingleton : Subsingleton G
  · letI : Subsingleton G := hsubsingleton
    exact mixedThreeSylowCoreSynchronization_of_subsingleton
  · letI : Nontrivial G :=
      not_subsingleton_iff_nontrivial.mp hsubsingleton
    obtain ⟨N, hN⟩ := exists_minimalNormal (G := G)
    letI : N.Normal := hN.normal
    obtain ⟨C, hCN⟩ := hN.exists_chiefElementaryAbelianSection
    subst N
    have hlinearChief :
        CommonAffineTwoBaseTranslates.{uI}
          C.r C.d C.chiefAction :=
      hCATB G C
    have hlinear :
        CommonAffineTwoBaseTranslates.{uI}
          C.r C.d C.elementarySection.commonAction := by
      change CommonAffineTwoBaseTranslates.{uI}
        C.r C.d C.conjugation.range
      exact hlinearChief
    exact
      C.elementarySection.mixedThreeSylowCoreSynchronization_lift_commonAffineTwoBaseTranslates
        (mixedThreeSylowCoreSynchronization_of_solvable_of_allChiefActionsCATB
          hCATB)
        hlinear
termination_by Nat.card G
decreasing_by
  rw [← C.N.index_eq_card, ← C.N.index_mul_card]
  exact lt_mul_of_one_lt_right
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (C.N.one_lt_card_iff_ne_bot.mpr C.minimal.ne_bot)

/-- Diagonal specialization of the conditional mixed theorem to the
same-row three-conjugates synchronization statement. -/
theorem threeConjugatesSylowSynchronization_of_solvable_of_allChiefActionsCATB
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hCATB :
      AllSolvableChiefActionsCommonAffineTwoBaseTranslates.{uG, uI}) :
    HasThreeConjugatesSylowSynchronization.{uG, uI} G :=
  mixedThree_to_threeConjugates
    (mixedThreeSylowCoreSynchronization_of_solvable_of_allChiefActionsCATB
      hCATB)

end LisiSabatini
