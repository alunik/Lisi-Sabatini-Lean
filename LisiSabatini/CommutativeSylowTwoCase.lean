module

public import LisiSabatini.QuasiprimitiveAffineTwoOrbitAssembly

/-!
# The solvable case with commutative Sylow two-subgroups

The difficult affine leaf in the solvable mixed three-row theorem is an
odd-characteristic quasiprimitive action with noncommuting mapped `O₂`.
This file records a natural unconditional family in which that leaf cannot
occur.

Commutativity of Sylow `2`-subgroups is inherited by subgroups and
surjective images.  It therefore descends through every block-stabilizer
local action in the dimension recursion and through every quotient in the
solvable chief-factor induction.  At each quasiprimitive leaf the `2`-core
is contained in a commutative Sylow subgroup, so the already proved
commuting-`2`-core theorem applies.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open CharacteristicTwoTwoOrbitReserve

universe uG uH uI

/-- Every Sylow `p`-subgroup of `G` is commutative. -/
def HasCommutativeSylowSubgroups
    (p : ℕ) (G : Type uG) [Group G] : Prop :=
  ∀ P : Sylow p G, IsMulCommutative P

namespace HasCommutativeSylowSubgroups

variable {p : ℕ}
variable {G : Type uG} [Group G]
variable {H : Type uH} [Group H]

/-- Every `p`-subgroup lies in a Sylow subgroup and is therefore
commutative. -/
theorem isMulCommutative_of_isPGroup
    (hG : HasCommutativeSylowSubgroups p G)
    (A : Subgroup G) (hAp : IsPGroup p A) :
    IsMulCommutative A := by
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  letI : IsMulCommutative P := hG P
  exact
    ⟨⟨by
      intro a b
      apply Subtype.ext
      have hab :=
        mul_comm
          (⟨a.1, hAP a.2⟩ : P)
          (⟨b.1, hAP b.2⟩ : P)
      exact congrArg (fun x : P ↦ (x : G)) hab⟩⟩

/-- The property is inherited by subgroups. -/
theorem subgroup
    (hG : HasCommutativeSylowSubgroups p G)
    (K : Subgroup G) :
    HasCommutativeSylowSubgroups p K := by
  intro P
  have hImageP :
      IsPGroup p (P.map K.subtype) :=
    P.isPGroup'.map K.subtype
  letI : IsMulCommutative (P.map K.subtype) :=
    hG.isMulCommutative_of_isPGroup (P.map K.subtype) hImageP
  exact
    ⟨⟨by
      intro a b
      apply Subtype.ext
      apply Subtype.ext
      have hab :=
        mul_comm
          (⟨a.1.1, ⟨a, a.2, rfl⟩⟩ : P.map K.subtype)
          (⟨b.1.1, ⟨b, b.2, rfl⟩⟩ : P.map K.subtype)
      exact congrArg (fun x : P.map K.subtype ↦ (x : G)) hab⟩⟩

/-- The property is inherited by a surjective group homomorphism. -/
theorem map_surjective
    [Finite G] [Fact p.Prime]
    (hG : HasCommutativeSylowSubgroups p G)
    (f : G →* H) (hf : Function.Surjective f) :
    HasCommutativeSylowSubgroups p H := by
  intro P
  obtain ⟨Q, hQP⟩ :=
    Sylow.mapSurjective_surjective hf p P
  letI : IsMulCommutative Q := hG Q
  have hmap : IsMulCommutative (Q.map f) :=
    Subgroup.map_isMulCommutative Q f
  rw [← hQP]
  exact hmap

/-- In particular, the `p`-core is commutative. -/
theorem pCore_isMulCommutative
    (hG : HasCommutativeSylowSubgroups p G) :
    IsMulCommutative (LisiSabatini.pCore p G) :=
  hG.isMulCommutative_of_isPGroup
    (LisiSabatini.pCore p G) (pCore_isPGroup p G)

/-- Form convenient for the quasiprimitive affine leaf. -/
theorem isCommutingPrimeCore
    {r d : ℕ}
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hK : HasCommutativeSylowSubgroups p K) :
    IsCommutingPrimeCore p K := by
  letI : IsMulCommutative (LisiSabatini.pCore p K) :=
    hK.pCore_isMulCommutative
  intro a b
  exact mul_comm a b

end HasCommutativeSylowSubgroups

/-! ## Heredity through one imprimitive layer -/

namespace PrimeFieldPrimitiveInternalImprimitivityPresentation

variable {r b e : ℕ} {V : Type*}
variable [AddCommGroup V] [Module (ZMod r) V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}

/-- Commutativity of Sylow `2`-subgroups descends to every faithful
block-stabilizer local image. -/
theorem blockStabilizerLocalAction_hasCommutativeSylowTwo
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K)
    (hK : HasCommutativeSylowSubgroups 2 K)
    (i : Fin b) :
    HasCommutativeSylowSubgroups 2
      (P.blockStabilizerLocalAction i) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Finite K := P.finite_action
  have hStabilizer :
      HasCommutativeSylowSubgroups 2
        (P.system.blockStabilizer i) :=
    hK.subgroup (P.system.blockStabilizer i)
  have hImage :
      HasCommutativeSylowSubgroups 2
        (P.system.blockStabilizerLocalImage i) :=
    hStabilizer.map_surjective
      (P.system.blockStabilizerLocalRangeHom i)
      (P.system.blockStabilizerLocalRangeHom_surjective i)
  letI : Finite (P.system.blockStabilizerLocalImage i) :=
    P.system.blockStabilizerLocalImage_finite i
  exact
    hImage.map_surjective
      (P.system.blockStabilizerLocalImageCoordinateEquiv i
        (P.localCoordinates i)).toMonoidHom
      (P.system.blockStabilizerLocalImageCoordinateEquiv i
        (P.localCoordinates i)).surjective

end PrimeFieldPrimitiveInternalImprimitivityPresentation

/-! ## Dimension recursion with the hereditary Sylow hypothesis -/

/-- Every irreducible prime-field action whose Sylow `2`-subgroups are
commutative satisfies the recursively stable diagonal two-orbit
invariant. -/
theorem
    commonDiagonalAffineTwoOrbitAvoidingTranslates_of_irreducible_of_commutativeSylowTwo
    {r d : ℕ} [Fact r.Prime]
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hirr : IsIrreducibleLinearAction r d K)
    (hd : 0 < d)
    (hK : HasCommutativeSylowSubgroups 2 K) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
      r (Fin d → ZMod r) K := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      rcases
          quasiprimitiveLinearAction_or_strictInternalImprimitivityPresentation
            r d K hirr with hqp | hS
      · by_cases hrTwo : r = 2
        · subst r
          exact
            commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_quasiprimitive_of_charTwo
              hd hqp
        · exact
            commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_oddChar_of_commutingTwoCore
              hrTwo hd hqp hK.isCommutingPrimeCore
      · obtain ⟨S⟩ := hS
        exact
          S.presentation
            |>.commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_children
              (fun i ↦
                ih S.localDimension S.localDimension_lt
                  (S.presentation.blockStabilizerLocalAction_irreducible i)
                  S.presentation.localDimension_pos
                  (S.presentation
                    |>.blockStabilizerLocalAction_hasCommutativeSylowTwo
                      hK i))

/-! ## Solvable chief-factor induction -/

/-- The chief conjugation image inherits commutative Sylow
`2`-subgroups from the ambient group. -/
theorem ChiefElementaryAbelianSection.chiefAction_hasCommutativeSylowTwo
    {G : Type uG} [Group G] [Finite G]
    (C : ChiefElementaryAbelianSection G)
    (hG : HasCommutativeSylowSubgroups 2 G) :
    HasCommutativeSylowSubgroups 2 C.chiefAction := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change HasCommutativeSylowSubgroups 2 C.conjugation.range
  exact
    hG.map_surjective C.conjugation.rangeRestrict
      C.conjugation.rangeRestrict_surjective

/-- **Mixed three-row synchronization for solvable groups with
commutative Sylow `2`-subgroups.**

This includes even-order groups and is independent of the Hall--Berger
classification used by the unrestricted solvable theorem. -/
theorem
    mixedThreeSylowCoreSynchronization_of_solvable_of_commutativeSylowTwo
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hG : HasCommutativeSylowSubgroups 2 G) :
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
    letI : Fact C.r.Prime := ⟨C.prime⟩
    have hlinearChief :
        CommonAffineTwoBaseTranslates.{uI}
          C.r C.d C.chiefAction :=
      CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.commonAffineTwoBaseTranslatesOn
        (commonDiagonalAffineTwoOrbitAvoidingTranslates_of_irreducible_of_commutativeSylowTwo
          C.chiefAction_isIrreducibleLinearAction
          C.dimension_pos
          (C.chiefAction_hasCommutativeSylowTwo hG))
    have hlinear :
        CommonAffineTwoBaseTranslates.{uI}
          C.r C.d C.elementarySection.commonAction := by
      change CommonAffineTwoBaseTranslates.{uI}
        C.r C.d C.conjugation.range
      exact hlinearChief
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hquotient :
        HasCommutativeSylowSubgroups 2 (G ⧸ C.N) :=
      hG.map_surjective (QuotientGroup.mk' C.N)
        (QuotientGroup.mk'_surjective C.N)
    exact
      C.elementarySection.mixedThreeSylowCoreSynchronization_lift_commonAffineTwoBaseTranslates
        (mixedThreeSylowCoreSynchronization_of_solvable_of_commutativeSylowTwo
          hquotient)
        hlinear
termination_by Nat.card G
decreasing_by
  rw [← C.N.index_eq_card, ← C.N.index_mul_card]
  exact lt_mul_of_one_lt_right
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (C.N.one_lt_card_iff_ne_bot.mpr C.minimal.ne_bot)

/-- Same-row specialization of the preceding mixed theorem. -/
theorem
    threeConjugatesSylowSynchronization_of_solvable_of_commutativeSylowTwo
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hG : HasCommutativeSylowSubgroups 2 G) :
    HasThreeConjugatesSylowSynchronization.{uG, uI} G :=
  mixedThree_to_threeConjugates
    (mixedThreeSylowCoreSynchronization_of_solvable_of_commutativeSylowTwo
      hG)

end LisiSabatini
