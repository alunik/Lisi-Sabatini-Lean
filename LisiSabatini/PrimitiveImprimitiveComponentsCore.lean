import LisiSabatini.ImprimitiveNormalComponentsCore
import LisiSabatini.PrimitiveNormalPSubgroup
import LisiSabatini.SelfCentralizingTop

/-!
# Proof core for normal components over a primitive imprimitive top

Let one common linear group `K` carry imprimitive data `D`, with common top
`D.blockPerm.range`.  If that top is finite and acts faithfully and
primitively on the nonempty block set, then a distinctly prime-labelled
family of normal components of `K` has at most one nontrivial permutation
image.  No solvability assumption on the top is needed.

Unlike the regular-socle interface in `ImprimitiveNormalComponents`, no
socle subgroup or socle prime is supplied here.  Any nontrivial normal prime
subgroup of a finite faithful primitive top is itself regular abelian and
self-centralizing.  Distinct normal prime subgroups commute, so one active
component annihilates every component at another prime.  This argument also
works when the ambient top is trivial and needs no `Nontrivial` assumption.

Finally, `PrimitiveNormalPSubgroup` shows that the unique possible active
normal prime image is semiregular.  The selector theorem therefore returns
both hypotheses needed by the one-active-top theorem in
`SingleTopComponent`: all other top ranges are trivial, and the chosen top
range is semiregular.
-/

noncomputable section

namespace LisiSabatini

universe uI uJ uR uW

variable {I : Type uI} {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-! ## At most one active component -/

/-- In a finite faithful primitive common top, the internal top images of
distinctly prime-labelled normal components have subsingleton support.

The proof uses either active component as the self-centralizing normal prime
subgroup.  A second active component has a different prime label, hence is
trivial by the coprime-normal centralizer argument. -/
theorem componentTopImages_nontrivialIndices_subsingleton_of_primitiveTop
    (D : ImprimitiveLinearActionData K L)
    [Finite D.blockPerm.range]
    [Nonempty I]
    [FaithfulSMul D.blockPerm.range I]
    [MulAction.IsPreprimitive D.blockPerm.range I]
    (p : J → ℕ) (hp : ∀ j, Nat.Prime (p j))
    (hinj : Function.Injective p)
    (H : J → Subgroup K) (hHn : ∀ j, (H j).Normal)
    (hHp : ∀ j, IsPGroup (p j) (H j)) :
    ({j : J | D.componentTopImage (H j) ≠ ⊥} : Set J).Subsingleton := by
  intro i hi j hj
  by_contra hij
  let Aᵢ : Subgroup D.blockPerm.range := D.componentTopImage (H i)
  let Aⱼ : Subgroup D.blockPerm.range := D.componentTopImage (H j)
  have hAᵢn : Aᵢ.Normal := D.componentTopImage_normal (H i) (hHn i)
  have hAᵢp : IsPGroup (p i) Aᵢ :=
    D.componentTopImage_isPGroup (H i) (hHp i)
  have hAⱼn : Aⱼ.Normal := D.componentTopImage_normal (H j) (hHn j)
  have hAⱼp : IsPGroup (p j) Aⱼ :=
    D.componentTopImage_isPGroup (H j) (hHp j)
  have hAᵢne : Aᵢ ≠ ⊥ := hi
  have hAⱼne : Aⱼ ≠ ⊥ := hj
  have hAᵢcomm : IsMulCommutative Aᵢ :=
    PrimitiveNormalPSubgroup.isMulCommutative
      (G := D.blockPerm.range) (Ω := I) (hp i)
      Aᵢ hAᵢn hAᵢp hAᵢne
  have hAᵢregular : IsRegularSubgroupAction Aᵢ I :=
    PrimitiveNormalPSubgroup.isRegularSubgroupAction
      (G := D.blockPerm.range) (Ω := I) (hp i)
      Aᵢ hAᵢn hAᵢp hAᵢne
  letI : IsMulCommutative Aᵢ := hAᵢcomm
  letI : MulAction.IsPretransitive Aᵢ I := hAᵢregular.1
  let C : SelfCentralizingNormalPSubgroup (p i) D.blockPerm.range :=
    { subgroup := Aᵢ
      normal := hAᵢn
      isPGroup := hAᵢp
      centralizer_le :=
        PrimitiveSolvableTop.centralizer_le_of_isMulCommutative_of_isPretransitive
          (Ω := I) Aᵢ }
  have hpne : p j ≠ p i := by
    intro hpji
    exact hij (hinj hpji.symm)
  exact hAⱼne
    (C.normalPSubgroup_eq_bot_of_ne
      (hp i) (hp j) hpne Aⱼ hAⱼn hAⱼp)

/-- Concrete restricted-action form of the primitive-top theorem: at most
one restricted block-permutation range is nontrivial. -/
theorem restrictComponentRanges_nontrivialIndices_subsingleton_of_primitiveTop
    (D : ImprimitiveLinearActionData K L)
    [Finite D.blockPerm.range]
    [Nonempty I]
    [FaithfulSMul D.blockPerm.range I]
    [MulAction.IsPreprimitive D.blockPerm.range I]
    (p : J → ℕ) (hp : ∀ j, Nat.Prime (p j))
    (hinj : Function.Injective p)
    (H : J → Subgroup K) (hHn : ∀ j, (H j).Normal)
    (hHp : ∀ j, IsPGroup (p j) (H j)) :
    ({j : J | (D.restrictComponent (H j)).blockPerm.range ≠ ⊥} :
      Set J).Subsingleton := by
  intro i hi j hj
  apply D.componentTopImages_nontrivialIndices_subsingleton_of_primitiveTop
    p hp hinj H hHn hHp
  · intro hbot
    exact hi ((D.restrictComponent_range_eq_bot_iff (H i)).mpr hbot)
  · intro hbot
    exact hj ((D.restrictComponent_range_eq_bot_iff (H j)).mpr hbot)

/-! ## Semiregularity of the possible active image -/

/-- Every nontrivial concrete restricted top range is semiregular.  Normality
and the prime-group property are first transported to the internal top
image.  `PrimitiveNormalPSubgroup` proves semiregularity there, and the exact
range identity from `ImprimitiveNormalComponents` transports it back to the
concrete range used by `SingleTopComponent`.

Solvability of the common top is not needed for this local statement. -/
theorem restrictComponent_range_isSemiregular_of_ne_bot
    (D : ImprimitiveLinearActionData K L)
    [Finite D.blockPerm.range]
    [Nonempty I]
    [FaithfulSMul D.blockPerm.range I]
    [MulAction.IsPreprimitive D.blockPerm.range I]
    {p : ℕ} (hp : Nat.Prime p)
    (H : Subgroup K) (hHn : H.Normal) (hHp : IsPGroup p H)
    (hne : (D.restrictComponent H).blockPerm.range ≠ ⊥) :
    IsSemiregularPermutationSubgroup
      (D.restrictComponent H).blockPerm.range := by
  have htopNe : D.componentTopImage H ≠ ⊥ := by
    intro hbot
    exact hne ((D.restrictComponent_range_eq_bot_iff H).mpr hbot)
  have hsemi :=
    PrimitiveNormalPSubgroup.permutationImage_isSemiregular
      (G := D.blockPerm.range) (Ω := I) hp
      (D.componentTopImage H)
      (D.componentTopImage_normal H hHn)
      (D.componentTopImage_isPGroup H hHp) htopNe
  change IsSemiregularPermutationSubgroup
    ((D.componentTopImage H).map D.blockPerm.range.subtype) at hsemi
  rwa [D.componentTopImage_map_subtype_eq_restrictComponent_range H] at hsemi

/-- Every restricted top range is semiregular: the nontrivial case is the
primitive normal-prime theorem, while the trivial range acts freely
vacuously. -/
theorem restrictComponent_range_isSemiregular
    (D : ImprimitiveLinearActionData K L)
    [Finite D.blockPerm.range]
    [Nonempty I]
    [FaithfulSMul D.blockPerm.range I]
    [MulAction.IsPreprimitive D.blockPerm.range I]
    {p : ℕ} (hp : Nat.Prime p)
    (H : Subgroup K) (hHn : H.Normal) (hHp : IsPGroup p H) :
    IsSemiregularPermutationSubgroup
      (D.restrictComponent H).blockPerm.range := by
  by_cases hne : (D.restrictComponent H).blockPerm.range ≠ ⊥
  · exact D.restrictComponent_range_isSemiregular_of_ne_bot
      hp H hHn hHp hne
  · rw [not_ne_iff.mp hne]
    exact isSemiregularPermutationSubgroup_bot

/-! ## Exact one-active-top selector -/

/-- Choose a component `j₀` such that every other restricted top range is
trivial and the chosen range is semiregular.

If an active range exists, subsingleton support makes it the unique choice
and the preceding theorem supplies semiregularity.  If every range is
trivial, an arbitrary index is chosen and the trivial permutation subgroup
is semiregular.  Thus the conclusion works uniformly even when the common
top itself is trivial. -/
theorem exists_index_other_restrictComponent_ranges_bot_and_semiregular_of_primitiveTop
    [Nonempty J]
    (D : ImprimitiveLinearActionData K L)
    [Finite D.blockPerm.range]
    [Nonempty I]
    [FaithfulSMul D.blockPerm.range I]
    [MulAction.IsPreprimitive D.blockPerm.range I]
    (p : J → ℕ) (hp : ∀ j, Nat.Prime (p j))
    (hinj : Function.Injective p)
    (H : J → Subgroup K) (hHn : ∀ j, (H j).Normal)
    (hHp : ∀ j, IsPGroup (p j) (H j)) :
    ∃ j₀ : J,
      (∀ j, j ≠ j₀ →
        (D.restrictComponent (H j)).blockPerm.range = ⊥) ∧
      IsSemiregularPermutationSubgroup
        (D.restrictComponent (H j₀)).blockPerm.range := by
  classical
  have hsub :=
    D.restrictComponentRanges_nontrivialIndices_subsingleton_of_primitiveTop
      p hp hinj H hHn hHp
  by_cases hactive : ∃ j : J,
      (D.restrictComponent (H j)).blockPerm.range ≠ ⊥
  · obtain ⟨j₀, hj₀⟩ := hactive
    refine ⟨j₀, ?_,
      D.restrictComponent_range_isSemiregular_of_ne_bot
        (hp j₀) (H j₀) (hHn j₀) (hHp j₀) hj₀⟩
    intro j hj
    by_contra hjtop
    exact hj (hsub hjtop hj₀)
  · let j₀ : J := Classical.choice inferInstance
    refine ⟨j₀, fun j _ ↦
      not_ne_iff.mp (not_exists.mp hactive j), ?_⟩
    exact D.restrictComponent_range_isSemiregular
      (hp j₀) (H j₀) (hHn j₀) (hHp j₀)

end ImprimitiveLinearActionData

end LisiSabatini
