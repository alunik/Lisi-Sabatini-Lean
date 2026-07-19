import LisiSabatini.OddRegularListColoring
import LisiSabatini.RecursiveMixedPrimeCoreCore

/-!
# One-orbit composition through an active odd regular top

The generic labelled recursion spends one additional forbidden orbit at an
imprimitive node.  That loss is not necessary for the ordinary one-orbit
property.  In the only hard case, the externally distinguished component is
also the unique component with nontrivial top image.

Local one-orbit avoidance gives two simultaneously admissible base-orbit
colours at every block.  These are arbitrary block-dependent lists because
the affine translations are independent.  `OddRegularListColoring` chooses
one entry from every list while avoiding all nonidentity exact top fibres and
the prescribed external orbit.  This file identifies those deterministic
relations with the exact bundle fibres of the active component.
-/

noncomputable section

namespace LisiSabatini

universe uI uJ uR uW

variable {I : Type uI} {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- A finite regular permutation subgroup has the same cardinality as its
permutation domain. -/
theorem natCard_eq_fintypeCard_of_isRegularAbelianPermutationSubgroup
    [Fintype I] [Nonempty I]
    (T : Subgroup (Equiv.Perm I))
    (hT : IsRegularAbelianPermutationSubgroup T) :
    Nat.card T = Fintype.card I := by
  classical
  let omega : I := Classical.choice inferInstance
  letI : Fintype T := Fintype.ofFinite T
  have hcard :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (α := T) omega
  have horbit : MulAction.orbit T omega = Set.univ := by
    ext i
    simp only [Set.mem_univ, iff_true]
    exact hT.transitive omega i
  have hstabilizer : MulAction.stabilizer T omega = ⊥ :=
    hT.semiregular omega
  have hstabilizerCard :
      Fintype.card (MulAction.stabilizer T omega) = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    refine ⟨1, fun sigma ↦ ?_⟩
    apply Subtype.ext
    apply Subgroup.mem_bot.mp
    rw [← hstabilizer]
    exact sigma.2
  rw [show Fintype.card (MulAction.orbit T omega) = Fintype.card I by
      rw [Fintype.card_subtype, horbit]
      simp,
    hstabilizerCard,
    mul_one] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard.symm

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- If every component top is trivial, one local forbidden orbit at a
single block gives the active residual directly. -/
theorem activeTopOrbitAvoidanceResidual_of_localOneOrbit_of_allTops_bot
    [Nonempty I]
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (havoid : ∀ i : I,
      OrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i))
    (jactive : J)
    (htop : ∀ j,
      (D.restrictComponent (H j)).blockPerm.range = ⊥) :
    ActiveTopOrbitAvoidanceResidual H jactive := by
  classical
  intro t c
  let omega : I := Classical.choice inferInstance
  have hsemi : IsSemiregularAt
      (D.restrictComponent (H jactive)).blockPerm.range omega := by
    rw [htop jactive]
    exact isSemiregularAt_bot omega
  obtain ⟨v, hbaseGL, _hmarker, hparent⟩ :=
    D.exists_blockVector_commonBaseRegular_uniqueBundleMarker_avoidingOrbit_of_parentTop_bot
      H havoid t jactive jactive omega hsemi (htop jactive) c
  refine ⟨v, ?_, hparent⟩
  intro j
  exact D.restrictComponent_stabilizer_eq_bot_of_commonLocalGL_of_top_bot
    (H j) (v + t j) (hbaseGL j) (htop j)

/-- The active-top residual propagates from local one-orbit avoidance when
the active restricted top is a nontrivial odd regular permutation group.

The cardinal hypotheses are the concrete finite form of regularity.  They
are kept explicit here so the theorem is reusable independently of how the
primitive-top structure was obtained. -/
theorem activeTopOrbitAvoidanceResidual_of_localOneOrbit_of_regularOddTop
    [Fintype I]
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (havoid : ∀ i : I,
      OrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i))
    (jactive : J)
    (htop : ∀ j, j ≠ jactive →
      (D.restrictComponent (H j)).blockPerm.range = ⊥)
    (hcard : Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range =
        Fintype.card I)
    (hodd : Odd (Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range))
    (hthree : 3 ≤ Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range)
    (hsemi : IsSemiregularPermutationSubgroup
      (D.restrictComponent (H jactive)).blockPerm.range) :
    ActiveTopOrbitAvoidanceResidual H jactive := by
  classical
  intro t c
  let Da := D.restrictComponent (H jactive)
  let T : Subgroup (Equiv.Perm I) := Da.blockPerm.range
  have hfirstExists (i : I) :
      ∃ w : W,
        (∀ j, MulAction.stabilizer
          (D.componentBaseImageInCommonLocalGL (H j) i)
          (w + t j i) = ⊥) ∧
        ¬ SameBlockOrbit
          (D.componentBaseImageInCommonLocalGL (H jactive) i)
          (w + t jactive i) 0 :=
    havoid i jactive (fun j ↦ t j i) 0
  let firstShift (i : I) : W := Classical.choose (hfirstExists i)
  have hfirstSpec (i : I) :=
    Classical.choose_spec (hfirstExists i)
  have hsecondExists (i : I) :
      ∃ w : W,
        (∀ j, MulAction.stabilizer
          (D.componentBaseImageInCommonLocalGL (H j) i)
          (w + t j i) = ⊥) ∧
        ¬ SameBlockOrbit
          (D.componentBaseImageInCommonLocalGL (H jactive) i)
          (w + t jactive i) (firstShift i + t jactive i) :=
    havoid i jactive (fun j ↦ t j i)
      (firstShift i + t jactive i)
  let secondShift (i : I) : W := Classical.choose (hsecondExists i)
  have hsecondSpec (i : I) :=
    Classical.choose_spec (hsecondExists i)
  let shift (i : I) : Bool → W
    | false => firstShift i
    | true => secondShift i
  let activeValue (i : I) (b : Bool) : W :=
    shift i b + t jactive i
  have hbaseRegular (i : I) (b : Bool) (j : J) :
      MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i)
        (shift i b + t j i) = ⊥ := by
    cases b
    · exact (hfirstSpec i).1 j
    · exact (hsecondSpec i).1 j
  have hgroups (i : I) :
      Da.commonBaseLocalImageGL i =
        D.componentBaseImageInCommonLocalGL (H jactive) i :=
    D.restrictComponent_commonBaseLocalImageGL_eq_componentBaseImageInCommonLocalGL
      (H jactive) i
  have hseparate (i : I) :
      ¬ SameBlockOrbit (Da.commonBaseLocalImageGL i)
        (activeValue i true) (activeValue i false) := by
    rw [hgroups i]
    exact (hsecondSpec i).2
  let lift (sigma : T) : restrictedAmbient (H jactive) :=
    Classical.choose sigma.2
  have lift_spec (sigma : T) :
      Da.blockPerm (lift sigma) = sigma.1 :=
    Classical.choose_spec sigma.2
  let TopRelation (sigma : T) (i : I) (x y : Bool) : Prop :=
    SameBlockOrbit (Da.commonBaseLocalImageGL i)
      ((Da.bundleMap (lift sigma)
        (((sigma.1 : Equiv.Perm I).symm i,
          activeValue ((sigma.1 : Equiv.Perm I).symm i) x))).2)
      (activeValue i y)
  let ExternalRelation (sigma : T) (i : I) (y : Bool) : Prop :=
    SameBlockOrbit (Da.commonBaseLocalImageGL i)
      ((Da.bundleMap (lift sigma)
        (((sigma.1 : Equiv.Perm I).symm i,
          c ((sigma.1 : Equiv.Perm I).symm i)))).2)
      (activeValue i y)
  have hactiveValueOrbitInjective (i : I) (x y : Bool)
      (hxy : SameBlockOrbit (Da.commonBaseLocalImageGL i)
        (activeValue i x) (activeValue i y)) : x = y := by
    cases x <;> cases y
    · rfl
    · exact (hseparate i (sameBlockOrbit_symm _ hxy)).elim
    · exact (hseparate i hxy).elim
    · rfl
  have hTopFunctional : ∀ sigma i x y z,
      TopRelation sigma i x y → TopRelation sigma i x z → y = z := by
    intro sigma i x y z hy hz
    exact hactiveValueOrbitInjective i y z
      (sameBlockOrbit_trans _ (sameBlockOrbit_symm _ hy) hz)
  have hExternalFunctional : ∀ sigma i x y,
      ExternalRelation sigma i x → ExternalRelation sigma i y → x = y := by
    intro sigma i x y hx hy
    exact hactiveValueOrbitInjective i x y
      (sameBlockOrbit_trans _ (sameBlockOrbit_symm _ hx) hy)
  letI : IsCancelSMul T I :=
    isCancelSMul_iff_stabilizer_eq_bot.mpr fun i ↦ by
      simpa [T, Da, IsSemiregularAt] using hsemi i
  have hsemiPoint : ∀ sigma : T, sigma ≠ 1 → ∀ i,
      (sigma.1 : Equiv.Perm I) i ≠ i := by
    intro sigma hsigma i hfix
    exact hsigma (IsCancelSMul.eq_one_of_smul hfix)
  obtain ⟨epsilon, htopAvoid, hexternalAvoid⟩ :=
    exists_binaryChoice_avoiding_regularOddTop_and_external
      T TopRelation ExternalRelation
      (by simpa [T, Da] using hcard)
      (by simpa [T, Da] using hodd)
      (by simpa [T, Da] using hthree)
      hsemiPoint hTopFunctional hExternalFunctional
  let v : I → W := fun i ↦ shift i (epsilon i)
  have hbaseGL (j : J) (i : I) :
      MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i)
        ((v + t j) i) = ⊥ := by
    simpa [v] using hbaseRegular i (epsilon i) j
  have hactiveEq (i : I) :
      (v + t jactive) i = activeValue i (epsilon i) := by
    rfl
  refine ⟨v, ?_, ?_⟩
  · intro j
    by_cases hj : j = jactive
    · subst j
      have hbase (i : I) :
          MulAction.stabilizer
            (D.componentBaseBlockImageInLocal (H jactive) i)
            ((v + t jactive) i) = ⊥ :=
        D.componentBaseBlockImageInLocal_stabilizer_eq_bot_of_commonLocalGL
          (H jactive) i ((v + t jactive) i) (hbaseGL jactive i)
      apply (Subgroup.eq_bot_iff_forall _).mpr
      intro g hg
      let sigma : T := ⟨Da.blockPerm g, ⟨g, rfl⟩⟩
      by_cases hsigma : sigma = 1
      · let gs : MulAction.stabilizer (restrictedAmbient (H jactive))
            (v + t jactive) := ⟨g, hg⟩
        have hgs : gs = 1 := by
          apply pointStabilizerBlockPerm_injective_of_indexedBase_regular
            Da (D.componentBaseBlockImageInLocal (H jactive))
            (D.restrictComponent_kernelFactorsIn_componentBaseBlockImages
              (H jactive)) (v + t jactive) hbase
          have hperm : Da.blockPerm g = 1 := by
            exact congrArg Subtype.val hsigma
          simpa [pointStabilizerBlockPerm] using hperm
        exact congrArg Subtype.val hgs
      · exfalso
        apply htopAvoid sigma hsigma
        intro i
        let source : I := (sigma.1 : Equiv.Perm I).symm i
        have hliftTarget : Da.blockPerm (lift sigma) source = i := by
          rw [lift_spec]
          exact Equiv.apply_symm_apply _ i
        have hgTarget : Da.blockPerm g source = i := by
          change (sigma.1 : Equiv.Perm I) source = i
          exact Equiv.apply_symm_apply _ i
        have hfiber :=
          Da.sameBlockOrbit_commonBaseLocalImageGL_of_same_target
            source i (hsemi source) (lift sigma) g
            hliftTarget hgTarget (activeValue source (epsilon source))
        have hgraph := Da.bundleMap_graph_of_fix g (v + t jactive)
          (MulAction.mem_stabilizer_iff.mp hg) source
        have hgraphValue := congrArg Prod.snd hgraph
        have hgraphValue' :
            (Da.bundleMap g
              (source, activeValue source (epsilon source))).2 =
              activeValue i (epsilon i) := by
          rw [← hactiveEq source]
          calc
            (Da.bundleMap g (source, (v + t jactive) source)).2 =
                (v + t jactive) i := by
              simpa [hgTarget] using hgraphValue
            _ = activeValue i (epsilon i) := hactiveEq i
        change TopRelation sigma i (epsilon source) (epsilon i)
        rw [hgraphValue'] at hfiber
        exact hfiber
    · exact D.restrictComponent_stabilizer_eq_bot_of_commonLocalGL_of_top_bot
        (H j) (v + t j) (hbaseGL j) (htop j hj)
  · intro horbit
    obtain ⟨g, hg⟩ := horbit
    let h : restrictedAmbient (H jactive) := g⁻¹
    let sigma : T := ⟨Da.blockPerm h, ⟨h, rfl⟩⟩
    apply hexternalAvoid sigma
    intro i
    let source : I := (sigma.1 : Equiv.Perm I).symm i
    have hliftTarget : Da.blockPerm (lift sigma) source = i := by
      rw [lift_spec]
      exact Equiv.apply_symm_apply _ i
    have hhTarget : Da.blockPerm h source = i := by
      change (sigma.1 : Equiv.Perm I) source = i
      exact Equiv.apply_symm_apply _ i
    have hback : h.1 • c = v + t jactive := by
      rw [← hg]
      change g⁻¹.1 • (g.1 • (v + t jactive)) = v + t jactive
      rw [← mul_smul]
      simp
    have hfiber :=
      Da.sameBlockOrbit_commonBaseLocalImageGL_of_same_target
        source i (hsemi source) (lift sigma) h
        hliftTarget hhTarget (c source)
    have hgraphValue :
        (Da.bundleMap h (source, c source)).2 =
          activeValue i (epsilon i) := by
      change
        (Da.blockLinear h (Da.blockPerm h source)).1 • c source =
          activeValue i (epsilon i)
      rw [hhTarget, ← hactiveEq i]
      have hi := Da.action_apply h c i
      rw [hback] at hi
      simpa [source, sigma] using hi.symm
    change ExternalRelation sigma i (epsilon i)
    rw [hgraphValue] at hfiber
    exact hfiber

/-- **Sharp one-orbit propagation through one primitive imprimitive
layer.**  Unlike labelled multi-orbit recursion, ordinary one-orbit
avoidance loses no palette capacity at the node. -/
theorem orbitAvoidingCommonRegularTranslates_of_primitiveTop_of_localOneOrbit
    [Finite I]
    (D : ImprimitiveLinearActionData K L)
    [Finite D.blockPerm.range]
    [Nonempty I]
    [FaithfulSMul D.blockPerm.range I]
    [MulAction.IsPreprimitive D.blockPerm.range I]
    [Nonempty J]
    (p : J → ℕ) (hp : ∀ j, Nat.Prime (p j))
    (hinj : Function.Injective p)
    (hpTwo : ∀ j, p j ≠ 2)
    (H : J → Subgroup K) (hHnormal : ∀ j, (H j).Normal)
    (hHp : ∀ j, IsPGroup (p j) (H j))
    (havoid : ∀ i : I,
      OrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i)) :
    OrbitAvoidingCommonRegularTranslates
      (fun j ↦ restrictedAmbient (H j)) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨jactive, htop, hsemiActive⟩ :=
    D.exists_index_other_restrictComponent_ranges_bot_and_semiregular_of_primitiveTop
      p hp hinj H hHnormal hHp
  let omega : I := Classical.choice inferInstance
  have hsemi (j : J) : IsSemiregularAt
      (D.restrictComponent (H j)).blockPerm.range omega :=
    (D.restrictComponent_range_isSemiregular
      (hp j) (H j) (hHnormal j) (hHp j)) omega
  have haway : OrbitAvoidingCommonRegularTranslatesAwayFrom jactive
      (fun j ↦ restrictedAmbient (H j)) :=
    D.orbitAvoidingCommonRegularTranslatesAwayFrom_of_imprimitive_atMostOneTop
      H havoid jactive omega htop hsemi
  apply orbitAvoidingCommonRegularTranslates_of_awayFrom_of_activeResidual
    H jactive haway
  let T : Subgroup (Equiv.Perm I) :=
    (D.restrictComponent (H jactive)).blockPerm.range
  by_cases hTbot : T = ⊥
  · apply
      D.activeTopOrbitAvoidanceResidual_of_localOneOrbit_of_allTops_bot
        H havoid jactive
    intro j
    by_cases hj : j = jactive
    · subst j
      exact hTbot
    · exact htop j hj
  · let A : Subgroup D.blockPerm.range :=
      D.componentTopImage (H jactive)
    have hAne : A ≠ ⊥ := by
      intro hAbot
      apply hTbot
      exact (D.restrictComponent_range_eq_bot_iff (H jactive)).mpr hAbot
    have hAn : A.Normal :=
      D.componentTopImage_normal (H jactive) (hHnormal jactive)
    have hAp : IsPGroup (p jactive) A :=
      D.componentTopImage_isPGroup (H jactive) (hHp jactive)
    have hregularMapped :
        IsRegularAbelianPermutationSubgroup
          (A.map D.blockPerm.range.subtype) :=
      PrimitiveNormalPSubgroup.map_subtype_isRegularAbelian
        D.blockPerm.range (hp jactive) A hAn hAp hAne
    have hregular : IsRegularAbelianPermutationSubgroup T := by
      rw [D.componentTopImage_map_subtype_eq_restrictComponent_range
        (H jactive)] at hregularMapped
      exact hregularMapped
    have hcard : Nat.card T = Fintype.card I :=
      natCard_eq_fintypeCard_of_isRegularAbelianPermutationSubgroup
        T hregular
    have hTp : IsPGroup (p jactive) T := by
      have hmapped := hAp.map D.blockPerm.range.subtype
      rw [D.componentTopImage_map_subtype_eq_restrictComponent_range
        (H jactive)] at hmapped
      exact hmapped
    letI : Fact (Nat.Prime (p jactive)) := ⟨hp jactive⟩
    have hoddT : Odd (Nat.card T) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hTp
      rw [hn]
      exact ((hp jactive).odd_of_ne_two (hpTwo jactive)).pow
    have hthreeT : 3 ≤ Nat.card T := by
      haveI : Nontrivial T := T.nontrivial_iff_ne_bot.mpr hTbot
      have hone : 1 < Nat.card T :=
        Finite.one_lt_card_iff_nontrivial.mpr inferInstance
      obtain ⟨k, hk⟩ := hoddT
      omega
    exact
      D.activeTopOrbitAvoidanceResidual_of_localOneOrbit_of_regularOddTop
        H havoid jactive htop hcard hoddT hthreeT hsemiActive

end ImprimitiveLinearActionData

end LisiSabatini
