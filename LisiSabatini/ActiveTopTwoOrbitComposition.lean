import LisiSabatini.ActiveTopOneOrbitComposition
import LisiSabatini.RegularTernaryListColoring
import LisiSabatini.TwoOrbitAvoidingPaletteCore

/-!
# Two-orbit composition through a primitive imprimitive top

Two-orbit avoidance supplies three pairwise distinct local orbit colours.
For the unique component with nontrivial top image, ternary regular-list
colouring chooses among those colours while simultaneously destroying every
nonidentity top fibre and avoiding both prescribed parent orbits.

If the forbidden component has trivial top image, the two local exclusions
at one marker block are instead spent directly on the two external targets.
The remaining blocks use one exclusion to make the marker bundle orbit
unique.  This also supplies regularity for the possible active component.
-/

noncomputable section

namespace LisiSabatini

universe uI uJ uR uW

variable {I : Type uI} {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- When the forbidden component has trivial top, one marker block can
simultaneously avoid two prescribed parent orbits. -/
theorem exists_blockVector_commonBaseRegular_uniqueBundleMarker_avoidingTwoOrbits_of_parentTop_bot
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (havoid : ∀ i : I,
      TwoOrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i))
    (t : J → I → W) (jmark jparent : J) (omega : I)
    (hsemiMark : IsSemiregularAt
      (D.restrictComponent (H jmark)).blockPerm.range omega)
    (hparentTop :
      (D.restrictComponent (H jparent)).blockPerm.range = ⊥)
    (c : Fin 2 → I → W) :
    ∃ v : I → W,
      (∀ j i, MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i)
        ((v + t j) i) = ⊥) ∧
      (D.restrictComponent (H jmark)).UniqueBundleOrbitAt
        (v + t jmark) omega ∧
      ∀ k, ¬ SameBlockOrbit (restrictedAmbient (H jparent))
        (v + t jparent) (c k) := by
  classical
  let Dmark := D.restrictComponent (H jmark)
  let Dparent := D.restrictComponent (H jparent)
  obtain ⟨marker, hmarkerRegular, hmarkerAvoid⟩ :=
    havoid omega jparent (fun j ↦ t j omega) (fun k ↦ c k omega)
  let markerValue : W := marker + t jmark omega
  let MarkerReachable (i : I) : Prop :=
    ∃ g : restrictedAmbient (H jmark), Dmark.blockPerm g omega = i
  let markerTransporter (i : I) : restrictedAmbient (H jmark) :=
    if hi : MarkerReachable i then Classical.choose hi else 1
  have markerTransporter_spec (i : I) (hi : MarkerReachable i) :
      Dmark.blockPerm (markerTransporter i) omega = i := by
    simp only [markerTransporter, dif_pos hi]
    exact Classical.choose_spec hi
  let markerForbidden (i : I) : W :=
    (Dmark.bundleMap (markerTransporter i) (omega, markerValue)).2
  have hother : ∀ i : I, i ≠ omega →
      ∃ w : W,
        (∀ j, MulAction.stabilizer
          (D.componentBaseImageInCommonLocalGL (H j) i)
          (w + t j i) = ⊥) ∧
        ¬ SameBlockOrbit
          (D.componentBaseImageInCommonLocalGL (H jmark) i)
          (w + t jmark i) (markerForbidden i) := by
    intro i _hi
    exact
      (havoid i).orbitAvoidingCommonRegularTranslates
        jmark (fun j ↦ t j i) (markerForbidden i)
  let other (i : I) (hi : i ≠ omega) : W :=
    Classical.choose (hother i hi)
  let v : I → W := fun i ↦
    if hi : i = omega then marker else other i hi
  have hgroupsMark (i : I) :
      Dmark.commonBaseLocalImageGL i =
        D.componentBaseImageInCommonLocalGL (H jmark) i :=
    D.restrictComponent_commonBaseLocalImageGL_eq_componentBaseImageInCommonLocalGL
      (H jmark) i
  have hgroupsParent (i : I) :
      Dparent.commonBaseLocalImageGL i =
        D.componentBaseImageInCommonLocalGL (H jparent) i :=
    D.restrictComponent_commonBaseLocalImageGL_eq_componentBaseImageInCommonLocalGL
      (H jparent) i
  refine ⟨v, ?_, ?_, ?_⟩
  · intro j i
    by_cases hi : i = omega
    · subst i
      simpa [v] using hmarkerRegular j
    · have hreg := (Classical.choose_spec (hother i hi)).1 j
      simpa [v, hi] using hreg
  · intro i horbit
    by_contra hi
    obtain ⟨g, hgBundle⟩ := horbit
    have hmarkerCoord : (v + t jmark) omega = markerValue := by
      simp [v, markerValue]
    have hgBundle' :
        Dmark.bundleMap g (omega, markerValue) =
          (i, (v + t jmark) i) := by
      simpa [Dmark, hmarkerCoord] using hgBundle
    have hgTarget : Dmark.blockPerm g omega = i := by
      have hfirst := congrArg Prod.fst hgBundle'
      simpa [bundleMap] using hfirst
    have hiReachable : MarkerReachable i := ⟨g, hgTarget⟩
    have hfiber :=
      Dmark.sameBlockOrbit_commonBaseLocalImageGL_of_same_target
        omega i hsemiMark (markerTransporter i) g
        (markerTransporter_spec i hiReachable) hgTarget markerValue
    rw [hgroupsMark i] at hfiber
    have hgValue := congrArg Prod.snd hgBundle'
    rw [hgValue] at hfiber
    change SameBlockOrbit
      (D.componentBaseImageInCommonLocalGL (H jmark) i)
      (markerForbidden i) ((v + t jmark) i) at hfiber
    have hbad : SameBlockOrbit
        (D.componentBaseImageInCommonLocalGL (H jmark) i)
        ((v + t jmark) i) (markerForbidden i) :=
      sameBlockOrbit_symm _ hfiber
    have hnot := (Classical.choose_spec (hother i hi)).2
    apply hnot
    simpa [v, hi] using hbad
  · intro k horbit
    obtain ⟨g, hg⟩ := horbit
    have hback : g⁻¹.1 • c k = v + t jparent := by
      rw [← hg]
      change g⁻¹.1 • (g.1 • (v + t jparent)) = v + t jparent
      rw [← mul_smul]
      simp
    have hgTop : Dparent.blockPerm g⁻¹ omega = omega := by
      have hgmem : Dparent.blockPerm g⁻¹ ∈ Dparent.blockPerm.range :=
        ⟨g⁻¹, rfl⟩
      rw [hparentTop] at hgmem
      have hperm : Dparent.blockPerm g⁻¹ = 1 := hgmem
      rw [hperm]
      rfl
    have hgBundle := Dparent.bundleMap_graph g⁻¹ (c k) omega
    rw [hback, hgTop] at hgBundle
    have hparentSemi : IsSemiregularAt Dparent.blockPerm.range omega := by
      have hp : Dparent.blockPerm.range = ⊥ := by
        simpa only [Dparent] using hparentTop
      rw [hp]
      exact isSemiregularAt_bot omega
    have hparentFiber :=
      Dparent.sameBlockOrbit_commonBaseLocalImageGL_of_same_target
        omega omega hparentSemi 1 g⁻¹ (by simp) hgTop (c k omega)
    rw [hgroupsParent omega] at hparentFiber
    have hgValue := congrArg Prod.snd hgBundle
    rw [hgValue] at hparentFiber
    apply hmarkerAvoid k
    simpa [v] using sameBlockOrbit_symm _ hparentFiber

/-- The active component inherits two-orbit avoidance through any nontrivial
finite regular top.  No parity hypothesis is needed. -/
theorem activeTopTwoOrbitAvoidance_of_localTwoOrbit_of_regularTop
    [Fintype I]
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (havoid : ∀ i : I,
      TwoOrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i))
    (jactive : J)
    (htop : ∀ j, j ≠ jactive →
      (D.restrictComponent (H j)).blockPerm.range = ⊥)
    (hcard : Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range =
        Fintype.card I)
    (hcardTwo : 2 ≤ Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range)
    (hsemi : IsSemiregularPermutationSubgroup
      (D.restrictComponent (H jactive)).blockPerm.range) :
    ∀ (t : J → I → W) (c : Fin 2 → I → W),
      ∃ v : I → W,
        (∀ j, MulAction.stabilizer
          (restrictedAmbient (H j)) (v + t j) = ⊥) ∧
        ∀ k, ¬ SameBlockOrbit (restrictedAmbient (H jactive))
          (v + t jactive) (c k) := by
  classical
  intro t c
  let Da := D.restrictComponent (H jactive)
  let T : Subgroup (Equiv.Perm I) := Da.blockPerm.range
  have hpaletteExists (i : I) :
      ∃ shift : Fin 3 → W,
        (∀ a j, MulAction.stabilizer
          (D.componentBaseImageInCommonLocalGL (H j) i)
          (shift a + t j i) = ⊥) ∧
        ∀ a b, SameBlockOrbit
          (D.componentBaseImageInCommonLocalGL (H jactive) i)
          (shift a + t jactive i) (shift b + t jactive i) →
          a = b := by
    obtain ⟨v₀, v₁, v₂, hreg₀, hreg₁, hreg₂,
      hsep₀₁, hsep₀₂, hsep₁₂⟩ :=
      (havoid i).exists_three_pairwise_orbitSeparated_commonRegularTranslates
        jactive (fun j ↦ t j i)
    let shift : Fin 3 → W := ![v₀, v₁, v₂]
    refine ⟨shift, ?_, ?_⟩
    · intro a j
      fin_cases a
      · simpa [shift] using hreg₀ j
      · simpa [shift] using hreg₁ j
      · simpa [shift] using hreg₂ j
    · intro a b hab
      fin_cases a <;> fin_cases b
      · rfl
      · exact (hsep₀₁ (by simpa [shift] using hab)).elim
      · exact (hsep₀₂ (by simpa [shift] using hab)).elim
      · exact (hsep₀₁
          (sameBlockOrbit_symm _ (by simpa [shift] using hab))).elim
      · rfl
      · exact (hsep₁₂ (by simpa [shift] using hab)).elim
      · exact (hsep₀₂
          (sameBlockOrbit_symm _ (by simpa [shift] using hab))).elim
      · exact (hsep₁₂
          (sameBlockOrbit_symm _ (by simpa [shift] using hab))).elim
      · rfl
  let shift (i : I) : Fin 3 → W :=
    Classical.choose (hpaletteExists i)
  have hshiftSpec (i : I) :=
    Classical.choose_spec (hpaletteExists i)
  let activeValue (i : I) (a : Fin 3) : W :=
    shift i a + t jactive i
  have hbaseRegular (i : I) (a : Fin 3) (j : J) :
      MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i)
        (shift i a + t j i) = ⊥ :=
    (hshiftSpec i).1 a j
  have hgroups (i : I) :
      Da.commonBaseLocalImageGL i =
        D.componentBaseImageInCommonLocalGL (H jactive) i :=
    D.restrictComponent_commonBaseLocalImageGL_eq_componentBaseImageInCommonLocalGL
      (H jactive) i
  have hactiveValueOrbitInjective (i : I) (x y : Fin 3)
      (hxy : SameBlockOrbit (Da.commonBaseLocalImageGL i)
        (activeValue i x) (activeValue i y)) : x = y := by
    have hxy' := hxy
    change SameBlockOrbit (Da.commonBaseLocalImageGL i)
      (shift i x + t jactive i) (shift i y + t jactive i) at hxy'
    rw [hgroups i] at hxy'
    exact (hshiftSpec i).2 x y hxy'
  let lift (sigma : T) : restrictedAmbient (H jactive) :=
    Classical.choose sigma.2
  have lift_spec (sigma : T) :
      Da.blockPerm (lift sigma) = sigma.1 :=
    Classical.choose_spec sigma.2
  let TopRelation (sigma : T) (i : I) (x y : Fin 3) : Prop :=
    SameBlockOrbit (Da.commonBaseLocalImageGL i)
      ((Da.bundleMap (lift sigma)
        (((sigma.1 : Equiv.Perm I).symm i,
          activeValue ((sigma.1 : Equiv.Perm I).symm i) x))).2)
      (activeValue i y)
  let ExternalRelation
      (k : Fin 2) (sigma : T) (i : I) (y : Fin 3) : Prop :=
    SameBlockOrbit (Da.commonBaseLocalImageGL i)
      ((Da.bundleMap (lift sigma)
        (((sigma.1 : Equiv.Perm I).symm i,
          c k ((sigma.1 : Equiv.Perm I).symm i)))).2)
      (activeValue i y)
  have hTopFunctional : ∀ sigma i x y z,
      TopRelation sigma i x y → TopRelation sigma i x z → y = z := by
    intro sigma i x y z hy hz
    exact hactiveValueOrbitInjective i y z
      (sameBlockOrbit_trans _ (sameBlockOrbit_symm _ hy) hz)
  have hExternalFunctional : ∀ k sigma i x y,
      ExternalRelation k sigma i x →
      ExternalRelation k sigma i y → x = y := by
    intro k sigma i x y hx hy
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
    exists_ternaryChoice_avoiding_deterministicTop_and_twoExternal
      T TopRelation ExternalRelation
      (by simpa [T, Da] using hcard)
      (by simpa [T, Da] using hcardTwo)
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
          have hperm : Da.blockPerm g = 1 :=
            congrArg Subtype.val hsigma
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
  · intro k horbit
    obtain ⟨g, hg⟩ := horbit
    let h : restrictedAmbient (H jactive) := g⁻¹
    let sigma : T := ⟨Da.blockPerm h, ⟨h, rfl⟩⟩
    apply hexternalAvoid k sigma
    intro i
    let source : I := (sigma.1 : Equiv.Perm I).symm i
    have hliftTarget : Da.blockPerm (lift sigma) source = i := by
      rw [lift_spec]
      exact Equiv.apply_symm_apply _ i
    have hhTarget : Da.blockPerm h source = i := by
      change (sigma.1 : Equiv.Perm I) source = i
      exact Equiv.apply_symm_apply _ i
    have hback : h.1 • c k = v + t jactive := by
      rw [← hg]
      change g⁻¹.1 • (g.1 • (v + t jactive)) = v + t jactive
      rw [← mul_smul]
      simp
    have hfiber :=
      Da.sameBlockOrbit_commonBaseLocalImageGL_of_same_target
        source i (hsemi source) (lift sigma) h
        hliftTarget hhTarget (c k source)
    have hgraphValue :
        (Da.bundleMap h (source, c k source)).2 =
          activeValue i (epsilon i) := by
      change
        (Da.blockLinear h (Da.blockPerm h source)).1 • c k source =
          activeValue i (epsilon i)
      rw [hhTarget, ← hactiveEq i]
      have hi := Da.action_apply h (c k) i
      rw [hback] at hi
      simpa [source, sigma] using hi.symm
    change ExternalRelation k sigma i (epsilon i)
    rw [hgraphValue] at hfiber
    exact hfiber

/-- **Parity-free two-orbit propagation through one primitive imprimitive
layer.** -/
theorem twoOrbitAvoidingCommonRegularTranslates_of_primitiveTop_of_localTwoOrbit
    [Finite I]
    (D : ImprimitiveLinearActionData K L)
    [Finite D.blockPerm.range]
    [Nonempty I]
    [FaithfulSMul D.blockPerm.range I]
    [MulAction.IsPreprimitive D.blockPerm.range I]
    [Nonempty J]
    (p : J → ℕ) (hp : ∀ j, Nat.Prime (p j))
    (hinj : Function.Injective p)
    (H : J → Subgroup K) (hHnormal : ∀ j, (H j).Normal)
    (hHp : ∀ j, IsPGroup (p j) (H j))
    (havoid : ∀ i : I,
      TwoOrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i)) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun j ↦ restrictedAmbient (H j)) := by
  classical
  letI : Fintype I := Fintype.ofFinite I
  obtain ⟨jactive, htop, hsemiActive⟩ :=
    D.exists_index_other_restrictComponent_ranges_bot_and_semiregular_of_primitiveTop
      p hp hinj H hHnormal hHp
  let omega : I := Classical.choice inferInstance
  intro jparent t c
  by_cases hparent : jparent = jactive
  · subst jparent
    let T : Subgroup (Equiv.Perm I) :=
      (D.restrictComponent (H jactive)).blockPerm.range
    by_cases hTbot : T = ⊥
    · obtain ⟨v, hbaseGL, _hmarker, havoidParent⟩ :=
        D.exists_blockVector_commonBaseRegular_uniqueBundleMarker_avoidingTwoOrbits_of_parentTop_bot
          H havoid t jactive jactive omega (hsemiActive omega)
          hTbot c
      refine ⟨v, ?_, havoidParent⟩
      intro j
      apply D.restrictComponent_stabilizer_eq_bot_of_commonLocalGL_of_top_bot
        (H j) (v + t j) (hbaseGL j)
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
      have hcardTwo : 2 ≤ Nat.card T := by
        haveI : Nontrivial T := T.nontrivial_iff_ne_bot.mpr hTbot
        have hone : 1 < Nat.card T :=
          Finite.one_lt_card_iff_nontrivial.mpr inferInstance
        omega
      exact
        D.activeTopTwoOrbitAvoidance_of_localTwoOrbit_of_regularTop
          H havoid jactive htop hcard hcardTwo hsemiActive t c
  · obtain ⟨v, hbaseGL, hmarker, havoidParent⟩ :=
      D.exists_blockVector_commonBaseRegular_uniqueBundleMarker_avoidingTwoOrbits_of_parentTop_bot
        H havoid t jactive jparent omega (hsemiActive omega)
        (htop jparent hparent) c
    refine ⟨v, ?_, havoidParent⟩
    intro j
    by_cases hj : j = jactive
    · subst j
      have hbase (i : I) :
          MulAction.stabilizer
            (D.componentBaseBlockImageInLocal (H jactive) i)
            ((v + t jactive) i) = ⊥ :=
        D.componentBaseBlockImageInLocal_stabilizer_eq_bot_of_commonLocalGL
          (H jactive) i ((v + t jactive) i) (hbaseGL jactive i)
      exact
        stabilizer_eq_bot_of_indexedBase_regular_of_uniqueBundleOrbit_of_semiregularAt
          (D.restrictComponent (H jactive))
          (D.componentBaseBlockImageInLocal (H jactive))
          (D.restrictComponent_kernelFactorsIn_componentBaseBlockImages
            (H jactive))
          (v + t jactive) omega hbase hmarker (hsemiActive omega)
    · exact D.restrictComponent_stabilizer_eq_bot_of_commonLocalGL_of_top_bot
        (H j) (v + t j) (hbaseGL j) (htop j hj)

end ImprimitiveLinearActionData

end LisiSabatini
