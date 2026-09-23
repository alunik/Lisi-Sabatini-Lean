module

public import LisiSabatini.OddRegularListColoring
public import LisiSabatini.ImprimitiveBundleMarkerCore
public import LisiSabatini.ImprimitiveBundleGraph

/-!
# Odd-top composition retaining a distinguished stabilizer

The extra component in the all-prime translated-regularity induction fixes
all blocks. Its local stabilizers must be contained in prescribed reference
stabilizers, and are not required to be trivial. We carry arbitrary local
admissibility conditions through the odd-top composition, then specialize
them to this literal containment condition.

All structural assumptions on the block system and the local induction
hypothesis remain explicit. This module does not assert the full nilpotent
translated-regularity theorem.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uJ uR uW

variable {I : Type uI} {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- Coordinatewise containment in the local base images implies literal
containment of full stabilizers for a component which fixes every block. -/
theorem restrictComponent_stabilizer_le_of_local_stabilizer_le_of_top_bot
    (D : ImprimitiveLinearActionData K L) (T : Subgroup K)
    (x a : I → W)
    (htop : (D.restrictComponent T).blockPerm.range = ⊥)
    (hlocal : ∀ i,
      MulAction.stabilizer (D.componentBaseImageInCommonLocalGL T i) (x i) ≤
        MulAction.stabilizer (D.componentBaseImageInCommonLocalGL T i) (a i)) :
    MulAction.stabilizer (restrictedAmbient T) x ≤
      MulAction.stabilizer (restrictedAmbient T) a := by
  intro g hg
  have hgfix : g.1 • x = x := MulAction.mem_stabilizer_iff.mp hg
  have hgker : g ∈ D.componentBaseKernel T := by
    have hmem : (D.restrictComponent T).blockPerm g ∈
        (D.restrictComponent T).blockPerm.range := ⟨g, rfl⟩
    rw [htop] at hmem
    exact hmem
  let gbase : D.componentBaseKernel T := ⟨g, hgker⟩
  apply MulAction.mem_stabilizer_iff.mpr
  ext i
  change (gbase.1.1 • a) i = a i
  rw [D.componentBaseKernel_action_apply T gbase a i]
  let image : D.componentBaseImageInCommonLocalGL T i :=
    ⟨D.componentBaseBlockLinearGL T i gbase, by
      rw [D.componentBaseImageInCommonLocalGL_eq_componentBaseBlockImage T i]
      exact MonoidHom.mem_range.mpr ⟨gbase, rfl⟩⟩
  have himage : image ∈
      MulAction.stabilizer (D.componentBaseImageInCommonLocalGL T i) (x i) := by
    apply MulAction.mem_stabilizer_iff.mpr
    change (D.componentBaseBlockLinearGL T i gbase) • x i = x i
    rw [← D.componentBaseKernel_action_apply T gbase x i, hgfix]
  exact MulAction.mem_stabilizer_iff.mp (hlocal i himage)

/-- The binary odd-top construction retains every coordinatewise condition
shared by its two local palette entries. The externally marked component
is the active component in this version. -/
theorem exists_admissible_regular_translate_avoiding_activeOrbit_of_regularOddTop
    [Fintype I]
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (t : J → I → W) (admissible : I → W → Prop)
    (havoid : ∀ i jparent c, ∃ w : W,
      admissible i w ∧
      (∀ j, MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i) (w + t j i) = ⊥) ∧
      ¬ SameBlockOrbit
        (D.componentBaseImageInCommonLocalGL (H jparent) i)
        (w + t jparent i) c)
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
    ∀ c : I → W, ∃ v : I → W,
      (∀ i, admissible i (v i)) ∧
      (∀ j, MulAction.stabilizer (restrictedAmbient (H j)) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit (restrictedAmbient (H jactive)) (v + t jactive) c := by
  classical
  intro c
  let Da := D.restrictComponent (H jactive)
  let T : Subgroup (Equiv.Perm I) := Da.blockPerm.range
  have hfirstExists (i : I) :
      ∃ w : W,
        admissible i w ∧
        (∀ j, MulAction.stabilizer
          (D.componentBaseImageInCommonLocalGL (H j) i)
          (w + t j i) = ⊥) ∧
        ¬ SameBlockOrbit
          (D.componentBaseImageInCommonLocalGL (H jactive) i)
          (w + t jactive i) 0 :=
    havoid i jactive 0
  let firstShift (i : I) : W := Classical.choose (hfirstExists i)
  have hfirstSpec (i : I) :=
    Classical.choose_spec (hfirstExists i)
  have hsecondExists (i : I) :
      ∃ w : W,
        admissible i w ∧
        (∀ j, MulAction.stabilizer
          (D.componentBaseImageInCommonLocalGL (H j) i)
          (w + t j i) = ⊥) ∧
        ¬ SameBlockOrbit
          (D.componentBaseImageInCommonLocalGL (H jactive) i)
          (w + t jactive i) (firstShift i + t jactive i) :=
    havoid i jactive (firstShift i + t jactive i)
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
    · exact (hfirstSpec i).2.1 j
    · exact (hsecondSpec i).2.1 j
  have hgroups (i : I) :
      Da.commonBaseLocalImageGL i =
        D.componentBaseImageInCommonLocalGL (H jactive) i :=
    D.restrictComponent_commonBaseLocalImageGL_eq_componentBaseImageInCommonLocalGL
      (H jactive) i
  have hseparate (i : I) :
      ¬ SameBlockOrbit (Da.commonBaseLocalImageGL i)
        (activeValue i true) (activeValue i false) := by
    rw [hgroups i]
    exact (hsecondSpec i).2.2
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
  let : IsCancelSMul T I :=
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
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    change admissible i (shift i (epsilon i))
    cases h : epsilon i
    · exact (hfirstSpec i).1
    · exact (hsecondSpec i).1
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

/-- The unique-marker construction also retains coordinatewise conditions
when the externally marked component fixes all blocks. -/
theorem exists_admissible_blockVector_regular_marker_avoidingOrbit_of_parentTop_bot
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (t : J → I → W) (admissible : I → W → Prop)
    (havoid : ∀ i jparent c, ∃ w : W,
      admissible i w ∧
      (∀ j, MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i) (w + t j i) = ⊥) ∧
      ¬ SameBlockOrbit
        (D.componentBaseImageInCommonLocalGL (H jparent) i)
        (w + t jparent i) c)
    (jmark jparent : J) (omega : I)
    (hsemiMark : IsSemiregularAt
      (D.restrictComponent (H jmark)).blockPerm.range omega)
    (hparentTop :
      (D.restrictComponent (H jparent)).blockPerm.range = ⊥)
    (c : I → W) :
    ∃ v : I → W,
      (∀ i, admissible i (v i)) ∧
      (∀ j i, MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i)
        ((v + t j) i) = ⊥) ∧
      (D.restrictComponent (H jmark)).UniqueBundleOrbitAt
        (v + t jmark) omega ∧
      ¬ SameBlockOrbit (restrictedAmbient (H jparent))
        (v + t jparent) c := by
  classical
  let Dmark := D.restrictComponent (H jmark)
  let Dparent := D.restrictComponent (H jparent)
  obtain ⟨marker, hmarkerAdmissible, hmarkerRegular, hmarkerAvoid⟩ :=
    havoid omega jparent (c omega)
  let markerValue : W := marker + t jmark omega
  let MarkerReachable (i : I) : Prop :=
    ∃ g : restrictedAmbient (H jmark), Dmark.blockPerm g omega = i
  let markerTransporter (i : I) : restrictedAmbient (H jmark) :=
    if hi : MarkerReachable i then Classical.choose hi else 1
  have markerTransporter_spec (i : I) (hi : MarkerReachable i) :
      Dmark.blockPerm (markerTransporter i) omega = i := by
    simp only [markerTransporter, dite_eq_left hi]
    exact Classical.choose_spec hi
  let markerForbidden (i : I) : W :=
    (Dmark.bundleMap (markerTransporter i) (omega, markerValue)).2
  have hother : ∀ i : I, i ≠ omega →
      ∃ w : W,
        admissible i w ∧
        (∀ j, MulAction.stabilizer
          (D.componentBaseImageInCommonLocalGL (H j) i)
          (w + t j i) = ⊥) ∧
        ¬ SameBlockOrbit
          (D.componentBaseImageInCommonLocalGL (H jmark) i)
          (w + t jmark i) (markerForbidden i) := by
    intro i _hi
    exact havoid i jmark (markerForbidden i)
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
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = omega
    · subst i
      simpa [v] using hmarkerAdmissible
    · have ha := (Classical.choose_spec (hother i hi)).1
      simpa [v, hi, other] using ha
  · intro j i
    by_cases hi : i = omega
    · subst i
      simpa [v] using hmarkerRegular j
    · have hreg := (Classical.choose_spec (hother i hi)).2.1 j
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
    have hnot := (Classical.choose_spec (hother i hi)).2.2
    apply hnot
    simpa [v, hi] using hbad
  · intro horbit
    obtain ⟨g, hg⟩ := horbit
    have hback : g⁻¹.1 • c = v + t jparent := by
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
    have hgBundle := Dparent.bundleMap_graph g⁻¹ c omega
    rw [hback, hgTop] at hgBundle
    have hparentSemi : IsSemiregularAt Dparent.blockPerm.range omega := by
      have hp : Dparent.blockPerm.range = ⊥ := by
        simpa only [Dparent] using hparentTop
      rw [hp]
      exact isSemiregularAt_bot omega
    have hparentFiber :=
      Dparent.sameBlockOrbit_commonBaseLocalImageGL_of_same_target
        omega omega hparentSemi 1 g⁻¹ (by simp) hgTop (c omega)
    rw [hgroupsParent omega] at hparentFiber
    have hgValue := congrArg Prod.snd hgBundle
    rw [hgValue] at hparentFiber
    apply hmarkerAvoid
    simpa [v] using sameBlockOrbit_symm _ hparentFiber


/-- Every externally marked component is covered by odd-top composition,
while retaining the common coordinatewise admissibility conditions. -/
theorem exists_admissible_regular_translate_avoidingOrbit_of_regularOddTop
    [Fintype I] [Nonempty I]
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (t : J → I → W) (admissible : I → W → Prop)
    (havoid : ∀ i jparent c, ∃ w : W,
      admissible i w ∧
      (∀ j, MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i) (w + t j i) = ⊥) ∧
      ¬ SameBlockOrbit
        (D.componentBaseImageInCommonLocalGL (H jparent) i)
        (w + t jparent i) c)
    (jactive : J)
    (htop : ∀ j, j ≠ jactive →
      (D.restrictComponent (H j)).blockPerm.range = ⊥)
    (hcard : Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range = Fintype.card I)
    (hodd : Odd (Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range))
    (hthree : 3 ≤ Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range)
    (hsemi : IsSemiregularPermutationSubgroup
      (D.restrictComponent (H jactive)).blockPerm.range)
    (jparent : J) (c : I → W) :
    ∃ v : I → W,
      (∀ i, admissible i (v i)) ∧
      (∀ j, MulAction.stabilizer (restrictedAmbient (H j)) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit (restrictedAmbient (H jparent)) (v + t jparent) c := by
  classical
  by_cases hj : jparent = jactive
  · subst jparent
    exact D.exists_admissible_regular_translate_avoiding_activeOrbit_of_regularOddTop
      H t admissible havoid jactive htop hcard hodd hthree hsemi c
  · let omega : I := Classical.choice inferInstance
    obtain ⟨v, hv, hbaseGL, hmarker, hparent⟩ :=
      D.exists_admissible_blockVector_regular_marker_avoidingOrbit_of_parentTop_bot
        H t admissible havoid jactive jparent omega (hsemi omega) (htop jparent hj) c
    refine ⟨v, hv, ?_, hparent⟩
    intro j
    by_cases hjactive : j = jactive
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
          (D.restrictComponent_kernelFactorsIn_componentBaseBlockImages (H jactive))
          (v + t jactive) omega hbase hmarker (hsemi omega)
    · exact D.restrictComponent_stabilizer_eq_bot_of_commonLocalGL_of_top_bot
        (H j) (v + t j) (hbaseGL j) (htop j hjactive)

/-- The all-prime induction step through an odd regular top: regularity is
required only for the odd rows. A separate block-fixing component retains
literal containment in the stabilizer of the supplied reference vector.

The local translated orbit-avoidance statement is the induction hypothesis;
all assumptions constructing the block system are explicit. -/
theorem exists_regular_translate_preserving_stabilizer_avoidingOrbit_of_regularOddTop
    [Fintype I] [Nonempty I]
    (D : ImprimitiveLinearActionData K L)
    (T : Subgroup K)
    (hTtop : (D.restrictComponent T).blockPerm.range = ⊥)
    (H : J → Subgroup K) (a b : I → W) (t : J → I → W)
    (havoid : ∀ i jparent c, ∃ w : W,
      (MulAction.stabilizer (D.componentBaseImageInCommonLocalGL T i) (w + b i) ≤
        MulAction.stabilizer (D.componentBaseImageInCommonLocalGL T i) (a i)) ∧
      (∀ j, MulAction.stabilizer
        (D.componentBaseImageInCommonLocalGL (H j) i) (w + t j i) = ⊥) ∧
      ¬ SameBlockOrbit
        (D.componentBaseImageInCommonLocalGL (H jparent) i)
        (w + t jparent i) c)
    (jactive : J)
    (htop : ∀ j, j ≠ jactive →
      (D.restrictComponent (H j)).blockPerm.range = ⊥)
    (hcard : Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range = Fintype.card I)
    (hodd : Odd (Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range))
    (hthree : 3 ≤ Nat.card
      (D.restrictComponent (H jactive)).blockPerm.range)
    (hsemi : IsSemiregularPermutationSubgroup
      (D.restrictComponent (H jactive)).blockPerm.range)
    (jparent : J) (c : I → W) :
    ∃ v : I → W,
      (MulAction.stabilizer (restrictedAmbient T) (v + b) ≤
        MulAction.stabilizer (restrictedAmbient T) a) ∧
      (∀ j, MulAction.stabilizer (restrictedAmbient (H j)) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit (restrictedAmbient (H jparent)) (v + t jparent) c := by
  let admissible : I → W → Prop := fun i w ↦
    MulAction.stabilizer (D.componentBaseImageInCommonLocalGL T i) (w + b i) ≤
      MulAction.stabilizer (D.componentBaseImageInCommonLocalGL T i) (a i)
  obtain ⟨v, hv, hregular, horbit⟩ :=
    D.exists_admissible_regular_translate_avoidingOrbit_of_regularOddTop
      H t admissible havoid jactive htop hcard hodd hthree hsemi jparent c
  exact ⟨v, D.restrictComponent_stabilizer_le_of_local_stabilizer_le_of_top_bot
    T (v + b) a hTtop hv, hregular, horbit⟩

end ImprimitiveLinearActionData

end LisiSabatini
