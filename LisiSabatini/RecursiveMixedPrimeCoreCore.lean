import LisiSabatini.NormalComponentOrbitAvoidingCore
import LisiSabatini.PrimitiveImprimitiveComponentsCore
import LisiSabatini.ImprimitiveBundleMarkerCore
import LisiSabatini.ImprimitiveBundleGraph

/-!
# Core mixed prime-core one-orbit frontier

This proof dependency contains only the active-top composition lemmas used
by the direct dimension induction.  The old quasiprimitive-leaf record,
generic recursive wrappers, labelled certificates, and obstruction examples
remain outside the proof closure.
-/

noncomputable section

namespace LisiSabatini

universe uI uJ uR uW

/-! ## Splitting the marker and external-orbit roles -/

variable {I : Type uI} {J : Type uJ} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- One local forbidden orbit per block suffices when the externally
forbidden component has trivial top image.

At `omega`, the local orbit is spent on the external target.  At every other
block it is spent on the transported marker value for `jmark`.  Triviality
of the parent top means that a hypothetical full parent-orbit witness must
already be visible at `omega`. -/
theorem exists_blockVector_commonBaseRegular_uniqueBundleMarker_avoidingOrbit_of_parentTop_bot
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (havoid : ∀ i : I,
      OrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i))
    (t : J → I → W) (jmark jparent : J) (omega : I)
    (hsemiMark : IsSemiregularAt
      (D.restrictComponent (H jmark)).blockPerm.range omega)
    (hparentTop :
      (D.restrictComponent (H jparent)).blockPerm.range = ⊥)
    (c : I → W) :
    ∃ v : I → W,
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
  obtain ⟨marker, hmarkerRegular, hmarkerAvoid⟩ :=
    havoid omega jparent (fun j ↦ t j omega) (c omega)
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
    exact havoid i jmark (fun j ↦ t j i) (markerForbidden i)
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

/-- The one-orbit property obtained after one primitive imprimitive layer
for every forbidden component except the possible active-top component. -/
def OrbitAvoidingCommonRegularTranslatesAwayFrom
    (jactive : J)
    (H : J → Subgroup (LinearMap.GeneralLinearGroup R (I → W))) : Prop :=
  ∀ jparent, jparent ≠ jactive → ∀ (t : J → I → W) (c : I → W),
    ∃ v : I → W,
      (∀ j, MulAction.stabilizer (H j) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit (H jparent) (v + t jparent) c

/-- If `jactive` is the only component with possibly nontrivial top, local
one-orbit avoidance proves full one-orbit avoidance away from `jactive`. -/
theorem orbitAvoidingCommonRegularTranslatesAwayFrom_of_imprimitive_atMostOneTop
    (D : ImprimitiveLinearActionData K L)
    (H : J → Subgroup K)
    (havoid : ∀ i : I,
      OrbitAvoidingCommonRegularTranslates
        (fun j ↦ D.componentBaseImageInCommonLocalGL (H j) i))
    (jactive : J) (omega : I)
    (htop : ∀ j, j ≠ jactive →
      (D.restrictComponent (H j)).blockPerm.range = ⊥)
    (hsemi : ∀ j, IsSemiregularAt
      (D.restrictComponent (H j)).blockPerm.range omega) :
    OrbitAvoidingCommonRegularTranslatesAwayFrom jactive
      (fun j ↦ restrictedAmbient (H j)) := by
  intro jparent hj t c
  obtain ⟨v, hbaseGL, hmarker, hparent⟩ :=
    D.exists_blockVector_commonBaseRegular_uniqueBundleMarker_avoidingOrbit_of_parentTop_bot
      H havoid t jactive jparent omega (hsemi jactive) (htop jparent hj) c
  refine ⟨v, ?_, hparent⟩
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
        (D.restrictComponent_kernelFactorsIn_componentBaseBlockImages
          (H jactive))
        (v + t jactive) omega hbase hmarker (hsemi jactive)
  · exact D.restrictComponent_stabilizer_eq_bot_of_commonLocalGL_of_top_bot
      (H j) (v + t j) (hbaseGL j) (htop j hjactive)

/-- The exact unresolved one-orbit obligation after distributing the two
roles for top-trivial components.  It asks only for the unique component
whose top image is nontrivial. -/
def ActiveTopOrbitAvoidanceResidual
    (H : J → Subgroup K) (jactive : J) : Prop :=
  ∀ (t : J → I → W) (c : I → W),
    ∃ v : I → W,
      (∀ j, MulAction.stabilizer
        (restrictedAmbient (H j)) (v + t j) = ⊥) ∧
      ¬ SameBlockOrbit (restrictedAmbient (H jactive))
        (v + t jactive) c

/-- Away-from-active avoidance plus the active residual is exactly enough
for unrestricted one-orbit avoidance. -/
theorem orbitAvoidingCommonRegularTranslates_of_awayFrom_of_activeResidual
    (H : J → Subgroup K) (jactive : J)
    (haway : OrbitAvoidingCommonRegularTranslatesAwayFrom jactive
      (fun j ↦ restrictedAmbient (H j)))
    (hactive : ActiveTopOrbitAvoidanceResidual H jactive) :
    OrbitAvoidingCommonRegularTranslates
      (fun j ↦ restrictedAmbient (H j)) := by
  intro jparent t c
  by_cases hj : jparent = jactive
  · subst jparent
    exact hactive t c
  · exact haway jparent hj t c

end ImprimitiveLinearActionData

end LisiSabatini
