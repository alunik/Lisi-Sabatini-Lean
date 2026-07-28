module

public import LisiSabatini.OrbitAvoidingPaletteCore
public import LisiSabatini.NCASLinearEquiv

/-!
# Orbit-avoiding normal-component synchronization

The imprimitive bundle-marker argument needs more than one simultaneous
regular affine translate: one distinguished component must also avoid one
prescribed orbit colour.  This file packages that recursive hypothesis in a
representation-independent form parallel to
`NormalComponentAffineSynchronizationOn`.

The stronger predicate implies ordinary NCAS, is invariant under linear
equivalence, and follows uniformly from fixed-point-freeness of all active
normal prime components when the finite ambient module has odd nontrivial
cardinality.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uJ uV uW

/-- Representation-independent orbit-avoiding normal-component
synchronization on a `ZMod r`-module.

For every family occurring in NCAS—normal `p`-subgroups at injectively
labelled odd primes different from the module characteristic—the concrete
ambient images satisfy one-orbit-avoiding common translated regularity. -/
def NormalComponentOrbitAvoidingSynchronizationOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {J : Type uJ} [Fintype J] (p : J → ℕ),
    (∀ j, Nat.Prime (p j)) →
    Function.Injective p →
    (∀ j, p j ≠ 2) →
    (∀ j, p j ≠ r) →
    ∀ H : J → Subgroup K,
      (∀ j, (H j).Normal) →
      (∀ j, IsPGroup (p j) (H j)) →
      OrbitAvoidingCommonRegularTranslates
        (fun j ↦ (H j).map K.subtype)

/-- Coordinate-space specialization of orbit-avoiding normal-component
synchronization. -/
def NormalComponentOrbitAvoidingSynchronization
    (r d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop :=
  NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r
    (Fin d → ZMod r) K

/-- The coordinate predicate is definitionally the arbitrary-module
predicate on the standard coordinate space. -/
theorem normalComponentOrbitAvoidingSynchronization_iff_on
    (r d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    NormalComponentOrbitAvoidingSynchronization.{uJ} r d K ↔
      NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r
        (Fin d → ZMod r) K :=
  Iff.rfl

namespace NormalComponentOrbitAvoidingSynchronizationOn

variable {r : ℕ} {V : Type uV}
variable [AddCommGroup V] [Module (ZMod r) V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}

/-- Orbit-avoiding synchronization implies ordinary NCAS.

For a nonempty family, specialize orbit avoidance at any distinguished
component and forbidden colour `0`, then retain its simultaneous regularity
conclusion.  For an empty family, the zero vector is a witness directly. -/
theorem normalComponentAffineSynchronization
    (h : NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r V K) :
    NormalComponentAffineSynchronizationOn.{uJ} r V K := by
  intro J _ p hp hinj hpTwo hcross H hHnormal hHp t
  by_cases hJ : Nonempty J
  · letI : Nonempty J := hJ
    obtain ⟨v, hregular, _havoid⟩ :=
      h p hp hinj hpTwo hcross H hHnormal hHp
        (Classical.choice hJ) t 0
    exact ⟨v, hregular⟩
  · refine ⟨0, fun j ↦ ?_⟩
    exact (hJ ⟨j⟩).elim

end NormalComponentOrbitAvoidingSynchronizationOn

namespace NCASLinearEquiv

variable {r : ℕ} {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module (ZMod r) V]
variable [AddCommGroup W] [Module (ZMod r) W]

/-! ## Linear-equivalence invariance -/

/-- The orbit relation for a linear subgroup is invariant under conjugating
the group and transporting both vectors through a linear equivalence. -/
theorem sameBlockOrbit_map_conjugation_iff
    (e : V ≃ₗ[ZMod r] W)
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (x y : V) :
    SameBlockOrbit (A.map (conjugation e).toMonoidHom) (e x) (e y) ↔
      SameBlockOrbit A x y := by
  let c := conjugation e
  constructor
  · rintro ⟨g, hg⟩
    let a : A := (c.subgroupMap A).symm g
    have hag : c.subgroupMap A a = g := by
      change c.subgroupMap A ((c.subgroupMap A).symm g) = g
      exact (c.subgroupMap A).apply_symm_apply g
    refine ⟨a, ?_⟩
    apply e.injective
    calc
      e (a.1 • x) = c a.1 • e x :=
        (conjugation_smul e a.1 x).symm
      _ = g.1 • e x := by
        exact congrArg
          (fun h : A.map c.toMonoidHom ↦ h.1 • e x) hag
      _ = e y := hg
  · rintro ⟨a, ha⟩
    refine ⟨(conjugation e).subgroupMap A a, ?_⟩
    change conjugation e a.1 • e x = e y
    rw [conjugation_smul]
    exact congrArg e ha

/-- One-orbit-avoiding common translated regularity is invariant under a
simultaneous linear change of coordinates. -/
theorem orbitAvoidingCommonRegularTranslates_map_conjugation_iff
    {J : Type uJ}
    (e : V ≃ₗ[ZMod r] W)
    (A : J → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    OrbitAvoidingCommonRegularTranslates
        (fun j ↦ (A j).map (conjugation e).toMonoidHom) ↔
      OrbitAvoidingCommonRegularTranslates A := by
  constructor
  · intro h j₀ t c
    obtain ⟨w, hregular, havoid⟩ :=
      h j₀ (fun j ↦ e (t j)) (e c)
    refine ⟨e.symm w, ?_, ?_⟩
    · intro j
      apply
        (stabilizer_map_conjugation_eq_bot_iff e (A j)
          (e.symm w + t j)).mp
      simpa using hregular j
    · intro horbit
      apply havoid
      have hmapped :=
        (sameBlockOrbit_map_conjugation_iff e (A j₀)
          (e.symm w + t j₀) c).mpr horbit
      simpa using hmapped
  · intro h j₀ t c
    obtain ⟨v, hregular, havoid⟩ :=
      h j₀ (fun j ↦ e.symm (t j)) (e.symm c)
    refine ⟨e v, ?_, ?_⟩
    · intro j
      have htransport :=
        (stabilizer_map_conjugation_eq_bot_iff e (A j)
          (v + e.symm (t j))).mpr (hregular j)
      simpa using htransport
    · intro horbit
      apply havoid
      have hmapped : SameBlockOrbit
          ((A j₀).map (conjugation e).toMonoidHom)
          (e (v + e.symm (t j₀))) (e (e.symm c)) := by
        simpa using horbit
      exact
        (sameBlockOrbit_map_conjugation_iff e (A j₀)
          (v + e.symm (t j₀)) (e.symm c)).mp hmapped

/-- Orbit-avoiding synchronization for the conjugated common action implies
orbit-avoiding synchronization for the original action. -/
theorem normalComponentOrbitAvoidingSynchronizationOn_of_conjugate
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (hconj : NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r W
      (conjugateSubgroup e K)) :
    NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r V K := by
  intro J _ p hp hinj hpTwo hcross H hHnormal hHp
  let Hconj : J → Subgroup (conjugateSubgroup e K) :=
    fun j ↦ conjugateInternalSubgroup e K (H j)
  have hconjFamily :=
    hconj p hp hinj hpTwo hcross Hconj
      (fun j ↦ conjugateInternalSubgroup_normal e K (H j) (hHnormal j))
      (fun j ↦ conjugateInternalSubgroup_isPGroup e K (H j) (hHp j))
  have hambient :
      (fun j ↦ (Hconj j).map (conjugateSubgroup e K).subtype) =
        (fun j ↦ ((H j).map K.subtype).map
          (conjugation e).toMonoidHom) := by
    funext j
    exact conjugateInternalSubgroup_map_subtype e K (H j)
  rw [hambient] at hconjFamily
  exact
    (orbitAvoidingCommonRegularTranslates_map_conjugation_iff e
      (fun j ↦ (H j).map K.subtype)).mp hconjFamily

/-- **Orbit-avoiding NCAS is invariant under a linear change of
coordinates.** -/
theorem normalComponentOrbitAvoidingSynchronizationOn_conjugate_iff
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r W
        (conjugateSubgroup e K) ↔
      NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r V K := by
  constructor
  · exact normalComponentOrbitAvoidingSynchronizationOn_of_conjugate e K
  · intro hK
    have hback : NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r V
        (conjugateSubgroup e.symm (conjugateSubgroup e K)) := by
      rw [conjugateSubgroup_symm_conjugateSubgroup]
      exact hK
    exact
      @normalComponentOrbitAvoidingSynchronizationOn_of_conjugate.{uJ, uW, uV}
        r W V inferInstance inferInstance inferInstance inferInstance
        e.symm (conjugateSubgroup e K) hback

end NCASLinearEquiv

end LisiSabatini
