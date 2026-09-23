module

public import LisiSabatini.NormalComponentReductionCore
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Linear-equivalence invariance of NCAS

Normal-component affine synchronization is intrinsic to the linear action:
it does not depend on a choice of coordinates.  This file transports the
common action, its internal normal prime components, affine translations,
and stabilizer regularity along a `ZMod r`-linear equivalence.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uV uW

variable {r : ℕ}
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module (ZMod r) V]
variable [AddCommGroup W] [Module (ZMod r) W]

namespace NCASLinearEquiv

abbrev conjugation (e : V ≃ₗ[ZMod r] W) :
    LinearMap.GeneralLinearGroup (ZMod r) V ≃*
      LinearMap.GeneralLinearGroup (ZMod r) W :=
  LinearMap.GeneralLinearGroup.congrLinearEquiv e

@[simp]
theorem conjugation_smul (e : V ≃ₗ[ZMod r] W)
    (g : LinearMap.GeneralLinearGroup (ZMod r) V) (v : V) :
    conjugation e g • e v = e (g • v) := by
  change e (g.toLinearEquiv (e.symm (e v))) =
    e (g.toLinearEquiv v)
  rw [e.symm_apply_apply]

/-- The common linear group after changing coordinates by `e`. -/
abbrev conjugateSubgroup (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod r) W) :=
  K.map (conjugation e).toMonoidHom

/-- The canonical isomorphism from an action group to its conjugate. -/
def subgroupEquiv (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    K ≃* conjugateSubgroup e K :=
  (conjugation e).subgroupMap K

@[simp]
theorem subgroupEquiv_coe (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) (g : K) :
    ((subgroupEquiv e K g : conjugateSubgroup e K) :
      LinearMap.GeneralLinearGroup (ZMod r) W) =
        conjugation e g :=
  rfl

/-- An internal subgroup transported through the common-action
isomorphism. -/
def conjugateInternalSubgroup (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (H : Subgroup K) : Subgroup (conjugateSubgroup e K) :=
  H.map (subgroupEquiv e K).toMonoidHom

/-- Internal normality is preserved by coordinate transport. -/
theorem conjugateInternalSubgroup_normal (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (H : Subgroup K) (hH : H.Normal) :
    (conjugateInternalSubgroup e K H).Normal :=
  hH.map (subgroupEquiv e K).toMonoidHom
    (subgroupEquiv e K).surjective

/-- The prime-group property is preserved by coordinate transport. -/
theorem conjugateInternalSubgroup_isPGroup (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    {p : ℕ} (H : Subgroup K) (hH : IsPGroup p H) :
    IsPGroup p (conjugateInternalSubgroup e K H) :=
  hH.map (subgroupEquiv e K).toMonoidHom

/-- Mapping a transported internal subgroup into the ambient general linear
group is the same as conjugating its original ambient image. -/
theorem conjugateInternalSubgroup_map_subtype
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (H : Subgroup K) :
    (conjugateInternalSubgroup e K H).map
        (conjugateSubgroup e K).subtype =
      (H.map K.subtype).map (conjugation e).toMonoidHom := by
  rw [conjugateInternalSubgroup, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-! ## Stabilizer transport -/

/-- Trivial stabilizers are invariant under simultaneously conjugating the
acting subgroup and transporting the vector by `e`. -/
theorem stabilizer_map_conjugation_eq_bot_iff
    (e : V ≃ₗ[ZMod r] W)
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (x : V) :
    MulAction.stabilizer
        (A.map (conjugation e).toMonoidHom) (e x) = ⊥ ↔
      MulAction.stabilizer A x = ⊥ := by
  let c := conjugation e
  constructor
  · intro hmap
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    let cg : A.map c.toMonoidHom := c.subgroupMap A g
    have hcg : cg ∈ MulAction.stabilizer
        (A.map c.toMonoidHom) (e x) := by
      apply MulAction.mem_stabilizer_iff.mpr
      have hfix : g.1 • x = x :=
        MulAction.mem_stabilizer_iff.mp hg
      change c g.1 • e x = e x
      rw [conjugation_smul]
      exact congrArg e hfix
    rw [hmap] at hcg
    have hcgeq : cg = 1 := Subgroup.mem_bot.mp hcg
    apply Subgroup.mem_bot.mpr
    apply (c.subgroupMap A).injective
    rw [map_one]
    exact hcgeq
  · intro hsource
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    let a : A := (c.subgroupMap A).symm g
    have hag : c.subgroupMap A a = g := by
      change c.subgroupMap A ((c.subgroupMap A).symm g) = g
      exact (c.subgroupMap A).apply_symm_apply g
    have ha : a ∈ MulAction.stabilizer A x := by
      apply MulAction.mem_stabilizer_iff.mpr
      apply e.injective
      have hfix : g.1 • e x = e x :=
        MulAction.mem_stabilizer_iff.mp hg
      calc
        e (a.1 • x) = c a.1 • e x :=
          (conjugation_smul e a.1 x).symm
        _ = g.1 • e x := by
          exact congrArg (fun h : A.map c.toMonoidHom ↦ h.1 • e x) hag
        _ = e x := hfix
    rw [hsource] at ha
    have haone : a = 1 := Subgroup.mem_bot.mp ha
    apply Subgroup.mem_bot.mpr
    change g = (1 : A.map c.toMonoidHom)
    rw [← hag, haone]
    exact map_one _

/-! ## NCAS transport -/

/-- Synchronization for the conjugated common action implies
synchronization for the original action.  Internal normal `p`-subgroups are
mapped through the induced common-group isomorphism, translations are sent
through `e`, and the resulting regular point is pulled back through
`e.symm`. -/
theorem normalComponentAffineSynchronizationOn_of_conjugate
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (hconj : NormalComponentAffineSynchronizationOn.{uI} r W
      (conjugateSubgroup e K)) :
    NormalComponentAffineSynchronizationOn.{uI} r V K := by
  intro I _ p hp hinj hpTwo hcross H hHnormal hHp t
  let Hconj : I → Subgroup (conjugateSubgroup e K) :=
    fun i ↦ conjugateInternalSubgroup e K (H i)
  obtain ⟨w, hw⟩ := hconj p hp hinj hpTwo hcross Hconj
    (fun i ↦ conjugateInternalSubgroup_normal e K (H i) (hHnormal i))
    (fun i ↦ conjugateInternalSubgroup_isPGroup e K (H i) (hHp i))
    (fun i ↦ e (t i))
  refine ⟨e.symm w, fun i ↦ ?_⟩
  apply
    (stabilizer_map_conjugation_eq_bot_iff e
      ((H i).map K.subtype) (e.symm w + t i)).mp
  have hwi := hw i
  change MulAction.stabilizer
      ((conjugateInternalSubgroup e K (H i)).map
        (conjugateSubgroup e K).subtype)
      (w + e (t i)) = ⊥ at hwi
  rw [conjugateInternalSubgroup_map_subtype] at hwi
  simpa using hwi

/-- Conjugating a subgroup and then conjugating back by `e.symm` recovers
the original subgroup. -/
@[simp]
theorem conjugateSubgroup_symm_conjugateSubgroup
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    conjugateSubgroup e.symm (conjugateSubgroup e K) = K := by
  change
    (K.map (conjugation e).toMonoidHom).map
        (conjugation e.symm).toMonoidHom = K
  change
    (K.map (conjugation e).toMonoidHom).map
        (conjugation e).symm.toMonoidHom = K
  exact
    (Subgroup.map_symm_eq_iff_map_eq
      (H := K.map (conjugation e).toMonoidHom)
      (e := conjugation e) K).mpr rfl

/-- **NCAS is invariant under a linear change of coordinates.** -/
theorem normalComponentAffineSynchronizationOn_conjugate_iff
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    NormalComponentAffineSynchronizationOn.{uI} r W
        (conjugateSubgroup e K) ↔
      NormalComponentAffineSynchronizationOn.{uI} r V K := by
  constructor
  · exact normalComponentAffineSynchronizationOn_of_conjugate e K
  · intro hK
    have hback : NormalComponentAffineSynchronizationOn.{uI} r V
        (conjugateSubgroup e.symm (conjugateSubgroup e K)) := by
      rw [conjugateSubgroup_symm_conjugateSubgroup]
      exact hK
    exact
      @normalComponentAffineSynchronizationOn_of_conjugate.{uI, uW, uV}
        r W V inferInstance inferInstance inferInstance inferInstance
        e.symm (conjugateSubgroup e K) hback

/-! ## Flattened-coordinate to block-function reindexing -/

/-- The standard linear equivalence between a vector indexed by
`Fin (b * d)` and a `b`-tuple of `d`-dimensional blocks. -/
def finProductCurryLinearEquiv (r b d : ℕ) :
    (Fin (b * d) → ZMod r) ≃ₗ[ZMod r]
      (Fin b → Fin d → ZMod r) :=
  (LinearEquiv.piCongrLeft (ZMod r)
      (fun _ : Fin b × Fin d ↦ ZMod r)
      (finProdFinEquiv.symm)).trans
    (LinearEquiv.curry (ZMod r) (ZMod r) (Fin b) (Fin d))

/-- NCAS may be checked after reshaping flattened coordinates into a block
function.  The common subgroup on the block side is the corresponding
conjugate action. -/
theorem normalComponentAffineSynchronization_finProductCurry_iff
    (r b d : ℕ)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r)
      (Fin (b * d) → ZMod r))) :
    NormalComponentAffineSynchronizationOn.{uI} r
        (Fin b → Fin d → ZMod r)
        (conjugateSubgroup (finProductCurryLinearEquiv r b d) K) ↔
      NormalComponentAffineSynchronization.{uI} r (b * d) K :=
  (normalComponentAffineSynchronizationOn_conjugate_iff
      (finProductCurryLinearEquiv r b d) K).trans
    (normalComponentAffineSynchronization_iff_on r (b * d) K).symm

end NCASLinearEquiv

end LisiSabatini
