import LisiSabatini.AffineTwoBaseOrbitAvoidance
import LisiSabatini.TwoOrbitAvoidingLinearEquiv

/-!
# Coordinate invariance of diagonal affine two-orbit avoidance

Changing coordinates on a module conjugates its diagonal action on two
copies by the product coordinate equivalence.  Consequently the recursively
stable affine two-base invariant is intrinsic to the linear representation.
-/

noncomputable section

namespace LisiSabatini

universe uI uV uW

namespace NCASLinearEquiv

variable {r : ℕ} {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module (ZMod r) V]
variable [AddCommGroup W] [Module (ZMod r) W]

/-- Diagonalization commutes with a linear change of coordinates. -/
@[simp]
theorem diagonalGeneralLinearHom_conjugation
    (e : V ≃ₗ[ZMod r] W)
    (g : LinearMap.GeneralLinearGroup (ZMod r) V) :
    diagonalGeneralLinearHom (ZMod r) W (conjugation e g) =
      conjugation (e.prodCongr e)
        (diagonalGeneralLinearHom (ZMod r) V g) := by
  ext z <;> rfl

/-- The mapped diagonal image of a conjugated subgroup is the conjugate,
on the doubled module, of the original diagonal image. -/
theorem map_conjugation_map_diagonalGeneralLinearHom
    (e : V ≃ₗ[ZMod r] W)
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    (A.map (conjugation e).toMonoidHom).map
        (diagonalGeneralLinearHom (ZMod r) W) =
      (A.map (diagonalGeneralLinearHom (ZMod r) V)).map
        (conjugation (e.prodCongr e)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- The strong diagonal affine two-orbit invariant for a conjugated common
action implies the invariant for the original action. -/
theorem commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_conjugate
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (hconj :
      CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
        r W (conjugateSubgroup e K)) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI} r V K := by
  intro I _ p hp hinj hcross H hHnormal hHp
  let Hconj : I → Subgroup (conjugateSubgroup e K) :=
    fun i ↦ conjugateInternalSubgroup e K (H i)
  have hconjFamily :=
    hconj p hp hinj hcross Hconj
      (fun i ↦ conjugateInternalSubgroup_normal e K (H i) (hHnormal i))
      (fun i ↦ conjugateInternalSubgroup_isPGroup e K (H i) (hHp i))
  have hambient :
      (fun i ↦
          ((Hconj i).map (conjugateSubgroup e K).subtype).map
            (diagonalGeneralLinearHom (ZMod r) W)) =
        (fun i ↦
          (((H i).map K.subtype).map
              (diagonalGeneralLinearHom (ZMod r) V)).map
            (conjugation (e.prodCongr e)).toMonoidHom) := by
    funext i
    rw [conjugateInternalSubgroup_map_subtype]
    exact
      map_conjugation_map_diagonalGeneralLinearHom e
        ((H i).map K.subtype)
  rw [hambient] at hconjFamily
  exact
    (twoOrbitAvoidingCommonRegularTranslates_map_conjugation_iff
      (e.prodCongr e)
      (fun i ↦
        ((H i).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod r) V))).mp hconjFamily

/-- **The strong diagonal affine two-orbit invariant is invariant under a
linear change of coordinates.** -/
theorem commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_conjugate_iff
    (e : V ≃ₗ[ZMod r] W)
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
        r W (conjugateSubgroup e K) ↔
      CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI} r V K := by
  constructor
  · exact commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_conjugate e K
  · intro hK
    have hback :
        CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI} r V
          (conjugateSubgroup e.symm (conjugateSubgroup e K)) := by
      rw [conjugateSubgroup_symm_conjugateSubgroup]
      exact hK
    exact
      @commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_conjugate.{uI, uW, uV}
        r W V inferInstance inferInstance inferInstance inferInstance
        e.symm (conjugateSubgroup e K) hback

end NCASLinearEquiv

end LisiSabatini
