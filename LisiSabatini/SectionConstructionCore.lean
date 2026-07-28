module

public import LisiSabatini.ElementarySection
public import Mathlib.Algebra.Module.ZMod

/-!
# Constructing an elementary-abelian section from coordinates
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe u

variable {G : Type u} [Group G]

/-- Conjugation on a normal subgroup, transported through additive
coordinates. -/
def coordinateConjAddEquiv
    (N : Subgroup G) (hN : N.Normal)
    {r d : ℕ} (e : Additive N ≃+ (Fin d → ZMod r)) (g : G) :
    (Fin d → ZMod r) ≃+ (Fin d → ZMod r) :=
  (e.symm.trans ((MulEquiv.toAdditive) (normalConj N hN g))).trans e

@[simp]
theorem coordinateConjAddEquiv_apply
    (N : Subgroup G) (hN : N.Normal)
    {r d : ℕ} (e : Additive N ≃+ (Fin d → ZMod r)) (g : G) (n : N) :
    coordinateConjAddEquiv N hN e g (e (Additive.ofMul n)) =
      e (Additive.ofMul (normalConj N hN g n)) := by
  simp [coordinateConjAddEquiv]

/-- The transported additive automorphism, regarded as a `ZMod r`-linear
automorphism. -/
def coordinateConjLinearEquiv
    (N : Subgroup G) (hN : N.Normal)
    {r d : ℕ} (e : Additive N ≃+ (Fin d → ZMod r)) (g : G) :
    (Fin d → ZMod r) ≃ₗ[ZMod r] (Fin d → ZMod r) :=
  LinearEquiv.mk
    ((coordinateConjAddEquiv N hN e g).toAddMonoidHom.toZModLinearMap r)
    (coordinateConjAddEquiv N hN e g).symm
    (coordinateConjAddEquiv N hN e g).left_inv
    (coordinateConjAddEquiv N hN e g).right_inv

@[simp]
theorem coordinateConjLinearEquiv_apply
    (N : Subgroup G) (hN : N.Normal)
    {r d : ℕ} (e : Additive N ≃+ (Fin d → ZMod r)) (g : G)
    (v : Fin d → ZMod r) :
    coordinateConjLinearEquiv N hN e g v = coordinateConjAddEquiv N hN e g v :=
  rfl

/-- The coordinate representation of ambient conjugation. -/
def coordinateConjugation
    (N : Subgroup G) (hN : N.Normal)
    {r d : ℕ} (e : Additive N ≃+ (Fin d → ZMod r)) :
    G →* LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r) :=
  MonoidHom.mk'
    (fun g ↦ LinearMap.GeneralLinearGroup.ofLinearEquiv
      (coordinateConjLinearEquiv N hN e g)) (by
      intro g h
      apply (LinearMap.GeneralLinearGroup.generalLinearEquiv
        (ZMod r) (Fin d → ZMod r)).injective
      apply LinearEquiv.ext
      intro v
      let n : N := Additive.toMul (e.symm v)
      change coordinateConjAddEquiv N hN e (g * h) v =
        coordinateConjAddEquiv N hN e g (coordinateConjAddEquiv N hN e h v)
      rw [show v = e (Additive.ofMul n) by simp [n],
        coordinateConjAddEquiv_apply, coordinateConjAddEquiv_apply,
        coordinateConjAddEquiv_apply, normalConj_mul])

@[simp]
theorem coordinateConjugation_apply
    (N : Subgroup G) (hN : N.Normal)
    {r d : ℕ} (e : Additive N ≃+ (Fin d → ZMod r)) (g : G) (n : N) :
    coordinateConjugation N hN e g • e (Additive.ofMul n) =
      e (Additive.ofMul (normalConj N hN g n)) := by
  change coordinateConjLinearEquiv N hN e g (e (Additive.ofMul n)) = _
  rw [coordinateConjLinearEquiv_apply, coordinateConjAddEquiv_apply]

namespace ElementaryAbelianSection

/-- Build a complete elementary-abelian section from a normal subgroup and
additive coordinates. -/
def ofCoordinates
    (N : Subgroup G) (hN : N.Normal) (r d : ℕ) (hr : Nat.Prime r)
    (e : Additive N ≃+ (Fin d → ZMod r)) : ElementaryAbelianSection G where
  r := r
  d := d
  prime := hr
  N := N
  normal := hN
  coordinates := e
  exponent_eq_one := by
    intro n
    apply Additive.ofMul.injective
    apply e.injective
    change e (r • Additive.ofMul n) = e 0
    rw [map_nsmul, map_zero]
    ext i
    simp [nsmul_eq_mul, CharP.cast_eq_zero]
  conjugation := coordinateConjugation N hN e
  conjugation_apply := coordinateConjugation_apply N hN e

end ElementaryAbelianSection

end LisiSabatini
