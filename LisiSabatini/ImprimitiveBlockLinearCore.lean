import LisiSabatini.ImprimitiveReductionCore

/-!
# The block-factor cocycle

The local factors of an imprimitive linear action form a crossed
homomorphism.  Keeping this elementary consequence of `action_apply` below
the component and bundle layers lets every restriction to a permutation
kernel reuse the same proof.
-/

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

namespace ImprimitiveLinearActionData

variable {H : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- The local factor of the identity is the identity. -/
@[simp]
theorem blockLinear_one
    (D : ImprimitiveLinearActionData H L) (i : I) :
    D.blockLinear 1 i = 1 := by
  apply Subtype.ext
  ext w
  let x : I → W := fun _ ↦ w
  have hi := D.action_apply (1 : H) x i
  simpa [x] using hi.symm

/-- The local factors obey the monomial cocycle law. -/
theorem blockLinear_mul
    (D : ImprimitiveLinearActionData H L) (g h : H) (i : I) :
    D.blockLinear (g * h) i =
      D.blockLinear g i * D.blockLinear h ((D.blockPerm g).symm i) := by
  apply Subtype.ext
  ext w
  let x : I → W := fun _ ↦ w
  have hgh := D.action_apply (g * h) x i
  have hg := D.action_apply g (h.1 • x) i
  have hh := D.action_apply h x ((D.blockPerm g).symm i)
  change
    (D.blockLinear (g * h) i : L).1 • w =
      ((D.blockLinear g i *
        D.blockLinear h ((D.blockPerm g).symm i) : L) :
          LinearMap.GeneralLinearGroup R W) • w
  calc
    (D.blockLinear (g * h) i : L).1 • w =
        ((g * h).1 • x) i := by rw [hgh]
    _ = (g.1 • (h.1 • x)) i := congrFun (mul_smul g.1 h.1 x) i
    _ = (D.blockLinear g i).1 •
        ((h.1 • x) ((D.blockPerm g).symm i)) := hg
    _ = (D.blockLinear g i).1 •
        ((D.blockLinear h ((D.blockPerm g).symm i)).1 • w) := by rw [hh]
    _ = ((D.blockLinear g i *
        D.blockLinear h ((D.blockPerm g).symm i) : L) :
          LinearMap.GeneralLinearGroup R W) • w := by
      exact (mul_smul (D.blockLinear g i).1
        (D.blockLinear h ((D.blockPerm g).symm i)).1 w).symm

end ImprimitiveLinearActionData

end LisiSabatini
