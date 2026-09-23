module

public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Proof core for imprimitive linear actions

The monomial action data, local-orbit colour stabilizer, and induced action
of a point stabilizer used by the odd-order proof.
-/

@[expose] public section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

/-- Data witnessing that `H` acts imprimitively on `I → W`, with local
linear factors in `L`. -/
structure ImprimitiveLinearActionData
    (H : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) where
  blockPerm : H →* Equiv.Perm I
  blockLinear : H → I → L
  action_apply : ∀ (g : H) (x : I → W) (i : I),
    (g.1 • x) i = (blockLinear g i).1 • x ((blockPerm g).symm i)

/-- Two local vectors have the same block colour when they lie in the same
`L`-orbit. -/
def SameBlockOrbit
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) (u v : W) : Prop :=
  ∃ a : L, a • u = v

@[refl]
theorem sameBlockOrbit_refl
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) (u : W) :
    SameBlockOrbit L u u := by
  exact ⟨1, one_smul _ _⟩

@[symm]
theorem sameBlockOrbit_symm
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) {u v : W}
    (h : SameBlockOrbit L u v) :
    SameBlockOrbit L v u := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a⁻¹, ?_⟩
  rw [← ha, ← mul_smul]
  simp

@[trans]
theorem sameBlockOrbit_trans
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) {u v w : W}
    (huv : SameBlockOrbit L u v) (hvw : SameBlockOrbit L v w) :
    SameBlockOrbit L u w := by
  obtain ⟨a, ha⟩ := huv
  obtain ⟨b, hb⟩ := hvw
  refine ⟨b * a, ?_⟩
  rw [mul_smul, ha, hb]

/-- Permutations preserving the local-orbit colour of every coordinate. -/
def blockOrbitColorStabilizer
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) (x : I → W) :
    Subgroup (Equiv.Perm I) where
  carrier := {σ | ∀ i, SameBlockOrbit L (x (σ.symm i)) (x i)}
  one_mem' := by
    intro i
    exact sameBlockOrbit_refl L (x i)
  mul_mem' := by
    intro σ τ hσ hτ i
    change SameBlockOrbit L (x (τ.symm (σ.symm i))) (x i)
    exact sameBlockOrbit_trans L (hτ (σ.symm i)) (hσ i)
  inv_mem' := by
    intro σ hσ i
    change SameBlockOrbit L (x (σ i)) (x i)
    apply sameBlockOrbit_symm L
    simpa using hσ (σ i)

@[simp]
theorem mem_blockOrbitColorStabilizer_iff
    (L : Subgroup (LinearMap.GeneralLinearGroup R W))
    (x : I → W) (σ : Equiv.Perm I) :
    σ ∈ blockOrbitColorStabilizer L x ↔
      ∀ i, SameBlockOrbit L (x (σ.symm i)) (x i) :=
  Iff.rfl

/-- The permutation induced by an element of the point stabilizer. -/
def pointStabilizerBlockPerm
    {H : Subgroup (LinearMap.GeneralLinearGroup R (I → W))}
    {L : Subgroup (LinearMap.GeneralLinearGroup R W)}
    (D : ImprimitiveLinearActionData H L) (x : I → W) :
    MulAction.stabilizer H x →* Equiv.Perm I :=
  D.blockPerm.comp (MulAction.stabilizer H x).subtype

/-- A matrix fixing `x` induces a block permutation preserving every local
orbit colour of `x`. -/
theorem blockPerm_mem_colorStabilizer_of_mem_pointStabilizer
    {H : Subgroup (LinearMap.GeneralLinearGroup R (I → W))}
    {L : Subgroup (LinearMap.GeneralLinearGroup R W)}
    (D : ImprimitiveLinearActionData H L) (x : I → W)
    (g : MulAction.stabilizer H x) :
    D.blockPerm g.1 ∈ blockOrbitColorStabilizer L x := by
  intro i
  refine ⟨D.blockLinear g.1 i, ?_⟩
  have hfix : g.1.1 • x = x :=
    MulAction.mem_stabilizer_iff.mp g.2
  have hi := congrFun hfix i
  rw [D.action_apply] at hi
  exact hi

end LisiSabatini
