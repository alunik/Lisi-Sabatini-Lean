module

public import LisiSabatini.ChiefActionCore
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Elementary abelian coordinates for solvable chief factors

This construction works in every characteristic and is shared by the
odd-order recursion and the good solvable reduction.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped IsMulCommutative

universe uG

/-- A minimal normal subgroup of a finite solvable group is a chief
elementary-abelian section. There is no restriction on its characteristic. -/
theorem MinimalNormal.exists_chiefElementaryAbelianSection
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    {N : Subgroup G} (hN : MinimalNormal N) :
    ∃ C : ChiefElementaryAbelianSection G, C.N = N := by
  let : N.Normal := hN.normal
  have hcomm : IsMulCommutative N := hN.isMulCommutative
  obtain ⟨p, hp, hpg⟩ := hN.exists_prime_isPGroup hcomm
  have hpow : ∀ x : N, x ^ p = 1 :=
    hN.pow_prime_eq_one hcomm hp hpg
  let : IsMulCommutative N := hcomm
  let : Fact p.Prime := ⟨hp⟩
  let zmodModule : Module (ZMod p) (Additive N) :=
    AddCommGroup.zmodModule fun x ↦ by
      simpa using congrArg Additive.ofMul (hpow x.toMul)
  let finiteModule : Module.Finite (ZMod p) (Additive N) :=
    Module.Finite.of_finite
  let freeModule : Module.Free (ZMod p) (Additive N) :=
    @Module.Free.of_divisionRing (ZMod p) (Additive N)
      (inferInstance) (inferInstance) zmodModule
  let d := Module.finrank (ZMod p) (Additive N)
  let basis : Module.Basis (Fin d) (ZMod p) (Additive N) :=
    @Module.finBasis (ZMod p) (Additive N)
      (inferInstance) (inferInstance) zmodModule freeModule (inferInstance) finiteModule
  let coordinates : Additive N ≃+ (Fin d → ZMod p) :=
    basis.equivFun.toAddEquiv
  let S : ElementaryAbelianSection G :=
    ElementaryAbelianSection.ofCoordinates N hN.normal p d hp coordinates
  exact ⟨ChiefElementaryAbelianSection.ofSection S hN, rfl⟩


end LisiSabatini
