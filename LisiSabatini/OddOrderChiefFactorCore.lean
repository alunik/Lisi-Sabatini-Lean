import LisiSabatini.ChiefActionCore
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Minimal chief-factor input for the odd-order theorem

This proof-only module contains exactly the group-theoretic construction used
by the direct odd-order recursion: a nontrivial minimal normal subgroup of a
finite solvable odd-order group is a positive-dimensional elementary abelian
section in odd characteristic.

The historical abstract lifting interfaces remain in
`OddOrderReductionCore.lean`, outside the import closure of the unconditional
odd-order theorem.
-/

noncomputable section

namespace LisiSabatini

universe uG

/-- A minimal normal subgroup of a finite solvable odd-order group admits a
chief elementary-abelian section in odd characteristic.  Positivity of its
dimension follows from minimal normality via
`ChiefElementaryAbelianSection.dimension_pos`; it need not be reproved during
the coordinate construction. -/
theorem MinimalNormal.exists_oddChiefElementaryAbelianSection
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    {N : Subgroup G} (hN : MinimalNormal N)
    (hodd : Odd (Nat.card G)) :
    ∃ C : ChiefElementaryAbelianSection G,
      C.N = N ∧ C.r ≠ 2 := by
  letI : N.Normal := hN.normal
  have hcomm : IsMulCommutative N := hN.isMulCommutative
  obtain ⟨p, hp, hpg⟩ := hN.exists_prime_isPGroup hcomm
  have hpow : ∀ x : N, x ^ p = 1 :=
    hN.pow_prime_eq_one hcomm hp hpg
  letI : IsMulCommutative N := hcomm
  letI : Fact p.Prime := ⟨hp⟩
  letI zmodModule : Module (ZMod p) (Additive N) :=
    AddCommGroup.zmodModule fun x ↦ by
      simpa using congrArg Additive.ofMul (hpow x.toMul)
  letI finiteModule : Module.Finite (ZMod p) (Additive N) :=
    Module.Finite.of_finite
  letI freeModule : Module.Free (ZMod p) (Additive N) :=
    @Module.Free.of_divisionRing (ZMod p) (Additive N)
      (inferInstance) (inferInstance) zmodModule
  let d := Module.finrank (ZMod p) (Additive N)
  let basis : Module.Basis (Fin d) (ZMod p) (Additive N) :=
    @Module.finBasis (ZMod p) (Additive N)
      (inferInstance) (inferInstance) (inferInstance)
      zmodModule freeModule finiteModule
  let coordinates : Additive N ≃+ (Fin d → ZMod p) :=
    basis.equivFun.toAddEquiv
  have hp_dvd_N : p ∣ Nat.card N :=
    hpg.card_eq_or_dvd.resolve_left
      (ne_of_gt (N.one_lt_card_iff_ne_bot.mpr hN.ne_bot))
  have hp_dvd_G : p ∣ Nat.card G :=
    hp_dvd_N.trans N.card_subgroup_dvd_card
  let S : ElementaryAbelianSection G :=
    ElementaryAbelianSection.ofCoordinates N hN.normal p d hp coordinates
  let C : ChiefElementaryAbelianSection G :=
    ChiefElementaryAbelianSection.ofSection S hN
  exact ⟨C, rfl, hodd.ne_two_of_dvd_nat hp_dvd_G⟩

end LisiSabatini
