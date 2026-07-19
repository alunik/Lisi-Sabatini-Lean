import LisiSabatini.ChiefActionCore
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.IntegralDomain
import Mathlib.RingTheory.LittleWedderburn
import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Homogeneous restrictions of quasiprimitive linear actions

A representation is homogeneous when its module is semisimple and all of
its simple constituents are isomorphic.  Quasiprimitivity asks for this of
the restriction to every normal subgroup.

The main lemma in this file is the elementary cross-characteristic engine
needed by the prime-core programme: a faithful homogeneous representation
of a finite commuting group is fixed-point-free away from zero.  Maschke's
theorem supplies semisimplicity, while isotypicity forces the fixed space of
each element to be either zero or the whole module.

For later structural work we also record that a finite faithful commuting
fixed-point-free linear group is cyclic.  The proof passes to a simple
constituent, embeds the group in its Schur endomorphism division ring, and
uses Wedderburn's little theorem.
-/

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

namespace Representation

/-- A representation is homogeneous if it is semisimple and isotypic. -/
def IsHomogeneous
    {k A V : Type*} [CommRing k] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k A V) : Prop :=
  IsSemisimpleModule k[A] rho.asModule ∧
    IsIsotypic k[A] rho.asModule

/-- A representation is quasiprimitive if it is irreducible and its
restriction to every normal subgroup is homogeneous. -/
def IsQuasiprimitive
    {k A V : Type*} [Field k] [Group A]
    [AddCommGroup V] [Module k V]
    (rho : Representation k A V) : Prop :=
  rho.IsIrreducible ∧
    ∀ H : Subgroup A, H.Normal → IsHomogeneous (rho.comp H.subtype)

end Representation

/-- The tautological representation of a concrete subgroup of a general
linear group. -/
def linearSubgroupRepresentation
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (K : Subgroup (LinearMap.GeneralLinearGroup R V)) :
    Representation R K V :=
  (Units.coeHom (Module.End R V)).comp K.subtype

/-- The tautological representation of a concrete linear subgroup is
faithful. -/
theorem linearSubgroupRepresentation_faithful
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (K : Subgroup (LinearMap.GeneralLinearGroup R V)) :
    Function.Injective (linearSubgroupRepresentation K) := by
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  exact hxy

/-- Field-instance-free quasiprimitivity for the concrete `ZMod r` actions
used by the project.  The first field records ordinary irreducibility; the
second records homogeneous restriction to every normal subgroup. -/
def IsQuasiprimitiveLinearAction
    (r d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop :=
  IsIrreducibleLinearAction r d K ∧
    ∀ H : Subgroup K, H.Normal →
      Representation.IsHomogeneous
        ((linearSubgroupRepresentation K).comp H.subtype)

/-- A faithful isotypic representation of a finite commuting group in
cross characteristic is fixed-point-free away from zero.

The fixed space of `g` is a fully invariant `k[A]`-submodule: every module
endomorphism commutes with the action of `g`.  Maschke's theorem and
isotypicity make this fixed space bottom or top.  The top case contradicts
faithfulness for a nonidentity `g`. -/
theorem fixedPointFree_of_faithful_isIsotypic_of_commuting
    {k A V : Type*} [Field k] [Group A] [Finite A]
    [AddCommGroup V] [Module k V]
    [NeZero (Nat.card A : k)]
    (rho : Representation k A V)
    (hiso : IsIsotypic k[A] rho.asModule)
    (hcomm : ∀ a b : A, Commute a b)
    (hfaith : Function.Injective rho) :
    ∀ g : A, g ≠ 1 → ∀ x : V, rho g x = x → x = 0 := by
  intro g hg x hx
  let N : Submodule k[A] rho.asModule :=
    { carrier := {y | MonoidAlgebra.of k A g • y = y}
      zero_mem' := by simp
      add_mem' := by
        intro y z hy hz
        change MonoidAlgebra.of k A g • y = y at hy
        change MonoidAlgebra.of k A g • z = z at hz
        change MonoidAlgebra.of k A g • (y + z) = y + z
        rw [smul_add, hy, hz]
      smul_mem' := by
        intro c y hy
        change MonoidAlgebra.of k A g • y = y at hy
        change MonoidAlgebra.of k A g • (c • y) = c • y
        rw [← mul_smul, (MonoidAlgebra.of_commute (hcomm g) c).eq,
          mul_smul, hy] }
  have hNfull : N.IsFullyInvariant := by
    intro f y hy
    change MonoidAlgebra.of k A g • f y = f y
    rw [← f.map_smul]
    exact congrArg f hy
  haveI : IsSemisimpleModule k[A] rho.asModule := inferInstance
  have hN : N = ⊥ ∨ N = ⊤ :=
    isIsotypic_iff_isFullyInvariant_imp_bot_or_top.mp hiso N hNfull
  rcases hN with hN | hN
  · have hxN : rho.asModuleEquiv.symm x ∈ N := by
      change MonoidAlgebra.of k A g • rho.asModuleEquiv.symm x =
        rho.asModuleEquiv.symm x
      rw [← rho.asModuleEquiv_symm_map_rho]
      exact congrArg rho.asModuleEquiv.symm hx
    rw [hN] at hxN
    exact rho.asModuleEquiv.symm.injective (by simpa using hxN)
  · exfalso
    apply hg
    apply hfaith
    apply LinearMap.ext
    intro y
    have hyN : rho.asModuleEquiv.symm y ∈ N := by
      rw [hN]
      trivial
    change MonoidAlgebra.of k A g • rho.asModuleEquiv.symm y =
      rho.asModuleEquiv.symm y at hyN
    rw [← rho.asModuleEquiv_symm_map_rho] at hyN
    exact rho.asModuleEquiv.symm.injective (by simpa using hyN)

/-- A finite faithful commuting fixed-point-free linear group over a finite
field is cyclic. -/
theorem isCyclic_of_faithful_fixedPointFree_representation
    {k A V : Type*} [Field k] [Finite k] [Group A] [Finite A]
    [AddCommGroup V] [Module k V] [Finite V]
    [NeZero (Nat.card A : k)]
    (rho : Representation k A V)
    (hcomm : ∀ a b : A, Commute a b)
    (hfaith : Function.Injective rho)
    (hfixedPointFree :
      ∀ g : A, g ≠ 1 → ∀ x : V, rho g x = x → x = 0) :
    IsCyclic A := by
  classical
  by_cases hV : Subsingleton V
  · letI : Subsingleton V := hV
    haveI : Subsingleton (Module.End k V) := inferInstance
    haveI : Subsingleton A := hfaith.subsingleton
    exact isCyclic_of_subsingleton
  · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
    haveI : Nontrivial rho.asModule := rho.asModuleEquiv.toEquiv.nontrivial
    haveI : Finite rho.asModule :=
      rho.asModuleEquiv.toEquiv.finite_iff.mpr inferInstance
    haveI : IsSemisimpleModule k[A] rho.asModule := inferInstance
    obtain ⟨S, hSsimple⟩ :=
      IsSemisimpleModule.exists_simple_submodule k[A] rho.asModule
    letI : IsSimpleModule k[A] S := hSsimple
    haveI : Nontrivial S := IsSimpleModule.nontrivial k[A] S
    let actionEnd (g : A) : Module.End k[A] S :=
      { toFun := fun s ↦ MonoidAlgebra.of k A g • s
        map_add' := by intro x y; exact smul_add _ _ _
        map_smul' := by
          intro c s
          apply Subtype.ext
          change MonoidAlgebra.of k A g • (c • (s : rho.asModule)) =
            c • (MonoidAlgebra.of k A g • (s : rho.asModule))
          rw [← mul_smul, (MonoidAlgebra.of_commute (hcomm g) c).eq,
            mul_smul] }
    let phi : A →* Module.End k[A] S :=
      { toFun := actionEnd
        map_one' := by
          ext s
          change MonoidAlgebra.of k A 1 • (s : rho.asModule) =
            (s : rho.asModule)
          rw [map_one, one_smul]
        map_mul' := by
          intro g h
          ext s
          change MonoidAlgebra.of k A (g * h) • (s : rho.asModule) =
            MonoidAlgebra.of k A g •
              (MonoidAlgebra.of k A h • (s : rho.asModule))
          rw [map_mul, mul_smul] }
    have hphi : Function.Injective phi := by
      intro g h hgh
      obtain ⟨s, hs⟩ := exists_ne (0 : S)
      have haction :
          MonoidAlgebra.of k A g • (s : rho.asModule) =
            MonoidAlgebra.of k A h • (s : rho.asModule) := by
        have hsEq := DFunLike.congr_fun hgh s
        exact congrArg Subtype.val hsEq
      have hrho : rho g (rho.asModuleEquiv (s : rho.asModule)) =
          rho h (rho.asModuleEquiv (s : rho.asModule)) := by
        have hsEq := congrArg rho.asModuleEquiv haction
        simpa using hsEq
      have hfix : rho (h⁻¹ * g) (rho.asModuleEquiv (s : rho.asModule)) =
          rho.asModuleEquiv (s : rho.asModule) := by
        rw [map_mul, Module.End.mul_apply, hrho]
        exact rho.inv_self_apply h _
      have hnonzero : rho.asModuleEquiv (s : rho.asModule) ≠ 0 := by
        intro hs0
        apply hs
        apply Subtype.ext
        exact rho.asModuleEquiv.injective (by simpa using hs0)
      have hone : h⁻¹ * g = 1 := by
        by_contra hne
        exact hnonzero (hfixedPointFree (h⁻¹ * g) hne _ hfix)
      calc
        g = h * (h⁻¹ * g) := by simp
        _ = h * 1 := by rw [hone]
        _ = h := mul_one h
    haveI : Finite S := inferInstance
    haveI : Finite (Module.End k[A] S) :=
      Finite.of_injective (fun f : Module.End k[A] S ↦ (f : S → S))
        DFunLike.coe_injective
    letI : DivisionRing (Module.End k[A] S) := Module.End.instDivisionRing
    letI : Field (Module.End k[A] S) := littleWedderburn _
    exact isCyclic_of_injective_ringHom phi hphi

/-- The cyclic refinement obtained by combining the two preceding
representation-theoretic lemmas. -/
theorem isCyclic_of_faithful_isIsotypic_of_commuting
    {k A V : Type*} [Field k] [Finite k] [Group A] [Finite A]
    [AddCommGroup V] [Module k V] [Finite V]
    [NeZero (Nat.card A : k)]
    (rho : Representation k A V)
    (hiso : IsIsotypic k[A] rho.asModule)
    (hcomm : ∀ a b : A, Commute a b)
    (hfaith : Function.Injective rho) :
    IsCyclic A :=
  isCyclic_of_faithful_fixedPointFree_representation rho hcomm hfaith
    (fixedPointFree_of_faithful_isIsotypic_of_commuting
      rho hiso hcomm hfaith)

end LisiSabatini
