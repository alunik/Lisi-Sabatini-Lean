import LisiSabatini.QuasiprimitiveRepresentation
import Mathlib.RepresentationTheory.Submodule
import Mathlib.RingTheory.Artinian.Module

/-!
# Semisimplicity of normal restrictions

This file records the modular Clifford-theoretic socle argument: the
restriction of a finite-dimensional irreducible representation to a normal
subgroup is semisimple, with no cross-characteristic hypothesis.
-/

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

namespace Representation

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]

/-- The linear equivalence underlying the action of a group element. -/
def actionLinearEquiv (rho : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  LinearEquiv.ofBijective (rho g) (rho.apply_bijective g)

@[simp]
theorem actionLinearEquiv_apply (rho : Representation k G V) (g : G) (x : V) :
    actionLinearEquiv rho g x = rho g x :=
  rfl

@[simp]
theorem actionLinearEquiv_symm_apply (rho : Representation k G V) (g : G) (x : V) :
    (actionLinearEquiv rho g).symm x = rho g⁻¹ x := by
  apply (actionLinearEquiv rho g).injective
  simp

variable (rho : Representation k G V) (H : Subgroup G) [H.Normal]

private abbrev restricted : Representation k H V := rho.comp H.subtype

/-- Conjugation by `g` sends an `H`-invariant subspace to an
`H`-invariant subspace when `H` is normal. -/
def conjugateInvariantSubmodule (g : G)
    (W : Representation.invtSubmodule (restricted rho H)) :
    Representation.invtSubmodule (restricted rho H) := by
  let e := actionLinearEquiv rho g
  refine ⟨(W : Submodule k V).map e.toLinearMap, ?_⟩
  rw [Representation.mem_invtSubmodule]
  intro h x hx
  rw [Submodule.mem_comap]
  rcases hx with ⟨y, hy, rfl⟩
  have hnormal : H.Normal := inferInstance
  let h' : H :=
    ⟨g⁻¹ * (h : G) * g, hnormal.conj_mem' (h : G) h.property g⟩
  have hy' : (restricted rho H) h' y ∈ (W : Submodule k V) :=
    ((_root_.Representation.mem_invtSubmodule (restricted rho H)).mp
      W.property h') hy
  refine ⟨(restricted rho H) h' y, hy', ?_⟩
  change rho g (rho (h' : G) y) = rho (h : G) (rho g y)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  dsimp [h']
  group

@[simp]
theorem conjugateInvariantSubmodule_coe (g : G)
    (W : Representation.invtSubmodule (restricted rho H)) :
    (conjugateInvariantSubmodule rho H g W : Submodule k V) =
      (W : Submodule k V).map (actionLinearEquiv rho g).toLinearMap :=
  rfl

/-- Conjugation by `g` is an order automorphism of the lattice of
`H`-invariant subspaces. -/
def conjugateInvariantSubmoduleOrderIso (g : G) :
    Representation.invtSubmodule (restricted rho H) ≃o
      Representation.invtSubmodule (restricted rho H) where
  toFun := conjugateInvariantSubmodule rho H g
  invFun := conjugateInvariantSubmodule rho H g⁻¹
  left_inv W := by
    apply Subtype.ext
    ext x
    simp [conjugateInvariantSubmodule]
  right_inv W := by
    apply Subtype.ext
    ext x
    simp [conjugateInvariantSubmodule]
  map_rel_iff' {W Z} := by
    change (W : Submodule k V).map (actionLinearEquiv rho g).toLinearMap ≤
        (Z : Submodule k V).map (actionLinearEquiv rho g).toLinearMap ↔ W ≤ Z
    exact Submodule.map_le_map_iff_of_injective
      (actionLinearEquiv rho g).injective _ _

/-- The induced conjugation order automorphism on `k[H]`-submodules of
the restricted representation module. -/
def conjugateRestrictedSubmoduleOrderIso (g : G) :
    Submodule k[H] (restricted rho H).asModule ≃o
      Submodule k[H] (restricted rho H).asModule :=
  ((_root_.Representation.mapSubmodule (restricted rho H)).symm.trans
      (conjugateInvariantSubmoduleOrderIso rho H g)).trans
    (_root_.Representation.mapSubmodule (restricted rho H))

@[simp]
theorem conjugateRestrictedSubmoduleOrderIso_simple_iff (g : G)
    (N : Submodule k[H] (restricted rho H).asModule) :
    IsSimpleModule k[H] (conjugateRestrictedSubmoduleOrderIso rho H g N) ↔
      IsSimpleModule k[H] N := by
  let C := conjugateRestrictedSubmoduleOrderIso rho H g
  constructor
  · intro hs
    have ha : IsAtom (C N) :=
      (isSimpleModule_iff_isAtom (R := k[H])
        (M := (restricted rho H).asModule) (m := C N)).mp hs
    exact (isSimpleModule_iff_isAtom (R := k[H])
      (M := (restricted rho H).asModule) (m := N)).mpr ((C.isAtom_iff N).mp ha)
  · intro hs
    have ha : IsAtom N :=
      (isSimpleModule_iff_isAtom (R := k[H])
        (M := (restricted rho H).asModule) (m := N)).mp hs
    exact (isSimpleModule_iff_isAtom (R := k[H])
      (M := (restricted rho H).asModule) (m := C N)).mpr ((C.isAtom_iff N).mpr ha)

private def restrictedSocle : Submodule k[H] (restricted rho H).asModule :=
  sSup {N : Submodule k[H] (restricted rho H).asModule |
    IsSimpleModule k[H] N}

/-- Ambient conjugation fixes the socle of a normal restriction. -/
theorem conjugateRestrictedSubmoduleOrderIso_socle (g : G) :
    conjugateRestrictedSubmoduleOrderIso rho H g (restrictedSocle rho H) =
      restrictedSocle rho H := by
  rw [restrictedSocle, OrderIso.map_sSup]
  apply le_antisymm
  · apply iSup_le
    intro M
    apply iSup_le
    intro hM
    exact le_sSup
      ((conjugateRestrictedSubmoduleOrderIso_simple_iff rho H g M).2 hM)
  · apply sSup_le
    intro N hN
    let C := conjugateRestrictedSubmoduleOrderIso rho H g
    have hpre : IsSimpleModule k[H] (C.symm N) := by
      apply (conjugateRestrictedSubmoduleOrderIso_simple_iff rho H g _).mp
      rw [C.apply_symm_apply]
      exact hN
    calc
      N = C (C.symm N) := (C.apply_symm_apply N).symm
      _ ≤ ⨆ (_ : IsSimpleModule k[H] (C.symm N)), C (C.symm N) :=
        le_iSup (fun _ : IsSimpleModule k[H] (C.symm N) ↦ C (C.symm N)) hpre
      _ ≤ ⨆ M : Submodule k[H] (restricted rho H).asModule,
          ⨆ (_ : IsSimpleModule k[H] M), C M :=
        le_iSup
          (fun M : Submodule k[H] (restricted rho H).asModule ↦
            ⨆ (_ : IsSimpleModule k[H] M), C M)
          (C.symm N)

/-- The socle of the restriction, viewed in `V`, is fixed by every ambient
group element. -/
theorem conjugate_restrictedSocle_eq (g : G) :
    conjugateInvariantSubmodule rho H g
        ((_root_.Representation.mapSubmodule (restricted rho H)).symm
          (restrictedSocle rho H)) =
      ((_root_.Representation.mapSubmodule (restricted rho H)).symm
        (restrictedSocle rho H)) := by
  apply (_root_.Representation.mapSubmodule (restricted rho H)).injective
  simpa [conjugateRestrictedSubmoduleOrderIso] using
    conjugateRestrictedSubmoduleOrderIso_socle rho H g

/-- **Modular Clifford socle lemma.** The restriction of a
finite-dimensional irreducible representation to a normal subgroup is
semisimple.  In particular, no Maschke or cross-characteristic hypothesis
is needed. -/
theorem isSemisimpleModule_normalRestriction
    [FiniteDimensional k V]
    (hirr : rho.IsIrreducible) :
    IsSemisimpleModule k[H]
      (_root_.Representation.asModule (rho.comp H.subtype)) := by
  let sigma : Representation k H V := restricted rho H
  let soc : Submodule k[H] sigma.asModule := restrictedSocle rho H
  let E : sigma.invtSubmodule ≃o Submodule k[H] sigma.asModule :=
    _root_.Representation.mapSubmodule sigma
  haveI : IsSimpleModule k[G] rho.asModule :=
    (_root_.Representation.irreducible_iff_isSimpleModule_asModule rho).mp hirr
  haveI : Nontrivial rho.asModule := IsSimpleModule.nontrivial k[G] rho.asModule
  haveI : Nontrivial V := rho.asModuleEquiv.symm.toEquiv.nontrivial
  haveI : Nontrivial sigma.asModule := sigma.asModuleEquiv.toEquiv.nontrivial
  haveI : IsArtinian k sigma.asModule := inferInstance
  haveI : IsArtinian k[H] sigma.asModule := isArtinian_of_tower k inferInstance
  letI : IsAtomic (Submodule k[H] sigma.asModule) :=
    isAtomic_of_orderBot_wellFounded_lt
      ((isArtinian_iff k[H] sigma.asModule).mp inferInstance)
  have hsoc_ne : soc ≠ ⊥ := by
    obtain ⟨N, hN⟩ := IsAtomic.exists_atom (Submodule k[H] sigma.asModule)
    have hNsimple : IsSimpleModule k[H] N :=
      isSimpleModule_iff_isAtom.mpr hN
    intro hsoc
    have hle : N ≤ soc := le_sSup hNsimple
    exact hN.ne_bot (bot_unique (hsoc ▸ hle))
  let W : rho.invtSubmodule :=
    ⟨(E.symm soc : Submodule k V), by
      rw [_root_.Representation.mem_invtSubmodule]
      intro g x hx
      have hmap :
          (E.symm soc : Submodule k V).map
              (actionLinearEquiv rho g).toLinearMap =
            (E.symm soc : Submodule k V) := by
        exact congrArg Subtype.val (conjugate_restrictedSocle_eq rho H g)
      have hxmap : rho g x ∈
          (E.symm soc : Submodule k V).map
            (actionLinearEquiv rho g).toLinearMap := by
        exact Submodule.mem_map_of_mem hx
      rw [hmap] at hxmap
      exact hxmap⟩
  have hW : W = ⊥ ∨ W = ⊤ := by
    rcases eq_bot_or_eq_top
        (_root_.Representation.mapSubmodule rho W) with hbot | htop
    · exact Or.inl ((_root_.Representation.mapSubmodule rho).injective (by simpa using hbot))
    · exact Or.inr ((_root_.Representation.mapSubmodule rho).injective (by simpa using htop))
  have hW_ne : W ≠ ⊥ := by
    intro hbot
    have hval : (E.symm soc : Submodule k V) = ⊥ := by
      have h := congrArg (fun X : rho.invtSubmodule ↦ (X : Submodule k V)) hbot
      simpa [W] using h
    apply hsoc_ne
    apply E.symm.injective
    apply Subtype.ext
    simpa using hval
  have hW_top : W = ⊤ := hW.resolve_left hW_ne
  have hsoc_top : soc = ⊤ := by
    have hval : (E.symm soc : Submodule k V) = ⊤ := by
      have h := congrArg (fun X : rho.invtSubmodule ↦ (X : Submodule k V)) hW_top
      simpa [W] using h
    apply E.symm.injective
    apply Subtype.ext
    simpa using hval
  exact sSup_simples_eq_top_iff_isSemisimpleModule.mp hsoc_top

end Representation

end LisiSabatini
