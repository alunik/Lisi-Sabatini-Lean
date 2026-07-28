module

public import LisiSabatini.QuasiprimitiveRepresentation
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The elementary dimension factorization for homogeneous representations

An isotypic finite-dimensional representation is a finite direct sum of
copies of one simple constituent.  This file records only that elementary
multiplicity statement.  In particular, it makes no assertion about the
dimension of the simple constituent arising from an extraspecial prime core.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

universe u

/-- A simple constituent, its positive multiplicity, and the resulting
base-field dimension factorization for a concrete `d`-dimensional
representation over `ZMod r`. -/
structure HomogeneousDimensionData
    (r d : ℕ) [Fact (Nat.Prime r)]
    {A : Type u} [Group A]
    (rho : Representation (ZMod r) A (Fin d → ZMod r)) where
  /-- The number of copies of the simple constituent. -/
  multiplicity : ℕ
  multiplicity_neZero : NeZero multiplicity
  /-- A simple constituent inside the representation module. -/
  constituent : Submodule (ZMod r)[A] rho.asModule
  constituent_simple : IsSimpleModule (ZMod r)[A] constituent
  /-- The homogeneous decomposition over the group algebra. -/
  decomposition : Nonempty
    (rho.asModule ≃ₗ[(ZMod r)[A]] Fin multiplicity → constituent)
  /-- Dimension over the original prime field. -/
  dimension_eq :
    d = multiplicity * Module.finrank (ZMod r) constituent

/-- A positive-dimensional homogeneous representation over a prime field
has a simple constituent of positive multiplicity, and its ambient dimension
is exactly multiplicity times constituent dimension.

This is the direct finite-dimensional consequence of
`IsIsotypic.linearEquiv_fun`; it does not include the hard constituent-degree
part of the quasiprimitive degree theorem. -/
def homogeneousDimensionData
    {r d : ℕ} [Fact (Nat.Prime r)]
    {A : Type u} [Group A]
    (rho : Representation (ZMod r) A (Fin d → ZMod r))
    (hd : 0 < d)
    (hhom : Representation.IsHomogeneous rho) :
    HomogeneousDimensionData r d rho := by
  classical
  letI : Nontrivial (Fin d → ZMod r) := by
    let i : Fin d := ⟨0, hd⟩
    exact ⟨⟨0, fun _ => 1, fun h => by
      have hi := congrFun h i
      simp at hi⟩⟩
  letI : Nontrivial rho.asModule :=
    rho.asModuleEquiv.toEquiv.nontrivial
  letI : AddCommMonoid rho.asModule :=
    Representation.instAddCommMonoidAsModule rho
  letI : Module (ZMod r)[A] rho.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rho
  letI : IsScalarTower (ZMod r) (ZMod r)[A] rho.asModule :=
    Representation.instIsScalarTowerMonoidAlgebraAsModule rho
  letI : IsSemisimpleModule (ZMod r)[A] rho.asModule := hhom.1
  letI : Module.Finite (ZMod r)[A] rho.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod r) (ZMod r)[A]
      rho.asModule
  let hex := hhom.2.linearEquiv_fun
  let b := hex.choose
  let hb : NeZero b := hex.choose_spec.choose
  let hexS := hex.choose_spec.choose_spec
  let S := hexS.choose
  let hS : IsSimpleModule (ZMod r)[A] S := hexS.choose_spec.1
  let e : rho.asModule ≃ₗ[(ZMod r)[A]] Fin b → S :=
    hexS.choose_spec.2.some
  letI : Module.Finite (ZMod r) S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars (ZMod r)) S.subtype_injective
  refine
    { multiplicity := b
      multiplicity_neZero := hb
      constituent := S
      constituent_simple := hS
      decomposition := ⟨e⟩
      dimension_eq := ?_ }
  have he := (e.restrictScalars (ZMod r)).finrank_eq
  rw [rho.asModuleEquiv.finrank_eq, Module.finrank_fin_fun] at he
  rw [Module.finrank_pi_fintype] at he
  simpa using he

end LisiSabatini
