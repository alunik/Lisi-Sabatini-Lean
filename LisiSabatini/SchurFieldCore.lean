module

public import LisiSabatini.HomogeneousDimension
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.RingTheory.LittleWedderburn

/-!
# The finite Schur field of a simple constituent

This file contains only the Schur-field infrastructure used by the
Stone--von Neumann argument: finite-dimensionality of the endomorphism
ring, the central action on a constituent, and a separate carrier for the
finite Schur field.  Determinant-based compatibility results live in
`SchurFieldDegree.lean` and are deliberately not imported here.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

universe uK uA uV uP

/-- The Schur endomorphism ring of a simple finite-dimensional module is
finite as a vector space over the ground field. -/
theorem moduleFinite_schurEnd
    {k A S : Type*} [Field k] [Ring A] [Algebra k A]
    [AddCommGroup S] [Module k S] [Module A S]
    [IsScalarTower k A S] [SMulCommClass A k S]
    [Module.Finite k S] :
    Module.Finite k (Module.End A S) := by
  exact Module.Finite.of_injective
    (LinearMap.restrictScalarsₗ k A S S k)
    (LinearMap.restrictScalars_injective k)

/-! ## Central action on a simple constituent -/

section CentralAction

variable {k P V : Type*} [Field k] [Group P]
  [AddCommGroup V] [Module k V]
  (rho : Representation k P V)

/-- A central group element acts as an endomorphism of every constituent
over the full group algebra. -/
def centralConstituentAction
    (S : Submodule k[P] rho.asModule) (z : Subgroup.center P) :
    Module.End k[P] S where
  toFun s := ⟨MonoidAlgebra.of k P z.1 • (s : rho.asModule),
    S.smul_mem _ s.2⟩
  map_add' x y := by
    apply Subtype.ext
    exact smul_add _ _ _
  map_smul' c s := by
    apply Subtype.ext
    change MonoidAlgebra.of k P z.1 • (c • (s : rho.asModule)) =
      c • (MonoidAlgebra.of k P z.1 • (s : rho.asModule))
    let hzcomm : ∀ g : P, Commute z.1 g := fun g ↦
      (Subgroup.mem_center_iff.mp z.2 g).symm
    rw [← mul_smul, (MonoidAlgebra.of_commute hzcomm c).eq, mul_smul]

/-- The central constituent action is multiplicative. -/
def centralConstituentActionHom
    (S : Submodule k[P] rho.asModule) :
    Subgroup.center P →* Module.End k[P] S where
  toFun := centralConstituentAction rho S
  map_one' := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change MonoidAlgebra.of k P (1 : P) • (s : rho.asModule) =
      (s : rho.asModule)
    rw [map_one, one_smul]
  map_mul' x y := by
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change MonoidAlgebra.of k P (x.1 * y.1) • (s : rho.asModule) =
      MonoidAlgebra.of k P x.1 •
        (MonoidAlgebra.of k P y.1 • (s : rho.asModule))
    rw [map_mul, mul_smul]

/-- On a homogeneous faithful representation, the action of the center on
one simple constituent is already faithful. -/
theorem centralConstituentActionHom_injective_of_decomposition
    (hfaith : Function.Injective rho)
    {S : Submodule k[P] rho.asModule} {b : ℕ}
    (e : rho.asModule ≃ₗ[k[P]] Fin b → S) :
    Function.Injective (centralConstituentActionHom rho S) := by
  intro z w hzw
  apply Subtype.ext
  apply hfaith
  apply LinearMap.ext
  intro v
  apply rho.asModuleEquiv.symm.injective
  have heq : MonoidAlgebra.of k P z.1 • rho.asModuleEquiv.symm v =
      MonoidAlgebra.of k P w.1 • rho.asModuleEquiv.symm v := by
    apply e.injective
    apply funext
    intro i
    have hi := DFunLike.congr_fun hzw (e (rho.asModuleEquiv.symm v) i)
    rw [e.map_smul, e.map_smul]
    exact hi
  simpa only [rho.asModuleEquiv_symm_map_rho] using heq

end CentralAction

/-! ## A diamond-free wrapper for the finite Schur field -/

/-- A separate carrier for the Schur endomorphism field.  Keeping this
carrier distinct from `Module.End A S` avoids the instance diamond between
the latter's native (possibly noncommutative) ring and the commutative field
structure supplied by Wedderburn's little theorem. -/
structure SchurField
    (A S : Type*) [Ring A] [AddCommGroup S] [Module A S] where
  val : Module.End A S

namespace SchurField

variable {A S : Type*} [Ring A] [AddCommGroup S] [Module A S]

/-- The underlying-type equivalence with the endomorphism ring. -/
def equiv : SchurField A S ≃ Module.End A S where
  toFun := val
  invFun := mk
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

instance [Finite (Module.End A S)] : Finite (SchurField A S) :=
  Finite.of_equiv (Module.End A S) equiv.symm

/-- Schur's lemma plus Wedderburn, transported to a fresh carrier. -/
noncomputable instance [IsSimpleModule A S] [Finite (Module.End A S)] :
    Field (SchurField A S) := by
  classical
  letI : DivisionRing (Module.End A S) :=
    Module.End.instDivisionRing (R := A) (M := S)
  letI : Field (Module.End A S) := littleWedderburn (Module.End A S)
  exact equiv.field

/-- Evaluation is the natural action of the Schur field on its simple
module. -/
noncomputable instance [IsSimpleModule A S] [Finite (Module.End A S)] :
    Module (SchurField A S) S where
  smul f s := f.val s
  one_smul s := by
    change (1 : Module.End A S) s = s
    simp
  mul_smul f g s := by
    change (f.val * g.val) s = f.val (g.val s)
    rfl
  smul_zero f := f.val.map_zero
  smul_add f x y := f.val.map_add x y
  zero_smul s := by
    change (0 : Module.End A S) s = 0
    simp
  add_smul f g s := by
    change (f.val + g.val) s = f.val s + g.val s
    rfl

/-- The transported field is ring-equivalent to the original Schur
endomorphism ring. -/
noncomputable def ringEquiv [IsSimpleModule A S]
    [Finite (Module.End A S)] :
    SchurField A S ≃+* Module.End A S where
  __ := equiv
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- The ground-field algebra structure transported from the endomorphism
ring. -/
noncomputable instance
    {k : Type*} [Field k] [Algebra k A]
    [Module k S] [IsScalarTower k A S] [SMulCommClass A k S]
    [IsSimpleModule A S] [Finite (Module.End A S)] :
    Algebra k (SchurField A S) :=
  RingHom.toAlgebra
    ((ringEquiv (A := A) (S := S)).symm.toRingHom.comp
      (algebraMap k (Module.End A S)))

/-- Evaluation is compatible with the tower from the ground field through
the Schur field. -/
noncomputable instance
    {k : Type*} [Field k] [Algebra k A]
    [Module k S] [IsScalarTower k A S] [SMulCommClass A k S]
    [IsSimpleModule A S] [Finite (Module.End A S)] :
    IsScalarTower k (SchurField A S) S where
  smul_assoc c f s := by
    change (algebraMap k (Module.End A S) c) (f.val s) = c • f.val s
    exact Module.algebraMap_end_apply k A S c (f.val s)

/-- Group action on a module, now linear over the diamond-free Schur
field. -/
def linearAction
    {k P : Type*} [Field k] [Group P]
    (S : Type*) [AddCommGroup S] [Module k[P] S]
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (g : P) : Module.End (SchurField k[P] S) S where
  toFun s := MonoidAlgebra.of k P g • s
  map_add' x y := smul_add _ _ _
  map_smul' f s := by
    change MonoidAlgebra.of k P g • f.val s =
      f.val (MonoidAlgebra.of k P g • s)
    exact (f.val.map_smul (MonoidAlgebra.of k P g) s).symm

theorem linearAction_mul
    {k P : Type*} [Field k] [Group P]
    (S : Type*) [AddCommGroup S] [Module k[P] S]
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (g h : P) :
    linearAction (k := k) S (g * h) =
      linearAction (k := k) S g * linearAction (k := k) S h := by
  ext s
  change MonoidAlgebra.of k P (g * h) • s =
    MonoidAlgebra.of k P g • (MonoidAlgebra.of k P h • s)
  rw [map_mul, mul_smul]

@[simp]
theorem linearAction_one
    {k P : Type*} [Field k] [Group P]
    (S : Type*) [AddCommGroup S] [Module k[P] S]
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)] :
    linearAction (k := k) S (1 : P) = 1 := by
  apply LinearMap.ext
  intro s
  change MonoidAlgebra.of k P (1 : P) • s = s
  rw [map_one, one_smul]

theorem linearAction_mul_inv
    {k P : Type*} [Field k] [Group P]
    (S : Type*) [AddCommGroup S] [Module k[P] S]
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (g : P) :
    linearAction (k := k) S g * linearAction (k := k) S g⁻¹ = 1 := by
  rw [← linearAction_mul, mul_inv_cancel, linearAction_one]

end SchurField

/-! ## The full central character over the Schur field -/

/-- The action of the full center on a simple constituent, transported to
the separate Schur-field carrier. -/
def fullCenterSchurScalarHom
    {k P V : Type*} [Field k] [Group P]
    [AddCommGroup V] [Module k V]
    (rho : Representation k P V)
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)] :
    Subgroup.center P →* SchurField k[P] S :=
  (SchurField.ringEquiv (A := k[P]) (S := S)).symm.toMonoidHom.comp
    (centralConstituentActionHom rho S)

/-- Homogeneity and faithfulness make the full central Schur character
injective. -/
theorem fullCenterSchurScalarHom_injective_of_decomposition
    {k P V : Type*} [Field k] [Group P]
    [AddCommGroup V] [Module k V]
    (rho : Representation k P V)
    (hfaith : Function.Injective rho)
    {S : Submodule k[P] rho.asModule} {b : ℕ}
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (e : rho.asModule ≃ₗ[k[P]] Fin b → S) :
    Function.Injective (fullCenterSchurScalarHom rho S) := by
  intro x y hxy
  apply centralConstituentActionHom_injective_of_decomposition
    rho hfaith e
  exact (SchurField.ringEquiv
    (A := k[P]) (S := S)).symm.injective hxy

/-- The full center embeds in the unit group of the finite Schur field. -/
theorem card_center_dvd_natCard_schurField_sub_one
    {k P V : Type*} [Field k] [Group P]
    [AddCommGroup V] [Module k V]
    (rho : Representation k P V)
    (hfaith : Function.Injective rho)
    {S : Submodule k[P] rho.asModule} {b : ℕ}
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (e : rho.asModule ≃ₗ[k[P]] Fin b → S) :
    Nat.card (Subgroup.center P) ∣
      Nat.card (SchurField k[P] S) - 1 := by
  let f := fullCenterSchurScalarHom rho S
  have hf : Function.Injective f :=
    fullCenterSchurScalarHom_injective_of_decomposition rho hfaith e
  have hfUnits : Function.Injective f.toHomUnits := by
    intro x y hxy
    apply hf
    exact congrArg Units.val hxy
  have hdvd := Subgroup.card_dvd_of_injective f.toHomUnits hfUnits
  simpa only [Nat.card_units] using hdvd

end LisiSabatini
