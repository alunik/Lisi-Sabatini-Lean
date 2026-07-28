module

public import LisiSabatini.LinearImprimitivityExtraction
public import LisiSabatini.NormalRestrictionSemisimple
public import LisiSabatini.QuasiprimitiveRepresentation
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.RingTheory.SimpleModule.Isotypic

/-!
# Clifford imprimitivity extraction from normal restrictions

This file proves the Clifford-theoretic bridge needed by the project. For a
finite irreducible concrete linear group, a normal restriction with more than
one isotypic component supplies a nonzero proper subspace whose actual orbit
is independent. Hence the restriction is homogeneous, or the action carries
the precise `LinearImprimitivityExtractionWitness` consumed by the existing
imprimitivity pipeline.

The semisimplicity input is the normal-restriction socle theorem, so the final
alternative is unconditional in the defining characteristic: there is no
cross-characteristic or coprimality hypothesis.
-/

@[expose] public section

open scoped MonoidAlgebra

noncomputable section

namespace LisiSabatini

namespace Clifford

section Generic

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

noncomputable def componentTransport (sigma : R ≃+* R)
    (e : M ≃ₛₗ[RingHomClass.toRingHom sigma] M) :
    Submodule R M ≃o Submodule R M :=
  Submodule.orderIsoMapComap e

theorem simple_componentTransport (sigma : R ≃+* R)
    (e : M ≃ₛₗ[RingHomClass.toRingHom sigma] M) (P : Submodule R M)
    [IsSimpleModule R P] :
    IsSimpleModule R (componentTransport sigma e P) := by
  change IsSimpleModule R (P.map e.toLinearMap)
  apply (LinearMap.isSimpleModule_iff_of_bijective
    (e.submoduleMap P).toLinearMap (e.submoduleMap P).bijective).mp
  infer_instance

noncomputable def semilinearConjugateEnd (sigma : R ≃+* R)
    (e : M ≃ₛₗ[RingHomClass.toRingHom sigma] M)
    (f : Module.End R M) : Module.End R M where
  toFun x := e.symm (f (e x))
  map_add' x y := by simp
  map_smul' r x := by
    apply e.injective
    rw [e.apply_symm_apply, map_smulₛₗ, f.map_smul, map_smulₛₗ]
    simp

theorem fullyInvariant_componentTransport (sigma : R ≃+* R)
    (e : M ≃ₛₗ[RingHomClass.toRingHom sigma] M)
    (C : Submodule R M) (hC : C.IsFullyInvariant) :
    (componentTransport sigma e C).IsFullyInvariant := by
  intro f y hy
  change y ∈ C.map e.toLinearMap at hy
  rcases hy with ⟨x, hx, rfl⟩
  refine ⟨e.symm (f (e x)), hC (semilinearConjugateEnd sigma e f) hx, ?_⟩
  simp

noncomputable def semilinearConjugateEquiv (sigma : R ≃+* R)
    (e : M ≃ₛₗ[RingHomClass.toRingHom sigma] M)
    (P Q : Submodule R M) (f : P ≃ₗ[R] Q) :
    componentTransport sigma e P ≃ₗ[R] componentTransport sigma e Q where
  toFun x := e.submoduleMap Q (f ((e.submoduleMap P).symm x))
  invFun y := e.submoduleMap P (f.symm ((e.submoduleMap Q).symm y))
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by
    apply Subtype.ext
    change e (f ((e.submoduleMap P).symm (x + y))) =
      e (f ((e.submoduleMap P).symm x)) +
        e (f ((e.submoduleMap P).symm y))
    rw [← e.map_add]
    have hep : (e.submoduleMap P).symm (x + y) =
        (e.submoduleMap P).symm x + (e.submoduleMap P).symm y :=
      (e.submoduleMap P).symm.map_add x y
    have hfadd : f ((e.submoduleMap P).symm (x + y)) =
        f ((e.submoduleMap P).symm x) + f ((e.submoduleMap P).symm y) := by
      rw [hep, f.map_add]
    exact congrArg e (congrArg Subtype.val hfadd)
  map_smul' r x := by
    apply Subtype.ext
    change e (f ((e.submoduleMap P).symm (r • x))) =
      r • e (f ((e.submoduleMap P).symm x))
    have hxsmul : (e.submoduleMap P).symm (r • x) =
        sigma.symm r • (e.submoduleMap P).symm x := by
      exact map_smulₛₗ (e.submoduleMap P).symm r x
    rw [hxsmul, f.map_smul]
    change e (sigma.symm r • (f ((e.submoduleMap P).symm x) : M)) =
      r • e (f ((e.submoduleMap P).symm x) : M)
    rw [map_smulₛₗ]
    simp

/-- Compatibility spelling for mathlib's identity equivalence between equal
submodules. -/
noncomputable abbrev submoduleLinearEquivOfEq
    {P Q : Submodule R M} (h : P = Q) : P ≃ₗ[R] Q :=
  LinearEquiv.ofEq P Q h

theorem isIsotypic_componentTransport (sigma : R ≃+* R)
    (e : M ≃ₛₗ[RingHomClass.toRingHom sigma] M)
    (C : Submodule R M) (hC : IsIsotypic R C) :
    IsIsotypic R (componentTransport sigma e C) := by
  rw [isIsotypic_submodule_iff]
  intro P hP instP
  rw [isIsotypicOfType_submodule_iff]
  intro Q hQ instQ
  let P0 : Submodule R M := componentTransport sigma.symm e.symm P
  let Q0 : Submodule R M := componentTransport sigma.symm e.symm Q
  let F := componentTransport sigma e
  have hP0eq : P0 = F.symm P := by
    dsimp [P0, F, componentTransport]
    exact (Submodule.comap_equiv_eq_map_symm e P).symm
  have hQ0eq : Q0 = F.symm Q := by
    dsimp [Q0, F, componentTransport]
    exact (Submodule.comap_equiv_eq_map_symm e Q).symm
  letI : IsSimpleModule R P0 := simple_componentTransport sigma.symm e.symm P
  letI : IsSimpleModule R Q0 := simple_componentTransport sigma.symm e.symm Q
  have hP0 : P0 ≤ C := by
    rw [hP0eq]
    have := F.symm.monotone hP
    simpa [F] using this
  have hQ0 : Q0 ≤ C := by
    rw [hQ0eq]
    have := F.symm.monotone hQ
    simpa [F] using this
  obtain ⟨f⟩ := isIsotypicOfType_submodule_iff.mp
    (isIsotypic_submodule_iff.mp hC P0 hP0) Q0 hQ0
  have hPback : componentTransport sigma e P0 = P := by
    change F P0 = P
    rw [hP0eq]
    exact F.apply_symm_apply P
  have hQback : componentTransport sigma e Q0 = Q := by
    change F Q0 = Q
    rw [hQ0eq]
    exact F.apply_symm_apply Q
  exact ⟨(LinearEquiv.ofEq _ _ hQback).symm.trans
    ((semilinearConjugateEquiv sigma e Q0 P0 f).trans
      (LinearEquiv.ofEq _ _ hPback))⟩

theorem componentTransport_mem_isotypicComponents
    [IsSemisimpleModule R M]
    (sigma : R ≃+* R)
    (e : M ≃ₛₗ[RingHomClass.toRingHom sigma] M)
    (C : Submodule R M) (hC : C ∈ isotypicComponents R M) :
    componentTransport sigma e C ∈ isotypicComponents R M := by
  rw [mem_isotypicComponents_iff] at hC ⊢
  refine ⟨isIsotypic_componentTransport sigma e C hC.1,
    fullyInvariant_componentTransport sigma e C hC.2.1, ?_⟩
  intro hbot
  apply hC.2.2
  apply (componentTransport sigma e).injective
  simpa using hbot

end Generic

open scoped MonoidAlgebra

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {k G V : Type*} [Field k] [Group G]
  [AddCommGroup V] [Module k V]
  (rho : Representation k G V) (H : Subgroup G) [H.Normal]

/-- A restriction module whose type constructor remembers the representation,
so its group-algebra module instance is inferable without ambiguity. -/
def RestrictionModule (tau : Representation k H V) := tau.asModule
deriving AddCommGroup, Module k

noncomputable instance (tau : Representation k H V) :
    Module k[H] (RestrictionModule H tau) := by
  change Module k[H] tau.asModule
  exact Representation.instModuleMonoidAlgebraAsModule tau

noncomputable instance (tau : Representation k H V) :
    IsScalarTower k k[H] (RestrictionModule H tau) := by
  change IsScalarTower k k[H] tau.asModule
  letI : Module k[H] tau.asModule :=
    Representation.instModuleMonoidAlgebraAsModule tau
  infer_instance

def restrictionModuleEquiv (tau : Representation k H V) :
    RestrictionModule H tau ≃ₗ[k] V :=
  LinearEquiv.refl k V

omit [H.Normal] in
@[simp]
theorem restrictionModuleEquiv_map_smul (tau : Representation k H V)
    (a : k[H]) (v : RestrictionModule H tau) :
    restrictionModuleEquiv H tau (a • v) =
      tau.asAlgebraHom a (restrictionModuleEquiv H tau v) :=
  rfl

noncomputable def restrictionConjugationRingEquiv (g : G) :
    k[H] ≃+* k[H] :=
  (MonoidAlgebra.domCongr k k (MulAut.conjNormal g)).toRingEquiv

theorem restriction_conjugation_smul
    (tau : Representation k H V)
    (htau : ∀ h : H, tau h = rho h.1)
    (g : G) (a : k[H])
    (v : RestrictionModule H tau) :
    (restrictionModuleEquiv H tau).symm
        (rho g (restrictionModuleEquiv H tau (a • v))) =
      restrictionConjugationRingEquiv (k := k) H g a •
        (restrictionModuleEquiv H tau).symm
          (rho g (restrictionModuleEquiv H tau v)) := by
  apply (restrictionModuleEquiv H tau).injective
  simp only [LinearEquiv.apply_symm_apply,
    restrictionModuleEquiv_map_smul]
  apply a.induction_on
  · intro h
    have hdom : restrictionConjugationRingEquiv (k := k) H g
        (MonoidAlgebra.of k H h) =
        MonoidAlgebra.of k H (MulAut.conjNormal g h) := by
      simp [restrictionConjugationRingEquiv, MonoidAlgebra.of_apply]
    rw [hdom]
    simp only [Representation.asAlgebraHom_of]
    rw [htau h, htau (MulAut.conjNormal g h)]
    change rho g (rho (h : G)
        (restrictionModuleEquiv H tau v)) =
      rho ((MulAut.conjNormal g h : H) : G)
        (rho g (restrictionModuleEquiv H tau v))
    rw [MulAut.conjNormal_apply]
    let w := restrictionModuleEquiv H tau v
    change rho g (rho (h : G) w) =
      rho (g * (h : G) * g⁻¹) (rho g w)
    calc
      rho g (rho (h : G) w) = rho (g * (h : G)) w := by
        simp
      _ = rho ((g * (h : G) * g⁻¹) * g) w := by simp [mul_assoc]
      _ = rho (g * (h : G) * g⁻¹) (rho g w) := by
        simp
  · intro x y hx hy
    have hAlgAdd : tau.asAlgebraHom (x + y) =
        tau.asAlgebraHom x + tau.asAlgebraHom y :=
      map_add tau.asAlgebraHom x y
    have hσadd : restrictionConjugationRingEquiv (k := k) H g (x + y) =
        restrictionConjugationRingEquiv (k := k) H g x +
          restrictionConjugationRingEquiv (k := k) H g y :=
      map_add (restrictionConjugationRingEquiv (k := k) H g) x y
    have hAlgAddσ : tau.asAlgebraHom
          (restrictionConjugationRingEquiv (k := k) H g x +
            restrictionConjugationRingEquiv (k := k) H g y) =
        tau.asAlgebraHom
            (restrictionConjugationRingEquiv (k := k) H g x) +
          tau.asAlgebraHom
            (restrictionConjugationRingEquiv (k := k) H g y) :=
      map_add tau.asAlgebraHom _ _
    rw [hAlgAdd, hσadd, hAlgAddσ]
    simp only [LinearMap.add_apply, (rho g).map_add, hx, hy]
  · intro r x hx
    have hscale : restrictionConjugationRingEquiv (k := k) H g (r • x) =
        r • restrictionConjugationRingEquiv (k := k) H g x := by
      exact (MonoidAlgebra.domCongr k k
        (MulAut.conjNormal g)).toLinearEquiv.map_smul r x
    have hAlgScale (z : k[H]) :
        tau.asAlgebraHom (r • z) =
          r • tau.asAlgebraHom z :=
      tau.asAlgebraHom.toLinearMap.map_smul r z
    rw [hAlgScale x, hscale,
      hAlgScale (restrictionConjugationRingEquiv (k := k) H g x),
      LinearMap.smul_apply, (rho g).map_smul, hx]
    rw [LinearMap.smul_apply]

noncomputable def restrictionConjugationSemilinearEquiv
    (tau : Representation k H V)
    (htau : ∀ h : H, tau h = rho h.1)
    (g : G) :
    RestrictionModule H tau ≃ₛₗ[
      RingHomClass.toRingHom (restrictionConjugationRingEquiv (k := k) H g)]
      RestrictionModule H tau where
  toFun v := (restrictionModuleEquiv H tau).symm
    (rho g (restrictionModuleEquiv H tau v))
  invFun v := (restrictionModuleEquiv H tau).symm
    (rho g⁻¹ (restrictionModuleEquiv H tau v))
  left_inv v := by
    apply (restrictionModuleEquiv H tau).injective
    simp
  right_inv v := by
    apply (restrictionModuleEquiv H tau).injective
    simp
  map_add' x y := by simp
  map_smul' a v := restriction_conjugation_smul rho H tau htau g a v

theorem restrictionConjugation_mem_isotypicComponents
    (tau : Representation k H V)
    (htau : ∀ h : H, tau h = rho h.1)
    [IsSemisimpleModule k[H] (RestrictionModule H tau)]
    (g : G) (C : Submodule k[H] (RestrictionModule H tau))
    (hC : C ∈ isotypicComponents k[H]
      (RestrictionModule H tau)) :
    componentTransport (restrictionConjugationRingEquiv (k := k) H g)
        (restrictionConjugationSemilinearEquiv rho H tau htau g) C ∈
      isotypicComponents k[H] (RestrictionModule H tau) :=
  componentTransport_mem_isotypicComponents _ _ C hC

/-- The underlying `k`-subspace of an `H`-isotypic component. -/
noncomputable def underlyingRestrictionComponent
    (tau : Representation k H V)
    (C : Submodule k[H] (RestrictionModule H tau)) :
    Submodule k V :=
  (C.restrictScalars k).map
    (restrictionModuleEquiv H tau).toLinearMap

omit [H.Normal] in
theorem underlyingRestrictionComponents_iSupIndep
    (tau : Representation k H V) :
    iSupIndep (fun C : isotypicComponents k[H]
        (RestrictionModule H tau) =>
      underlyingRestrictionComponent H tau C.1) := by
  have hind : iSupIndep (fun C : isotypicComponents k[H]
      (RestrictionModule H tau) => C.1) :=
    (sSupIndep_iff _).mp
      (sSupIndep_isotypicComponents k[H]
        (RestrictionModule H tau))
  have hindRestrict : iSupIndep (fun C : isotypicComponents k[H]
      (RestrictionModule H tau) =>
      C.1.restrictScalars k) := by
    intro C
    have hC := hind C
    rw [disjoint_iff] at hC ⊢
    simp_rw [← Submodule.restrictScalars_iSup]
    rw [← Submodule.restrictScalars_inf]
    exact (Submodule.restrictScalars_eq_bot_iff
      k k[H] (RestrictionModule H tau)).mpr hC
  exact LinearMap.iSupIndep_map
    (restrictionModuleEquiv H tau).toLinearMap
    (restrictionModuleEquiv H tau).injective hindRestrict

/-- Conjugation by `g` sends the underlying subspace of a restriction
isotypic component to the underlying subspace of its semilinear transport. -/
theorem underlyingRestrictionComponent_map
    (tau : Representation k H V)
    (htau : ∀ h : H, tau h = rho h.1)
    (g : G) (C : Submodule k[H] (RestrictionModule H tau)) :
    (underlyingRestrictionComponent H tau C).map (rho g) =
      underlyingRestrictionComponent H tau
        (componentTransport (restrictionConjugationRingEquiv (k := k) H g)
          (restrictionConjugationSemilinearEquiv rho H tau htau g) C) := by
  ext x
  simp only [underlyingRestrictionComponent, Submodule.mem_map,
    Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨(restrictionConjugationSemilinearEquiv rho H tau htau g) v,
      ⟨v, hv, rfl⟩, ?_⟩
    rfl
  · rintro ⟨w, ⟨v, hv, hvw⟩, rfl⟩
    subst w
    exact ⟨restrictionModuleEquiv H tau v, ⟨v, hv, rfl⟩, rfl⟩

section Concrete

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup k V)}

def concreteRestrictionRepresentation (H : Subgroup K) :
    Representation k H V :=
  (linearSubgroupRepresentation K).comp H.subtype

theorem concreteRestrictionRepresentation_apply (H : Subgroup K) (h : H) :
    concreteRestrictionRepresentation H h =
      linearSubgroupRepresentation K h.1 :=
  rfl

theorem linearSubmoduleImage_underlyingRestrictionComponent
    (H : Subgroup K) [H.Normal] (g : K)
    (C : Submodule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))) :
    linearSubmoduleImage g
        (underlyingRestrictionComponent H
          (concreteRestrictionRepresentation H) C) =
      underlyingRestrictionComponent H
        (concreteRestrictionRepresentation H)
        (componentTransport
          (restrictionConjugationRingEquiv (k := k) H g)
          (restrictionConjugationSemilinearEquiv
            (linearSubgroupRepresentation K) H
            (concreteRestrictionRepresentation H)
            (concreteRestrictionRepresentation_apply H) g) C) := by
  change (underlyingRestrictionComponent H
      (concreteRestrictionRepresentation H) C).map
        (linearSubgroupRepresentation K g) = _
  exact underlyingRestrictionComponent_map
    (linearSubgroupRepresentation K) H
    (concreteRestrictionRepresentation H)
    (concreteRestrictionRepresentation_apply H) g C

/-- A chosen group element carrying the base component to a given member of
its actual submodule orbit. -/
noncomputable def orbitRepresentative
    (H : Subgroup K) [H.Normal]
    (C : Submodule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)))
    (W : SubmoduleOrbitIndex K
      (underlyingRestrictionComponent H
        (concreteRestrictionRepresentation H) C)) : K :=
  Classical.choose W.2

theorem orbitRepresentative_spec
    (H : Subgroup K) [H.Normal]
    (C : Submodule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)))
    (W : SubmoduleOrbitIndex K
      (underlyingRestrictionComponent H
        (concreteRestrictionRepresentation H) C)) :
    linearSubmoduleImage (orbitRepresentative H C W)
        (underlyingRestrictionComponent H
          (concreteRestrictionRepresentation H) C) = W.1 :=
  Classical.choose_spec W.2

/-- The isotypic component corresponding to a member of the orbit of one
chosen component. -/
noncomputable def orbitIsotypicComponent
    (H : Subgroup K) [H.Normal]
    [IsSemisimpleModule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))]
    (C : isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)))
    (W : SubmoduleOrbitIndex K
      (underlyingRestrictionComponent H
        (concreteRestrictionRepresentation H) C.1)) :
    isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)) :=
  ⟨componentTransport
      (restrictionConjugationRingEquiv (k := k) H
        (orbitRepresentative H C.1 W))
      (restrictionConjugationSemilinearEquiv
        (linearSubgroupRepresentation K) H
        (concreteRestrictionRepresentation H)
        (concreteRestrictionRepresentation_apply H)
        (orbitRepresentative H C.1 W)) C.1,
    restrictionConjugation_mem_isotypicComponents
      (linearSubgroupRepresentation K) H
      (concreteRestrictionRepresentation H)
      (concreteRestrictionRepresentation_apply H)
      (orbitRepresentative H C.1 W) C.1 C.2⟩

theorem underlying_orbitIsotypicComponent
    (H : Subgroup K) [H.Normal]
    [IsSemisimpleModule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))]
    (C : isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)))
    (W : SubmoduleOrbitIndex K
      (underlyingRestrictionComponent H
        (concreteRestrictionRepresentation H) C.1)) :
    underlyingRestrictionComponent H
        (concreteRestrictionRepresentation H)
        (orbitIsotypicComponent H C W).1 = W.1 := by
  exact (linearSubmoduleImage_underlyingRestrictionComponent
    H (orbitRepresentative H C.1 W) C.1).symm.trans
      (orbitRepresentative_spec H C.1 W)

theorem orbitIsotypicComponent_injective
    (H : Subgroup K) [H.Normal]
    [IsSemisimpleModule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))]
    (C : isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))) :
    Function.Injective (orbitIsotypicComponent H C) := by
  intro W Z hWZ
  apply Subtype.ext
  rw [← underlying_orbitIsotypicComponent H C W,
    ← underlying_orbitIsotypicComponent H C Z, hWZ]

theorem orbit_underlyingRestrictionComponent_iSupIndep
    (H : Subgroup K) [H.Normal]
    [IsSemisimpleModule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))]
    (C : isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))) :
    iSupIndep (fun W : SubmoduleOrbitIndex K
      (underlyingRestrictionComponent H
        (concreteRestrictionRepresentation H) C.1) => W.1) := by
  have hind := (underlyingRestrictionComponents_iSupIndep H
    (concreteRestrictionRepresentation H)).comp
      (orbitIsotypicComponent_injective H C)
  convert hind using 1
  funext W
  exact (underlying_orbitIsotypicComponent H C W).symm

/-- The project's field-independent irreducibility predicate implies
mathlib's representation-theoretic predicate on a nonzero module. -/
theorem linearSubgroupRepresentation_isIrreducible_of_project
    [Nontrivial V]
    (hirr : LinearImprimitivitySystem.IsIrreducible K) :
    (linearSubgroupRepresentation K).IsIrreducible := by
  change IsSimpleOrder (Subrepresentation (linearSubgroupRepresentation K))
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    have h' : (⊥ : Submodule k V) = ⊤ :=
      congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h'
  · intro W
    obtain hW | hW := hirr W.toSubmodule (by
      intro g v hv
      exact W.apply_mem_toSubmodule g hv)
    · left
      apply Subrepresentation.toSubmodule_injective
      simpa using hW
    · right
      apply Subrepresentation.toSubmodule_injective
      simpa using hW

theorem underlyingRestrictionComponent_ne_bot
    (H : Subgroup K) [H.Normal]
    [IsSemisimpleModule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))]
    (C : isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))) :
    underlyingRestrictionComponent H
      (concreteRestrictionRepresentation H) C.1 ≠ ⊥ := by
  intro hbot
  change
    (C.1.restrictScalars k).map
        (restrictionModuleEquiv H
          (concreteRestrictionRepresentation H)).toLinearMap = ⊥ at hbot
  rw [Submodule.map_eq_bot_iff] at hbot
  have hCbot : C.1 = ⊥ :=
    (Submodule.restrictScalars_eq_bot_iff
      k k[H] (RestrictionModule H
        (concreteRestrictionRepresentation H))).mp hbot
  exact (bot_lt_isotypicComponents C.2).ne' hCbot

theorem underlyingRestrictionComponent_ne_top
    (H : Subgroup K) [H.Normal]
    [IsSemisimpleModule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))]
    (C : isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)))
    (hCtop : C.1 ≠ ⊤) :
    underlyingRestrictionComponent H
      (concreteRestrictionRepresentation H) C.1 ≠ ⊤ := by
  intro htop
  change
    (C.1.restrictScalars k).map
        (restrictionModuleEquiv H
          (concreteRestrictionRepresentation H)).toLinearMap = ⊤ at htop
  rw [Submodule.map_eq_top_iff] at htop
  exact hCtop ((Submodule.restrictScalars_eq_top_iff
    k k[H] (RestrictionModule H
      (concreteRestrictionRepresentation H))).mp htop)

/-- A non-isotypic normal restriction of a finite irreducible concrete
linear group supplies the precise orbit witness used by the project's
imprimitivity extraction API. -/
theorem nonempty_linearImprimitivityExtractionWitness_of_not_isotypic
    [FiniteDimensional k V] [Finite K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (H : Subgroup K) [H.Normal]
    (hnotiso : ¬ IsIsotypic k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))) :
    Nonempty (LinearImprimitivityExtractionWitness K) := by
  have hMnontrivial : Nontrivial
      (RestrictionModule H (concreteRestrictionRepresentation H)) := by
    by_contra htriv
    letI : Subsingleton
        (RestrictionModule H (concreteRestrictionRepresentation H)) :=
      not_nontrivial_iff_subsingleton.mp htriv
    exact hnotiso (IsIsotypic.of_subsingleton k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)))
  letI : Nontrivial V := hMnontrivial
  have hrhoirr : (linearSubgroupRepresentation K).IsIrreducible :=
    linearSubgroupRepresentation_isIrreducible_of_project hirr
  letI : IsSemisimpleModule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)) := by
    exact Representation.isSemisimpleModule_normalRestriction
      (linearSubgroupRepresentation K) H hrhoirr
  obtain ⟨S, hSsimple⟩ :=
    IsSemisimpleModule.exists_simple_submodule k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H))
  let C : isotypicComponents k[H]
      (RestrictionModule H (concreteRestrictionRepresentation H)) :=
    ⟨isotypicComponent k[H]
        (RestrictionModule H (concreteRestrictionRepresentation H)) S,
      ⟨S, hSsimple, rfl⟩⟩
  have hCtop : C.1 ≠ ⊤ := by
    intro htop
    apply hnotiso
    apply Submodule.topEquiv.isIsotypic_iff.mp
    rw [← htop]
    exact IsIsotypic.isotypicComponents C.2
  exact ⟨LinearImprimitivityExtractionWitness.ofFiniteGroup hirr
    (underlyingRestrictionComponent H
      (concreteRestrictionRepresentation H) C.1)
    (underlyingRestrictionComponent_ne_bot H C)
    (underlyingRestrictionComponent_ne_top H C hCtop)
    (orbit_underlyingRestrictionComponent_iSupIndep H C)⟩

/-- Clifford's alternative in the exact form needed by the project's
imprimitivity pipeline: either every normal restriction is homogeneous, or
there is a concrete extraction witness. -/
theorem homogeneousNormalRestrictions_or_extractionWitness
    [FiniteDimensional k V] [Finite K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K) :
    (∀ H : Subgroup K, H.Normal →
      Representation.IsHomogeneous
        (concreteRestrictionRepresentation H)) ∨
      Nonempty (LinearImprimitivityExtractionWitness K) := by
  classical
  by_cases hV : Nontrivial V
  · letI : Nontrivial V := hV
    have hrhoirr : (linearSubgroupRepresentation K).IsIrreducible :=
      linearSubgroupRepresentation_isIrreducible_of_project hirr
    by_cases halliso : ∀ H : Subgroup K, H.Normal →
        IsIsotypic k[H]
          (RestrictionModule H (concreteRestrictionRepresentation H))
    · left
      intro H hHnormal
      letI : H.Normal := hHnormal
      refine ⟨Representation.isSemisimpleModule_normalRestriction
        (linearSubgroupRepresentation K) H hrhoirr, ?_⟩
      change IsIsotypic k[H]
        (RestrictionModule H (concreteRestrictionRepresentation H))
      exact halliso H hHnormal
    · right
      have hex : ∃ H : Subgroup K, ∃ _h : H.Normal,
          ¬ IsIsotypic k[H]
            (RestrictionModule H (concreteRestrictionRepresentation H)) := by
        simpa only [not_forall] using halliso
      obtain ⟨H, hHnormal, hnotiso⟩ := hex
      letI : H.Normal := hHnormal
      exact nonempty_linearImprimitivityExtractionWitness_of_not_isotypic
        hirr H hnotiso
  · left
    letI : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    intro H _hHnormal
    letI : Subsingleton
        (RestrictionModule H (concreteRestrictionRepresentation H)) := by
      constructor
      intro x y
      exact @Subsingleton.elim V
        (not_nontrivial_iff_subsingleton.mp hV) x y
    have hsemi : IsSemisimpleModule k[H]
        (RestrictionModule H (concreteRestrictionRepresentation H)) :=
      (isSemisimpleModule_iff k[H]
        (RestrictionModule H (concreteRestrictionRepresentation H))).mpr
          Subsingleton.instComplementedLattice
    have hiso : IsIsotypic k[H]
        (RestrictionModule H (concreteRestrictionRepresentation H)) :=
      IsIsotypic.of_subsingleton k[H]
        (RestrictionModule H (concreteRestrictionRepresentation H))
    exact ⟨hsemi, hiso⟩

/-- For the concrete finite-field actions used throughout the project, an
irreducible action is quasiprimitive or already carries a full linear
imprimitivity extraction witness.  This includes defining characteristic:
no coprimality hypothesis is present. -/
theorem quasiprimitiveLinearAction_or_extractionWitness
    (r d : ℕ) [Fact r.Prime]
    (K : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))) [Finite K]
    (hirr : IsIrreducibleLinearAction r d K) :
    IsQuasiprimitiveLinearAction r d K ∨
      Nonempty (LinearImprimitivityExtractionWitness K) := by
  rcases homogeneousNormalRestrictions_or_extractionWitness
      (K := K) hirr with hhom | hwitness
  · exact Or.inl ⟨hirr, hhom⟩
  · exact Or.inr hwitness

end Concrete

end Clifford

end LisiSabatini
