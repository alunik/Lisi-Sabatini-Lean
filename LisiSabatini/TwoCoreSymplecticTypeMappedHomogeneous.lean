import LisiSabatini.InnerNormalRestrictionHomogeneous
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Homogeneity after passage to a faithful subgroup image

Quasiprimitivity gives a homogeneous representation of an abstract normal
subgroup.  The counting arguments use its faithful image in the ambient
general linear group.  This file records the harmless, but type-theoretically
nontrivial, transport across the canonical group equivalence.
-/

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

namespace Representation

universe uR uS uM uN

private local instance ringEquiv_invPair
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (σ : R ≃+* S) :
    RingHomInvPair σ.toRingHom σ.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv σ

private local instance ringEquiv_symm_invPair
    {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (σ : R ≃+* S) :
    RingHomInvPair σ.symm.toRingHom σ.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm σ

private theorem isIsotypic_of_semilinearEquiv
    {R : Type uR} {S : Type uS}
    {M : Type uM} {N : Type uN}
    [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R ≃+* S)
    (l : M ≃ₛₗ[σ.toRingHom] N)
    (h : IsIsotypic R M) :
    IsIsotypic S N := by
  intro n hn
  let en := l.symm.submoduleMap n
  let mn : Submodule R M := n.map l.symm.toLinearMap
  haveI : IsSimpleModule R mn :=
    (en.toLinearMap.isSimpleModule_iff_of_bijective en.bijective).mp
      hn
  intro n' hn'
  let en' := l.symm.submoduleMap n'
  let mn' : Submodule R M := n'.map l.symm.toLinearMap
  haveI : IsSimpleModule R mn' :=
    (en'.toLinearMap.isSimpleModule_iff_of_bijective en'.bijective).mp
      hn'
  let f : mn' ≃ₗ[R] mn := (h mn mn').some
  exact
    ⟨(en'.trans (f.trans en.symm) : n' ≃ₗ[S] n)⟩

private theorem isHomogeneous_of_semilinearEquiv
    {R : Type uR} {S : Type uS}
    {M : Type uM} {N : Type uN}
    [Ring R] [Ring S]
    [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module S N]
    (σ : R ≃+* S)
    (l : M ≃ₛₗ[σ.toRingHom] N)
    (hsemi : IsSemisimpleModule R M)
    (hiso : IsIsotypic R M) :
    IsSemisimpleModule S N ∧ IsIsotypic S N := by
  have hsemi' :
      IsSemisimpleModule S N :=
    (l.toLinearMap.isSemisimpleModule_iff_of_bijective l.bijective).mp
      hsemi
  exact
    ⟨hsemi', isIsotypic_of_semilinearEquiv σ l hiso⟩

universe uK uA uB uV

variable {k : Type uK} {A : Type uA} {B : Type uB} {V : Type uV}
variable [Field k] [Group A] [Group B]
variable [AddCommGroup V] [Module k V]

private abbrev compMulEquivRepresentation
    (rho : Representation k B V)
    (e : A ≃* B) :
    Representation k A V :=
  rho.comp e.toMonoidHom

/-- The identity on the representation space, regarded as a semilinear
equivalence between the two group-algebra module structures obtained by
renaming the acting group through a multiplicative equivalence. -/
private def compMulEquivAsModuleEquiv
    (rho : Representation k B V)
    (e : A ≃* B) :
    (compMulEquivRepresentation rho e).asModule ≃ₛₗ[
      (MonoidAlgebra.mapDomainRingEquiv k e).toRingHom] rho.asModule where
  toFun := fun v => v
  invFun := fun v => v
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl
  map_add' := fun _ _ => rfl
  map_smul' c v := by
    change
      (compMulEquivRepresentation rho e).asAlgebraHom c v =
        rho.asAlgebraHom
          (MonoidAlgebra.mapDomainRingEquiv k e c) v
    induction c using MonoidAlgebra.induction_on with
    | hM x =>
        rw [MonoidAlgebra.of_apply,
          MonoidAlgebra.mapDomainRingEquiv_single]
        simp only [Representation.asAlgebraHom_single, one_smul]
        rfl
    | hadd c d hc hd =>
        simp only [map_add, LinearMap.add_apply]
        exact congrArg₂ (· + ·) hc hd
    | hsmul c d hd =>
        have hmap :
            MonoidAlgebra.mapDomainRingEquiv k e (c • d) =
              c • MonoidAlgebra.mapDomainRingEquiv k e d := by
          ext b
          simp
        rw [hmap]
        simp only [map_smul, LinearMap.smul_apply]
        exact congrArg (fun z => c • z) hd

/-- Homogeneity is invariant under renaming the acting group by a
multiplicative equivalence. -/
theorem isHomogeneous_comp_mulEquiv_iff
    (rho : Representation k B V)
    (e : A ≃* B) :
    IsHomogeneous (compMulEquivRepresentation rho e) ↔
      IsHomogeneous rho := by
  let σ := MonoidAlgebra.mapDomainRingEquiv k e
  let l := compMulEquivAsModuleEquiv rho e
  constructor
  · intro h
    exact isHomogeneous_of_semilinearEquiv σ l h.1 h.2
  · intro h
    have hback :=
      isHomogeneous_of_semilinearEquiv σ.symm l.symm h.1 h.2
    simpa only [σ, l] using hback

end Representation

/-- Quasiprimitivity transports the homogeneous restriction to the
faithful general-linear image of any normal subgroup. -/
theorem mappedNormalSubgroup_linearRepresentation_isHomogeneous
    {r d : ℕ} [Fact r.Prime]
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (H : Subgroup K) (hH : H.Normal) :
    Representation.IsHomogeneous
      (linearSubgroupRepresentation (H.map K.subtype)) := by
  let e : H ≃* H.map K.subtype :=
    H.equivMapOfInjective K.subtype K.subtype_injective
  let rho :=
    linearSubgroupRepresentation (H.map K.subtype)
  apply
    (Representation.isHomogeneous_comp_mulEquiv_iff rho e).mp
  change
    Representation.IsHomogeneous
      ((linearSubgroupRepresentation (H.map K.subtype)).comp
        e.toMonoidHom)
  have hsource := hqp.2 H hH
  simpa only [rho, e, linearSubgroupRepresentation,
    MonoidHom.coe_comp,
    Function.comp_apply, Subgroup.coe_equivMapOfInjective_apply] using
      hsource

/-- In particular, the mapped normal prime core inherits the homogeneous
representation supplied by quasiprimitivity. -/
theorem mappedPCore_linearRepresentation_isHomogeneous
    {r d q : ℕ} [Fact r.Prime]
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    Representation.IsHomogeneous
      (linearSubgroupRepresentation ((pCore q K).map K.subtype)) :=
  mappedNormalSubgroup_linearRepresentation_isHomogeneous
    hqp (pCore q K) inferInstance

end LisiSabatini
