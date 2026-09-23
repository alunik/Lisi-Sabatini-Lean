module

public import LisiSabatini.NilpotentTranslatedRegularityFiniteField
public import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Translated regularity on arbitrary modules over finite fields

Only finitely many regular witnesses, translations, and witnesses to
faithfulness are needed. Their span over the finite group algebra is a
finite invariant subspace, to which the finite-module theorem applies.
Thus the ambient module need not be finite or finite-dimensional.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

private theorem ofModule_submodule_semisimple
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (rho : Representation k G V)
    (hsemi : IsSemisimpleModule k[G] rho.asModule)
    (W : Submodule k[G] rho.asModule) :
    IsSemisimpleModule k[G]
      (Representation.ofModule' (k := k) (G := G) W).asModule := by
  let : IsSemisimpleModule k[G] rho.asModule := hsemi
  let sigma := Representation.ofModule' (k := k) (G := G) W
  exact IsSemisimpleModule.congr
    { toAddEquiv := sigma.asModuleEquiv.toAddEquiv
      map_smul' := by
        intro r m
        change sigma.asAlgebraHom r (sigma.asModuleEquiv m) =
          r • sigma.asModuleEquiv m
        simp [sigma, Representation.ofModule', Representation.asAlgebraHom_def] }

/-- Translated regular orbits for a faithful semisimple representation
of a finite nilpotent group over a finite field, with no restriction on
the dimension of the ambient module. -/
theorem exists_translated_regular_sylows_finiteField_arbitraryModule
    {k G V I : Type*} [Field k] [Finite k] [Group G] [Finite G]
    [Group.IsNilpotent G] [AddCommGroup V] [Module k V] [Finite I]
    (rho : Representation k G V) (hfaith : Function.Injective rho)
    (hsemi : IsSemisimpleModule k[G] rho.asModule)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P : ∀ i, Sylow (p i) G)
    (hregular : ∀ i, ∃ w : V, ∀ g : G,
      g ∈ (P i : Subgroup G) → rho g w = w → g = 1)
    (t : I → V) :
    ∃ v : V, ∀ i, ∀ g : G,
      g ∈ (P i : Subgroup G) → rho g (v + t i) = v + t i → g = 1 := by
  classical
  choose a ha using hregular
  have hseparate : ∀ z : G × G, ∃ v : V,
      z.1 ≠ z.2 → rho z.1 v ≠ rho z.2 v := by
    rintro ⟨g, h⟩
    by_cases hgh : g = h
    · exact ⟨0, fun hne ↦ (hne hgh).elim⟩
    have hex : ∃ v : V, rho g v ≠ rho h v := by
      by_contra! h
      exact hgh (hfaith (LinearMap.ext h))
    exact ⟨hex.choose, fun _ ↦ hex.choose_spec⟩
  choose b hb using hseparate
  let generators : I ⊕ (I ⊕ (G × G)) → V := Sum.elim a (Sum.elim t b)
  let W : Submodule k[G] rho.asModule := Submodule.span k[G]
    (Set.range fun j ↦ rho.asModuleEquiv.symm (generators j))
  let : Module.Finite k[G] W := Module.Finite.span_of_finite _ (Set.finite_range _)
  let : Finite k[G] := Finite.of_injective (fun c : k[G] ↦ (c.coeff : G → k))
    (fun _ _ h ↦ MonoidAlgebra.coeff_injective (DFunLike.coe_injective h))
  let : Finite W := Module.finite_of_finite k[G]
  let sigma := Representation.ofModule' (k := k) (G := G) W
  let inc : W →ₗ[k] V :=
    rho.asModuleEquiv.toLinearMap.comp (W.subtype.restrictScalars k)
  have hinc : Function.Injective inc :=
    rho.asModuleEquiv.injective.comp Subtype.val_injective
  have haction (g : G) (w : W) : inc (sigma g w) = rho g (inc w) := by
    change rho.asModuleEquiv (MonoidAlgebra.of k G g • (w : rho.asModule)) =
      rho g (rho.asModuleEquiv (w : rho.asModule))
    apply rho.asModuleEquiv.symm.injective
    rw [rho.asModuleEquiv.symm_apply_apply, rho.asModuleEquiv_symm_map_rho,
      rho.asModuleEquiv.symm_apply_apply]
  have hgen (j) : rho.asModuleEquiv.symm (generators j) ∈ W :=
    Submodule.subset_span ⟨j, rfl⟩
  let aw (i : I) : W := ⟨rho.asModuleEquiv.symm (a i), hgen (Sum.inl i)⟩
  let tw (i : I) : W :=
    ⟨rho.asModuleEquiv.symm (t i), hgen (Sum.inr (Sum.inl i))⟩
  have haw (i) : inc (aw i) = a i := rho.asModuleEquiv.apply_symm_apply _
  have htw (i) : inc (tw i) = t i := rho.asModuleEquiv.apply_symm_apply _
  have hsigmaFaith : Function.Injective sigma := by
    intro g h heq
    by_contra hne
    apply hb (g, h) hne
    let w : W := ⟨rho.asModuleEquiv.symm (b (g, h)),
      hgen (Sum.inr (Sum.inr (g, h)))⟩
    have hw : inc w = b (g, h) := rho.asModuleEquiv.apply_symm_apply _
    simpa only [haction, hw] using congrArg (fun f : Module.End k W ↦ inc (f w)) heq
  have hsigmaSemi : IsSemisimpleModule k[G] sigma.asModule :=
    ofModule_submodule_semisimple rho hsemi W
  have hregularW : ∀ i, ∃ w : W, ∀ g : G,
      g ∈ (P i : Subgroup G) → sigma g w = w → g = 1 := by
    intro i
    refine ⟨aw i, fun g hg hfix ↦ ha i g hg ?_⟩
    simpa only [haction, haw] using congrArg inc hfix
  obtain ⟨v, hv⟩ := exists_translated_regular_sylows_finiteField
    sigma hsigmaFaith hsigmaSemi p hp hinj P hregularW tw
  refine ⟨inc v, fun i g hg hfix ↦ hv i g hg ?_⟩
  apply hinc
  simpa only [haction, map_add, htw] using hfix

end LisiSabatini
