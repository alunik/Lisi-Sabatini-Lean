module

public import LisiSabatini.NilpotentTranslatedRegularityFiniteSpan
public import LisiSabatini.NilpotentTranslatedRegularityInfiniteField

/-!
# Translated regular Sylow orbits

The paper's translated-orbit proposition over an arbitrary field and module.
Finite fields reduce to a finite faithful invariant span. Over infinite
fields, avoidance of finitely many proper affine subspaces suffices.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

/-- A faithful completely reducible module for a finite nilpotent group
has simultaneous independently translated regular Sylow vectors whenever
each selected Sylow subgroup has an individual regular vector.
No finiteness or dimension hypothesis is imposed on the field or module. -/
theorem exists_translated_regular_sylows
    {k G V I : Type*} [Field k] [Group G] [Finite G]
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
  rcases finite_or_infinite k with hfinite | hinfinite
  · let : Finite k := hfinite
    exact exists_translated_regular_sylows_finiteField_arbitraryModule
      rho hfaith hsemi p hp hinj P hregular t
  · let : Infinite k := hinfinite
    have hfaithUnits : Function.Injective rho.asGroupHom := by
      intro g h heq
      exact hfaith (congrArg Units.val heq)
    obtain ⟨v, hv⟩ :=
      exists_regular_translates_of_faithful_representation_over_infinite_field
        rho.asGroupHom hfaithUnits t
    refine ⟨v, fun i g _hg hfix ↦ ?_⟩
    apply (Subgroup.eq_bot_iff_forall _).mp (hv i) g
    exact (mem_actionPointStabilizer rho.asGroupHom (v + t i) g).mpr hfix

end LisiSabatini
