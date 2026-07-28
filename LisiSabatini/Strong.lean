module

public import LisiSabatini.PCore

/-!
# The strong Lisi–Sabatini property

`StrongLisiSabatini G` asks for one conjugator for which every prescribed
Sylow intersection is exactly the corresponding `p`-core.

## Conjugation convention

Mathlib's action is `x • P = (MulAut.conj x) • P`.  Thus its underlying
elements are `x * p * x⁻¹`, the convention commonly written `x P x⁻¹`.
The definition below uses `sylowInter`, so it inherits exactly this convention.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG uI

/-- The synchronized strong conclusion: all prescribed Sylow intersections
simultaneously attain their theoretical lower bounds, the relevant `p`-cores. -/
def StrongLisiSabatini (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    ∀ P : ∀ i, Sylow (p i) G,
      ∃ x : G, ∀ i, sylowInter (P i) x = pCore (p i) G

/-- The strong property holds for a trivial group.  This is the base case for
normal-tower induction. -/
theorem strongLisiSabatini_of_subsingleton
    {G : Type uG} [Group G] [Finite G] [Subsingleton G] :
    StrongLisiSabatini.{uG, uI} G := by
  intro I _ p _hp _hinj P
  refine ⟨1, fun i ↦ ?_⟩
  exact Subsingleton.elim (sylowInter (P i) 1) (pCore (p i) G)

/-- Attaining the `p`-core is stronger than inclusion-minimality; hence the
strong synchronized property implies the exact Lisi–Sabatini property. -/
theorem StrongLisiSabatini.hasLisiSabatini
    {G : Type uG} [Group G] [Finite G]
    (hG : StrongLisiSabatini.{uG, uI} G) : HasLisiSabatini.{uG, uI} G := by
  intro I _ p hp hinj P
  obtain ⟨x, hx⟩ := hG p hp hinj P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  rw [hx i]
  exact pCore_le_sylowInter (P i) y

end LisiSabatini
