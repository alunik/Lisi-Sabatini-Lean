import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.RepresentationTheory.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Independently stated paper specifications

This trusted specification imports only Mathlib. It does not import any
`LisiSabatini` declaration. The definitions below spell out the group-theoretic
conclusions used in the paper's Comparator challenges.
-/

noncomputable section

namespace PaperSpecification

universe uG uI

/-- The largest normal `p`-subgroup, expressed as a supremum. -/
def primeCore (p : ℕ) (G : Type uG) [Group G] : Subgroup G :=
  sSup {K : Subgroup G | IsPGroup p K ∧ K.Normal}

/-- The Fitting subgroup, as the supremum of normal nilpotent subgroups. -/
def fitting (G : Type uG) [Group G] : Subgroup G :=
  sSup {K : Subgroup G | K.Normal ∧ Group.IsNilpotent K}

/-- The intersection with the conjugate `x P x⁻¹`. -/
def intersection {G : Type uG} [Group G] {p : ℕ}
    (P : Sylow p G) (x : G) : Subgroup G :=
  (P : Subgroup G) ⊓ ((x • P : Sylow p G) : Subgroup G)

/-- One conjugator attains all the prime cores in a prescribed finite family. -/
def CoreSynchronization (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) → Function.Injective p →
    ∀ P : ∀ i, Sylow (p i) G,
      ∃ x : G, ∀ i, intersection (P i) x = primeCore (p i) G

/-- One conjugator gives inclusion-minimal intersections in every row. -/
def MinimalSynchronization (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) → Function.Injective p →
    ∀ P : ∀ i, Sylow (p i) G,
      ∃ x : G, ∀ i, ∀ y : G,
        intersection (P i) y ≤ intersection (P i) x →
        intersection (P i) x ≤ intersection (P i) y

/-- Every quotient, including `G`, has individual Sylow-core attainment.
The quantification uses surjective homomorphisms. For a finite group,
Sylow conjugacy identifies this with the paper's property (*) in every quotient.
-/
def EveryQuotientHasStar (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ {H : Type uG} [Group H] [Finite H] (f : G →* H),
    Function.Surjective f →
    ∀ p : ℕ, Nat.Prime p →
      ∀ P : Sylow p H, ∃ x : H, intersection P x = primeCore p H

end PaperSpecification
