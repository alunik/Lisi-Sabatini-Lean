module

public import Mathlib.GroupTheory.Sylow

/-!
# The Lisi–Sabatini property

This file introduces the exact inclusion-minimal formulation used in the
Lisi–Sabatini conjecture.  In particular, it does not replace a minimal
intersection by the `p`-core, since that lower bound need not be attained by
the intersection of two Sylow subgroups.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

/-- The intersection of a Sylow subgroup with the conjugate selected by `x`. -/
def sylowInter {G : Type*} [Group G] {p : ℕ}
    (P : Sylow p G) (x : G) : Subgroup G :=
  (P : Subgroup G) ⊓ ((x • P : Sylow p G) : Subgroup G)

/-- The conjugator `x` gives an inclusion-minimal Sylow intersection. -/
def IsMinimalSylowInter {G : Type*} [Group G] {p : ℕ}
    (P : Sylow p G) (x : G) : Prop :=
  ∀ y : G, sylowInter P y ≤ sylowInter P x →
    sylowInter P x ≤ sylowInter P y

/--
The Lisi–Sabatini property: every prescribed finite family of Sylow subgroups
for distinct primes admits one conjugator making all intersections minimal.
-/
def HasLisiSabatini (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ {I : Type*} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    ∀ P : ∀ i, Sylow (p i) G,
      ∃ x : G, ∀ i, IsMinimalSylowInter (P i) x

end LisiSabatini

