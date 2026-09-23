module

public import LisiSabatini.LinearAction
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.PGroup

/-!
# The translated regularity input for the good solvable case

This file specifies the one-vector linear input needed by the group-theoretic
reduction. All primes are permitted, including an acting 2-component and
characteristic 2. In place of the odd-order restrictions in the older
normal-component predicate, each component is assumed individually to have
a regular vector.

The predicates below are explicit hypotheses, not axioms or assertions that
the translated regularity theorem has already been proved.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uV

/-- Independent translates of regular loci for distinct normal prime-power
components have a common point, provided each regular locus is nonempty. -/
def RegularNormalComponentSynchronizationOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    ∀ H : I → Subgroup K,
      (∀ i, (H i).Normal) →
      (∀ i, IsPGroup (p i) (H i)) →
      (∀ i, ∃ w : V,
        MulAction.stabilizer ((H i).map K.subtype) w = ⊥) →
      ∀ t : I → V,
        ∃ v : V, ∀ i,
          MulAction.stabilizer ((H i).map K.subtype) (v + t i) = ⊥

/-- The global, finite prime-field coordinate form needed for induction on
finite groups. This is a named linear hypothesis, with no solvability or
parity restriction hidden in its definition. -/
def RegularNormalComponentSynchronization : Prop :=
  ∀ (r : ℕ) [Fact r.Prime] (d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))),
    RegularNormalComponentSynchronizationOn.{uI}
      r (Fin d → ZMod r) K

end LisiSabatini
