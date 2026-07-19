import LisiSabatini.ActiveFixedSpaceSpectrum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Counting active elements one central coset at a time

For class-two prime cores with a cyclic center larger than the derived
subgroup, bounding all nonidentity elements by the group order is too
wasteful.  The useful interface is instead a bound on the active elements
in each coset of a central subgroup.  Summing those fiber bounds gives

`#active ≤ (# central cosets) * (active elements per coset)`.

The final corollary is normalized to the `q^(2n+1)` budget used by the
prime-core orbit rows.  This file is deliberately only a counting bridge:
the representation-theoretic assertion that a coset contains at most `q`
active scalar twists remains a separate input.
-/

noncomputable section

namespace LisiSabatini

/-- A finite-set cardinality is bounded by the number of target fibers
times a uniform fiber bound. -/
theorem Finset.card_le_card_mul_of_fiber_card_le
    {A B : Type*} [DecidableEq B]
    (s : Finset A) (f : A → B) (t : Finset B) (q : ℕ)
    (hmaps : ∀ a ∈ s, f a ∈ t)
    (hfiber : ∀ b ∈ t, (s.filter fun a ↦ f a = b).card ≤ q) :
    s.card ≤ t.card * q := by
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  calc
    ∑ b ∈ t, (s.filter fun a ↦ f a = b).card ≤
        ∑ _b ∈ t, q := by
      exact Finset.sum_le_sum fun b hb ↦ hfiber b hb
    _ = t.card * q := by simp

/-- If each coset of a normal subgroup `Z` contains at most `q` active
elements, the whole active spectrum has size at most `|P/Z| * q`. -/
theorem card_nonzeroFixingElements_le_quotient_mul_of_coset_active_le
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (P : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype P]
    (Z : Subgroup P) [Z.Normal] (q : ℕ)
    (hcoset : ∀ c : (P ⧸ Z),
      {x : P | x ∈ nonzeroFixingElements P ∧
        QuotientGroup.mk' Z x = c}.ncard ≤ q) :
    (nonzeroFixingElements P).card ≤ Nat.card (P ⧸ Z) * q := by
  classical
  have h := Finset.card_le_card_mul_of_fiber_card_le
    (nonzeroFixingElements P) (QuotientGroup.mk' Z)
    (Finset.univ : Finset (P ⧸ Z)) q
    (by intro a ha; simp) (by
      intro c hc
      simpa [← Set.ncard_coe_finset] using hcoset c)
  simpa [Nat.card_eq_fintype_card] using h

/-- Row-normalized form of central-coset active counting. -/
theorem card_nonzeroFixingElements_le_prime_pow_two_mul_add_one_of_coset_active_le
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (P : Subgroup (LinearMap.GeneralLinearGroup R V)) [Fintype P]
    (Z : Subgroup P) [Z.Normal] (q n : ℕ)
    (hquot : Nat.card (P ⧸ Z) = q ^ (2 * n))
    (hcoset : ∀ c : (P ⧸ Z),
      {x : P | x ∈ nonzeroFixingElements P ∧
        QuotientGroup.mk' Z x = c}.ncard ≤ q) :
    (nonzeroFixingElements P).card ≤ q ^ (2 * n + 1) := by
  calc
    (nonzeroFixingElements P).card ≤ Nat.card (P ⧸ Z) * q :=
      card_nonzeroFixingElements_le_quotient_mul_of_coset_active_le
        P Z q hcoset
    _ = q ^ (2 * n + 1) := by rw [hquot, pow_succ]

end LisiSabatini
