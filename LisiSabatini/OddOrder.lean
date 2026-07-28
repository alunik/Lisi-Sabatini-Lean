module

public import LisiSabatini.Quotient

/-!
# Trivial two-primary coordinates in odd-order groups

The local affine theorem concerns distinct *odd* primes.  These lemmas justify
discarding a prescribed `p = 2` coordinate before invoking it.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Every Sylow `2`-subgroup of a finite odd-order group is trivial. -/
theorem sylow_two_eq_bot (hodd : Odd (Nat.card G)) (P : Sylow 2 G) :
    (P : Subgroup G) = ⊥ := by
  rw [← Subgroup.card_eq_one, Sylow.card_eq_multiplicity,
    Nat.factorization_eq_zero_of_not_dvd hodd.not_two_dvd_nat, pow_zero]

/-- The `2`-core of a finite odd-order group is trivial. -/
theorem pCore_two_eq_bot (hodd : Odd (Nat.card G)) : pCore 2 G = ⊥ := by
  let P : Sylow 2 G := default
  apply le_antisymm
  · exact (pCore_le_sylow P).trans_eq (sylow_two_eq_bot hodd P)
  · exact bot_le

/-- Every two-primary Sylow intersection already equals its theoretical
lower bound, independently of the conjugator. -/
theorem sylowInter_two_eq_pCore
    (hodd : Odd (Nat.card G)) (P : Sylow 2 G) (x : G) :
    sylowInter P x = pCore 2 G := by
  rw [pCore_two_eq_bot hodd, sylowInter, sylow_two_eq_bot hodd P,
    sylow_two_eq_bot hodd (x • P)]
  simp

end LisiSabatini
