module

public import LisiSabatini.SymmetricFiniteCertificates.TinyBounds
public import LisiSabatini.SymmetricFiniteCertificates.MixedFamily
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Tactic.IntervalCases

/-!
# S5 from one tiny Sylow-two certificate

The bounds cover arbitrary independent Sylow rows and every finite family
with distinct prime labels. The binary row uses a single good double coset.
-/

@[expose] public section

namespace LisiSabatini

open SymmetricFiniteCertificates

universe uI

private theorem prime_divisor_card_symmetric_five (p : ℕ) (hp : p.Prime)
    (hd : p ∣ Nat.card (Equiv.Perm (Fin 5))) : p = 2 ∨ p = 3 ∨ p = 5 := by
  rw [S5Tiny.group_card] at hd
  have hfact : p ∣ Nat.factorial 5 := by simpa [Nat.factorial] using hd
  have hle : p ≤ 5 := hp.dvd_factorial.mp hfact
  have htwo := hp.two_le
  interval_cases p
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp)
  · exact Or.inr (Or.inr rfl)

/-- Arbitrary independent Sylow rows of S5 admit simultaneous trivial intersections. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_five
    {I : Type uI} [Finite I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin 5))) :
    ∃ x : Equiv.Perm (Fin 5), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  exact exists_common_mixedSylowInter_bot_of_235_bad_bounds 56 12 20
    prime_divisor_card_symmetric_five
    symmetricFive_two_bad_bound symmetricFive_three_bad_bound
    symmetricFive_five_bad_bound
    (by rw [S5Tiny.group_card]; norm_num) p hp hinj P Q

/-- Arbitrary prescribed Sylow rows of S5 admit simultaneous trivial self-intersections. -/
theorem exists_common_sylowInter_bot_symmetricGroup_five
    {I : Type uI} [Finite I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (P : ∀ i, Sylow (p i) (Equiv.Perm (Fin 5))) :
    ∃ x : Equiv.Perm (Fin 5), ∀ i, sylowInter (P i) x = ⊥ := by
  simpa only [mixedSylowInter, sylowInter] using
    exists_common_mixedSylowInter_bot_symmetricGroup_five p hp hinj P P

/-- Lisi–Sabatini for S5, with arbitrary finite prime-labelled families. -/
theorem hasLisiSabatini_symmetricGroup_five :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin 5)) := by
  exact hasLisiSabatini_of_mixed_235_bad_bounds 56 12 20
    prime_divisor_card_symmetric_five
    symmetricFive_two_bad_bound symmetricFive_three_bad_bound
    symmetricFive_five_bad_bound
    (by rw [S5Tiny.group_card]; norm_num)

end LisiSabatini
