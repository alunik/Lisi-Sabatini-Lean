module

public import LisiSabatini.SymmetricFiniteCertificates.TinyBounds
public import LisiSabatini.SymmetricFiniteCertificates.MixedFamily
public import LisiSabatini.SymmetricFiniteCertificates.S6ThreeCounts
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Tactic.IntervalCases

/-!
# S6 from a binary witness and a Sylow-three certificate

The bounds cover arbitrary independent Sylow rows and every finite family
with distinct prime labels. The binary row uses a single good double coset.
-/

@[expose] public section

namespace LisiSabatini

open SymmetricFiniteCertificates

universe uI

private theorem prime_divisor_card_symmetric_six (p : ℕ) (hp : p.Prime)
    (hd : p ∣ Nat.card (Equiv.Perm (Fin 6))) : p = 2 ∨ p = 3 ∨ p = 5 := by
  rw [S6Tiny.group_card] at hd
  have hfact : p ∣ Nat.factorial 6 := by simpa [Nat.factorial] using hd
  have hle : p ≤ 6 := hp.dvd_factorial.mp hfact
  have htwo := hp.two_le
  interval_cases p
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp)
  · exact Or.inr (Or.inr rfl)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp)

private theorem symmetricSix_three_bad_bound
    (P Q : Sylow 3 (Equiv.Perm (Fin 6))) :
    (mixedSylowPairBadConjugators P Q).ncard ≤ 72 :=
  mixedSylowPairBadConjugators_ncard_le_of_sample_bound
    (by decide) S6Three.sylow3 S6Three.sylow3_bad_card P Q

/-- Arbitrary independent Sylow rows of S6 admit simultaneous trivial intersections. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_six
    {I : Type uI} [Finite I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin 6))) :
    ∃ x : Equiv.Perm (Fin 6), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  exact exists_common_mixedSylowInter_bot_of_235_bad_bounds 464 72 20
    prime_divisor_card_symmetric_six
    symmetricSix_two_bad_bound symmetricSix_three_bad_bound
    symmetricSix_five_bad_bound
    (by rw [S6Tiny.group_card]; norm_num) p hp hinj P Q

/-- Arbitrary prescribed Sylow rows of S6 admit simultaneous trivial self-intersections. -/
theorem exists_common_sylowInter_bot_symmetricGroup_six
    {I : Type uI} [Finite I] (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (P : ∀ i, Sylow (p i) (Equiv.Perm (Fin 6))) :
    ∃ x : Equiv.Perm (Fin 6), ∀ i, sylowInter (P i) x = ⊥ := by
  simpa only [mixedSylowInter, sylowInter] using
    exists_common_mixedSylowInter_bot_symmetricGroup_six p hp hinj P P

/-- Lisi–Sabatini for S6, with arbitrary finite prime-labelled families. -/
theorem hasLisiSabatini_symmetricGroup_six :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin 6)) := by
  exact hasLisiSabatini_of_mixed_235_bad_bounds 464 72 20
    prime_divisor_card_symmetric_six
    symmetricSix_two_bad_bound symmetricSix_three_bad_bound
    symmetricSix_five_bad_bound
    (by rw [S6Tiny.group_card]; norm_num)

end LisiSabatini
