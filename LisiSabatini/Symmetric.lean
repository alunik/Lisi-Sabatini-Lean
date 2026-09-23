module

public import LisiSabatini.SymmetricSylowQuadraticEnvelope
public import LisiSabatini.AlternatingSylowQuadraticFormula
public import LisiSabatini.NilpotentIntersectionCorollaries
public import LisiSabatini.SylowPairQuadraticAssembly
public import LisiSabatini.Strong

/-!
# The Lisi--Sabatini conjecture for symmetric groups of degree at least 40

For each pair of prescribed Sylow rows of `S_n`, the exact normalized
quadratic bad-conjugator cost is the symmetric cycle profile of either row.
The uniform profile envelope has total cost strictly below one in degree at
least forty.  Consequently one conjugator lies outside every mixed bad row
simultaneously, so all the prescribed Sylow intersections are trivial.

This proves more than inclusion-minimality: every intersection is the trivial
subgroup, and hence is equal to the corresponding prime core.  It also gives
trivial intersections between suitable conjugates of any two, and hence any
three, nilpotent subgroups.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI

/-- In `S_n`, for `n ≥ 40`, one conjugator simultaneously makes every
prescribed mixed Sylow intersection trivial.

The primes labelling the rows are required to be distinct, exactly as in the
Lisi--Sabatini conjecture. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n)
    {I : Type uI} [Finite I]
    (p : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin n))) :
    ∃ x : Equiv.Perm (Fin n),
      ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let := Fintype.ofFinite I
  apply
    exists_common_mixedSylowInter_bot_of_normalized_cost_sum_lt_one
      p hp P Q
  calc
    (∑ i : I,
        normalizedSameRowSylowQuadraticCost
          (Equiv.Perm (Fin n)) (P i)) =
        ∑ i : I, symmetricSylowProfileQuadraticCost n (p i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact normalizedSameRowSylowQuadraticCost_perm_eq_profile
        (hp i) (P i)
    _ < 1 := by
      simpa using
        sum_symmetricSylowProfileQuadraticCost_lt_one
          (Finset.univ : Finset I) p n hn
          (by simpa using hp)
          hinjective.injOn

/-- Same-row specialization of
`exists_common_mixedSylowInter_bot_symmetricGroup_ge_forty`. -/
theorem exists_common_sylowInter_bot_symmetricGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n)
    {I : Type uI} [Finite I]
    (p : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P : ∀ i, Sylow (p i) (Equiv.Perm (Fin n))) :
    ∃ x : Equiv.Perm (Fin n), ∀ i, sylowInter (P i) x = ⊥ := by
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_symmetricGroup_ge_forty
      n hn p hp hinjective P P
  exact
    ⟨x, fun i ↦ by
      simpa only [mixedSylowInter, sylowInter] using hx i⟩

/-- Symmetric groups of degree at least forty satisfy mixed two-row
Sylow synchronization with trivial intersections. -/
theorem mixedTwoSylowBotSynchronization_symmetricGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasMixedTwoSylowBotSynchronization.{0, uI}
      (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinjective P Q
  exact
    exists_common_mixedSylowInter_bot_symmetricGroup_ge_forty
      n hn p hp hinjective P Q

/-- Any two nilpotent subgroups of `S_n`, for `n ≥ 40`, admit a relative
conjugate with trivial intersection. -/
theorem mixedNilpotentIntersectionTrivial_symmetricGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    MixedNilpotentIntersectionTrivial (Equiv.Perm (Fin n)) :=
  mixedNilpotentIntersectionTrivial_of_mixedSylowBot
    (mixedTwoSylowBotSynchronization_symmetricGroup_ge_forty n hn)

/-- Any three nilpotent subgroups of `S_n`, for `n ≥ 40`, admit two
relative conjugates with trivial common intersection. -/
theorem threeNilpotentIntersectionTrivial_symmetricGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    ThreeNilpotentIntersectionTrivial (Equiv.Perm (Fin n)) :=
  threeNilpotentIntersectionTrivial_of_mixedTwo
    (mixedNilpotentIntersectionTrivial_symmetricGroup_ge_forty n hn)

/-- **Strong Lisi--Sabatini for symmetric groups of degree at least forty.**

One conjugator simultaneously realizes the theoretical lower bound in every
prescribed prime row.  In fact, both that lower bound and every selected
intersection are trivial. -/
theorem strongLisiSabatini_symmetricGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    StrongLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_sylowInter_bot_symmetricGroup_ge_forty
      n hn p hp hinjective P
  refine ⟨x, fun i ↦ le_antisymm ?_ ?_⟩
  · rw [hx i]
    exact bot_le
  · exact pCore_le_sylowInter (P i) x

/-- The original inclusion-minimal Lisi--Sabatini conclusion for every
symmetric group of degree at least forty. -/
theorem hasLisiSabatini_symmetricGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) :=
  StrongLisiSabatini.hasLisiSabatini
    (strongLisiSabatini_symmetricGroup_ge_forty n hn)

end LisiSabatini
