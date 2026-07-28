module

public import LisiSabatini.AlternatingSylowQuadraticEnvelope
public import LisiSabatini.AlternatingSylowQuadraticFormula
public import LisiSabatini.NilpotentIntersectionCorollaries
public import LisiSabatini.SylowPairQuadraticAssembly

/-!
# The Lisi--Sabatini conjecture for alternating groups of degree at least 40

The first of two arbitrary prime-indexed families of Sylow subgroups of
`A_n` is lifted to linked Sylow rows of `S_n`.  The binary row uses the
restricted index-two transfer, which charges only even permutation classes;
odd-prime rows use the unrestricted transfer.  Their exact quadratic costs
are the alternating cycle profiles.  The cost is independent of the second
Sylow row.  The uniform profile envelope leaves a strict factor-four budget,
so the mixed bad-conjugator union cannot cover `A_n`.

The resulting mixed Sylow theorem also gives trivial intersections between
suitable conjugates of any two, and hence any three, nilpotent subgroups.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI

/-- In `A_n`, for `n ≥ 40`, one conjugator simultaneously makes every
prescribed mixed Sylow intersection trivial. -/
theorem exists_common_mixedSylowInter_bot_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n)
    {I : Type uI} [Finite I]
    (p : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin n))) :
    ∃ x : alternatingGroup (Fin n),
      ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  letI := Fintype.ofFinite I
  have hnTwo : 2 ≤ n := by omega
  apply
    exists_common_mixedSylowInter_bot_of_normalized_cost_sum_lt_one
      p hp P Q
  let S : ∀ i, Sylow (p i) (Equiv.Perm (Fin n)) :=
    fun i ↦ Classical.choose (P i).exists_comap_subtype_eq
  have hSP (i : I) :
      (S i).comap (alternatingGroup (Fin n)).subtype = P i :=
    Classical.choose_spec (P i).exists_comap_subtype_eq
  have hrow (i : I) :
      normalizedSameRowSylowQuadraticCost
          (alternatingGroup (Fin n)) (P i) ≤
        4 * alternatingSylowProfileQuadraticCost n (p i) := by
    by_cases htwo : p i = 2
    · have profile_of_eq_two :
          ∀ (q : ℕ) (hq : q = 2)
              (R : Sylow q (Equiv.Perm (Fin n))),
            normalizedSameRowSylowQuadraticCostMeetingSubgroup
                (alternatingGroup (Fin n)) R =
              alternatingSylowProfileQuadraticCost n q := by
        intro q hq R
        subst q
        exact
          normalizedSameRowSylowQuadraticCostMeetingAlternating_perm_eq_profile
            R
      have hformula :
          normalizedSameRowSylowQuadraticCostMeetingSubgroup
              (alternatingGroup (Fin n)) (S i) =
            alternatingSylowProfileQuadraticCost n (p i) :=
        profile_of_eq_two (p i) htwo (S i)
      calc
        normalizedSameRowSylowQuadraticCost
              (alternatingGroup (Fin n)) (P i) ≤
            4 *
              normalizedSameRowSylowQuadraticCostMeetingSubgroup
                (alternatingGroup (Fin n)) (S i) :=
          alternatingLinkedRowQuadraticTransfer_restricted
            hnTwo (S i) (P i) (hSP i)
        _ = 4 * alternatingSylowProfileQuadraticCost n (p i) := by
          rw [hformula]
    · calc
        normalizedSameRowSylowQuadraticCost
              (alternatingGroup (Fin n)) (P i) ≤
            4 *
              normalizedSameRowSylowQuadraticCost
                (Equiv.Perm (Fin n)) (S i) :=
          alternatingLinkedRowQuadraticTransfer
            hnTwo (S i) (P i) (hSP i)
        _ = 4 * symmetricSylowProfileQuadraticCost n (p i) := by
          rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile
            (hp i) (S i)]
        _ = 4 * alternatingSylowProfileQuadraticCost n (p i) := by
          rw [alternatingSylowProfileQuadraticCost, if_neg htwo]
  have hprofile :
      (∑ i : I, alternatingSylowProfileQuadraticCost n (p i)) <
        1 / 4 := by
    simpa using
      sum_alternatingSylowProfileQuadraticCost_lt_one_div_four
        (n := n) (Finset.univ : Finset I) p hn
        (by simpa using hp)
        hinjective.injOn
  calc
    (∑ i : I,
        normalizedSameRowSylowQuadraticCost
          (alternatingGroup (Fin n)) (P i)) ≤
        ∑ i : I, 4 * alternatingSylowProfileQuadraticCost n (p i) :=
      Finset.sum_le_sum fun i _hi ↦ hrow i
    _ = 4 *
        ∑ i : I, alternatingSylowProfileQuadraticCost n (p i) := by
      rw [Finset.mul_sum]
    _ < 1 := by nlinarith

/-- Same-row specialization of
`exists_common_mixedSylowInter_bot_alternatingGroup_ge_forty`. -/
theorem exists_common_sylowInter_bot_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n)
    {I : Type uI} [Finite I]
    (p : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P : ∀ i, Sylow (p i) (alternatingGroup (Fin n))) :
    ∃ x : alternatingGroup (Fin n), ∀ i, sylowInter (P i) x = ⊥ := by
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_alternatingGroup_ge_forty
      n hn p hp hinjective P P
  exact
    ⟨x, fun i ↦ by
      simpa only [mixedSylowInter, sylowInter] using hx i⟩

/-- Alternating groups of degree at least forty satisfy mixed two-row
Sylow synchronization with trivial intersections. -/
theorem mixedTwoSylowBotSynchronization_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasMixedTwoSylowBotSynchronization.{0, uI}
      (alternatingGroup (Fin n)) := by
  intro I _ p hp hinjective P Q
  exact
    exists_common_mixedSylowInter_bot_alternatingGroup_ge_forty
      n hn p hp hinjective P Q

/-- Any two nilpotent subgroups of `A_n`, for `n ≥ 40`, admit a relative
conjugate with trivial intersection. -/
theorem mixedNilpotentIntersectionTrivial_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    MixedNilpotentIntersectionTrivial (alternatingGroup (Fin n)) :=
  mixedNilpotentIntersectionTrivial_of_mixedSylowBot
    (mixedTwoSylowBotSynchronization_alternatingGroup_ge_forty n hn)

/-- Any three nilpotent subgroups of `A_n`, for `n ≥ 40`, admit two
relative conjugates with trivial common intersection. -/
theorem threeNilpotentIntersectionTrivial_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    ThreeNilpotentIntersectionTrivial (alternatingGroup (Fin n)) :=
  threeNilpotentIntersectionTrivial_of_mixedTwo
    (mixedNilpotentIntersectionTrivial_alternatingGroup_ge_forty n hn)

/-- The Lisi--Sabatini property for every alternating group of degree at
least forty. -/
theorem hasLisiSabatini_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasLisiSabatini (alternatingGroup (Fin n)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_sylowInter_bot_alternatingGroup_ge_forty
      n hn p hp hinjective P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  rw [hx i]
  exact bot_le

end LisiSabatini
