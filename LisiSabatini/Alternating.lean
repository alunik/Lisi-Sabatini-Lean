import LisiSabatini.AlternatingSylowQuadraticEnvelope
import LisiSabatini.AlternatingSylowQuadraticFormula
import LisiSabatini.SylowPairQuadraticAssembly

/-!
# The Lisi--Sabatini conjecture for alternating groups of degree at least 40

An arbitrary prime-indexed family of Sylow subgroups of `A_n` is lifted to
linked Sylow rows of `S_n`.  The binary row uses the restricted index-two
transfer, which charges only even permutation classes; odd-prime rows use
the unrestricted transfer.  Their exact quadratic costs are the alternating
cycle profiles.  The uniform profile envelope leaves a strict factor-four
budget, so the quadratic bad-conjugator union cannot cover `A_n`.
-/

noncomputable section

open scoped BigOperators

namespace LisiSabatini

/-- The Lisi--Sabatini property for every alternating group of degree at
least forty. -/
theorem hasLisiSabatini_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasLisiSabatini (alternatingGroup (Fin n)) := by
  have hnTwo : 2 ≤ n := by omega
  apply hasLisiSabatini_of_normalized_cost_budget
  intro I _ p hp hinjective Q
  let P : ∀ i, Sylow (p i) (Equiv.Perm (Fin n)) :=
    fun i ↦ Classical.choose (Q i).exists_comap_subtype_eq
  have hPQ (i : I) :
      (P i).comap (alternatingGroup (Fin n)).subtype = Q i :=
    Classical.choose_spec (Q i).exists_comap_subtype_eq
  have hrow (i : I) :
      normalizedSameRowSylowQuadraticCost
          (alternatingGroup (Fin n)) (Q i) ≤
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
              (alternatingGroup (Fin n)) (P i) =
            alternatingSylowProfileQuadraticCost n (p i) :=
        profile_of_eq_two (p i) htwo (P i)
      calc
        normalizedSameRowSylowQuadraticCost
              (alternatingGroup (Fin n)) (Q i) ≤
            4 *
              normalizedSameRowSylowQuadraticCostMeetingSubgroup
                (alternatingGroup (Fin n)) (P i) :=
          alternatingLinkedRowQuadraticTransfer_restricted
            hnTwo (P i) (Q i) (hPQ i)
        _ = 4 * alternatingSylowProfileQuadraticCost n (p i) := by
          rw [hformula]
    · calc
        normalizedSameRowSylowQuadraticCost
              (alternatingGroup (Fin n)) (Q i) ≤
            4 *
              normalizedSameRowSylowQuadraticCost
                (Equiv.Perm (Fin n)) (P i) :=
          alternatingLinkedRowQuadraticTransfer
            hnTwo (P i) (Q i) (hPQ i)
        _ = 4 * symmetricSylowProfileQuadraticCost n (p i) := by
          rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile
            (hp i) (P i)]
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
          (alternatingGroup (Fin n)) (Q i)) ≤
        ∑ i : I, 4 * alternatingSylowProfileQuadraticCost n (p i) :=
      Finset.sum_le_sum fun i _hi ↦ hrow i
    _ = 4 *
        ∑ i : I, alternatingSylowProfileQuadraticCost n (p i) := by
      rw [Finset.mul_sum]
    _ < 1 := by nlinarith

end LisiSabatini
