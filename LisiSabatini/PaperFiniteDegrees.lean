module

public import LisiSabatini.PaperFiniteDegreeCertificates
public import LisiSabatini.PaperSmallAlternatingCertificates
public import LisiSabatini.NormalSubgroupQuadraticCost
public import LisiSabatini.Alternating
public import LisiSabatini.Symmetric
public import LisiSabatini.AlternatingExactSylowCost
public import LisiSabatini.CyclicSylowQuadraticBound

/-!
# Finite-degree symmetric and alternating endpoints

Exact polynomial and rational certificates are kept in the independent
arithmetic module. This file turns their universal prime-family budgets
into simultaneous trivial intersections for arbitrary prescribed Sylow
rows. The degree-seven endpoints also count cyclic prime-order subgroups.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

/-! ## Group-theoretic endpoints -/

universe uI

/-- Mixed trivial Sylow intersections in the certified finite symmetric degrees. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_finite_degrees
    (n : ℕ) (hn : n = 11 ∨ n = 13 ∨ n = 15 ∨ (17 ≤ n ∧ n < 40))
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
        sum_symmetricSylowProfileQuadraticCost_lt_one_finite_degrees
          (Finset.univ : Finset I) p n hn
          (by simpa using hp)
          hinjective.injOn

/-- Lisi–Sabatini in the certified finite symmetric degrees. -/
theorem hasLisiSabatini_symmetricGroup_finite_degrees
    (n : ℕ) (hn : n = 11 ∨ n = 13 ∨ n = 15 ∨ (17 ≤ n ∧ n < 40)) :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_symmetricGroup_finite_degrees n hn p hp hinjective P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  have hbot : sylowInter (P i) x = ⊥ := by
    simpa only [mixedSylowInter, sylowInter] using hx i
  rw [hbot]
  exact bot_le

/-- The sharper index-two transfer closes the additional finite
alternating degrees without constructing ambient Sylow representatives. -/
theorem exists_common_mixedSylowInter_bot_alternatingGroup_finite_degrees
    (n : ℕ) (hn : n = 11 ∨ (13 ≤ n ∧ n < 40))
    {I : Type uI} [Finite I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin n))) :
    ∃ x : alternatingGroup (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let := Fintype.ofFinite I
  have hnTwo : 2 ≤ n := by omega
  apply exists_common_mixedSylowInter_bot_of_normalized_cost_sum_lt_one p hp P Q
  have hprofile :
      (∑ i : I, alternatingSylowProfileQuadraticCost n (p i)) < (1 : ℝ) / 2 := by
    simpa using sum_alternatingSylowProfileQuadraticCost_lt_one_div_two_finite_degrees
      (n := n) (Finset.univ : Finset I) p hn (by simpa using hp) hinjective.injOn
  calc
    (∑ i : I, normalizedSameRowSylowQuadraticCost
        (alternatingGroup (Fin n)) (P i)) ≤
        ∑ i : I, 2 * alternatingSylowProfileQuadraticCost n (p i) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact normalizedQuadraticCost_alternating_le_two_profile hnTwo (hp i) (P i)
    _ = 2 * ∑ i : I, alternatingSylowProfileQuadraticCost n (p i) := by
      rw [Finset.mul_sum]
    _ < 1 := by linarith

/-- Lisi–Sabatini in the certified finite alternating degrees. -/
theorem hasLisiSabatini_alternatingGroup_finite_degrees
    (n : ℕ) (hn : n = 11 ∨ (13 ≤ n ∧ n < 40)) :
    HasLisiSabatini.{0, uI} (alternatingGroup (Fin n)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_alternatingGroup_finite_degrees n hn p hp hinjective P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  have hbot : sylowInter (P i) x = ⊥ := by
    simpa only [mixedSylowInter, sylowInter] using hx i
  rw [hbot]
  exact bot_le

/-- Counting cyclic prime-order subgroups closes degree seven for S_n. -/
theorem exists_common_mixedSylowInter_bot_symmetricGroup_seven
    {I : Type uI} [Finite I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin 7))) :
    ∃ x : Equiv.Perm (Fin 7), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let := Fintype.ofFinite I
  apply exists_common_mixedSylowInter_bot_of_cyclic_cost_sum_lt_one p hp P Q
  calc
    (∑ i : I, normalizedSameRowSylowQuadraticCost (Equiv.Perm (Fin 7)) (P i) /
        ((p i - 1 : ℕ) : ℝ)) =
        ∑ i : I, symmetricSylowProfileQuadraticCost 7 (p i) / ((p i - 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile (hp i) (P i)]
    _ < 1 := by
      simpa using sum_symmetricSylowProfileCyclicCost_seven_lt_one
        (Finset.univ : Finset I) p (by simpa using hp) hinjective.injOn

/-- The cyclic-subgroup budget also closes A7 through the factor-two transfer. -/
theorem exists_common_mixedSylowInter_bot_alternatingGroup_seven
    {I : Type uI} [Finite I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin 7))) :
    ∃ x : alternatingGroup (Fin 7), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let := Fintype.ofFinite I
  apply exists_common_mixedSylowInter_bot_of_cyclic_cost_sum_lt_one p hp P Q
  have hprofile :
      (∑ i : I, alternatingSylowProfileQuadraticCost 7 (p i) /
        ((p i - 1 : ℕ) : ℝ)) < (1 : ℝ) / 2 := by
    simpa using sum_alternatingSylowProfileCyclicCost_seven_lt_one_div_two
      (Finset.univ : Finset I) p (by simpa using hp) hinjective.injOn
  calc
    (∑ i : I, normalizedSameRowSylowQuadraticCost (alternatingGroup (Fin 7)) (P i) /
        ((p i - 1 : ℕ) : ℝ)) ≤
        ∑ i : I, (2 * alternatingSylowProfileQuadraticCost 7 (p i)) /
          ((p i - 1 : ℕ) : ℝ) := by
      apply Finset.sum_le_sum
      intro i _hi
      exact div_le_div_of_nonneg_right
        (normalizedQuadraticCost_alternating_le_two_profile (by norm_num) (hp i) (P i))
        (Nat.cast_nonneg _)
    _ = 2 * ∑ i : I, alternatingSylowProfileQuadraticCost 7 (p i) /
        ((p i - 1 : ℕ) : ℝ) := by
      simp only [mul_div_assoc, Finset.mul_sum]
    _ < 1 := by linarith

/-- Lisi–Sabatini for the symmetric group of degree seven. -/
theorem hasLisiSabatini_symmetricGroup_seven :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin 7)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_symmetricGroup_seven p hp hinjective P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  have hbot : sylowInter (P i) x = ⊥ := by
    simpa only [mixedSylowInter, sylowInter] using hx i
  rw [hbot]
  exact bot_le

/-- Lisi–Sabatini for the alternating group of degree seven. -/
theorem hasLisiSabatini_alternatingGroup_seven :
    HasLisiSabatini.{0, uI} (alternatingGroup (Fin 7)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_alternatingGroup_seven p hp hinjective P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  have hbot : sylowInter (P i) x = ⊥ := by
    simpa only [mixedSylowInter, sylowInter] using hx i
  rw [hbot]
  exact bot_le

/-- Exact normal-subgroup costs close the five additional small
alternating degrees using cyclic prime-order witnesses. -/
theorem exists_common_mixedSylowInter_bot_alternatingGroup_small_degrees
    (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 12)
    {I : Type uI} [Finite I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin n))) :
    ∃ x : alternatingGroup (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let := Fintype.ofFinite I
  apply exists_common_mixedSylowInter_bot_of_cyclic_cost_sum_lt_one p hp P Q
  calc
    (∑ i : I, normalizedSameRowSylowQuadraticCost (alternatingGroup (Fin n)) (P i) /
        ((p i - 1 : ℕ) : ℝ)) =
        ∑ i : I, alternatingSylowProfileQuadraticCost n (p i) / ((p i - 1 : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [normalizedQuadraticCost_alternating_eq_profile (hp i) (P i)]
    _ < 1 := by
      simpa using sum_alternatingSylowProfileCyclicCost_small_degrees_lt_one
        (Finset.univ : Finset I) p n hn (by simpa using hp) hinjective.injOn

/-- Lisi–Sabatini for the five additional small alternating degrees. -/
theorem hasLisiSabatini_alternatingGroup_small_degrees
    (n : ℕ) (hn : n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 12) :
    HasLisiSabatini.{0, uI} (alternatingGroup (Fin n)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_alternatingGroup_small_degrees n hn p hp hinjective P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  have hbot : sylowInter (P i) x = ⊥ := by
    simpa only [mixedSylowInter, sylowInter] using hx i
  rw [hbot]
  exact bot_le

/-- Every alternating degree at least five except eight now admits one
conjugator making all prescribed mixed Sylow intersections trivial. -/
theorem exists_common_mixedSylowInter_bot_alternatingGroup_ge_five_of_ne_eight
    (n : ℕ) (hn : 5 ≤ n) (hne : n ≠ 8)
    {I : Type uI} [Finite I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinjective : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin n))) :
    ∃ x : alternatingGroup (Fin n), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  by_cases hlarge : 40 ≤ n
  · exact exists_common_mixedSylowInter_bot_alternatingGroup_ge_forty
      n hlarge p hp hinjective P Q
  by_cases hsmall : n = 5 ∨ n = 6 ∨ n = 9 ∨ n = 10 ∨ n = 12
  · exact exists_common_mixedSylowInter_bot_alternatingGroup_small_degrees
      n hsmall p hp hinjective P Q
  by_cases hseven : n = 7
  · subst n
    exact exists_common_mixedSylowInter_bot_alternatingGroup_seven p hp hinjective P Q
  have hmiddle : n = 11 ∨ (13 ≤ n ∧ n < 40) := by omega
  exact exists_common_mixedSylowInter_bot_alternatingGroup_finite_degrees
    n hmiddle p hp hinjective P Q

/-- Lisi–Sabatini for every A_n with n≥5 and n≠8. -/
theorem hasLisiSabatini_alternatingGroup_ge_five_of_ne_eight
    (n : ℕ) (hn : 5 ≤ n) (hne : n ≠ 8) :
    HasLisiSabatini.{0, uI} (alternatingGroup (Fin n)) := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_alternatingGroup_ge_five_of_ne_eight
      n hn hne p hp hinjective P P
  refine ⟨x, fun i y _hy ↦ ?_⟩
  have hbot : sylowInter (P i) x = ⊥ := by
    simpa only [mixedSylowInter, sylowInter] using hx i
  rw [hbot]
  exact bot_le

end LisiSabatini
