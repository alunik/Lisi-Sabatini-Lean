module

public import LisiSabatini.SylowDoubleCosetBound
public import LisiSabatini.A8DoubleCosetBudget
public import LisiSabatini.NormalSubgroupQuadraticCost

/-!
# Degree eight from one trivial Sylow-two intersection

A single certified good Sylow-two pair supplies 4096 good conjugators. The
remaining three primes are bounded by their exact quadratic cycle profiles.
The reduction below isolates the only concrete group certificate required.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

private theorem a8_bad_probability_le_row_budget
    (R : Sylow 2 (alternatingGroup (Fin 8)))
    (hcardR : Nat.card R = 64) (hR : ∃ g, sylowInter R g = ⊥)
    (p : ℕ) (hp : p.Prime)
    (P Q : Sylow p (alternatingGroup (Fin 8))) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) /
        Nat.card (alternatingGroup (Fin 8)) ≤
      if p = 2 then (251 : ℝ) / 315 else alternatingSylowProfileQuadraticCost 8 p := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases htwo : p = 2
  · subst p
    rw [ite_eq_left rfl]
    have h := bad_probability_le_of_one_trivial_pair R hR P Q
    have hG : Nat.card (alternatingGroup (Fin 8)) = 20160 := by
      rw [nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    rw [hcardR, hG] at h
    rw [hG]
    norm_num at h ⊢
    exact h
  · rw [ite_eq_right htwo, ← normalizedQuadraticCost_alternating_eq_profile hp P]
    unfold normalizedSameRowSylowQuadraticCost
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h := ncard_mixedSylowPairBadConjugators_le_quadraticClass_sum P Q
    simp_rw [mixedSylowPairQuadraticClassTerm_eq_sameRow P Q P] at h
    exact_mod_cast h

/-- The exact degree-eight row budgets sum to less than one for every
injectively prime-labelled finite family. -/
theorem sum_a8_double_coset_row_budget_lt_one
    {I : Type*} [Fintype I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    (∑ i, if p i = 2 then (251 : ℝ) / 315
      else alternatingSylowProfileQuadraticCost 8 (p i)) < 1 := by
  classical
  let s := (Finset.univ : Finset I).filter (fun i ↦ p i = 2)
  let t := (Finset.univ : Finset I).filter (fun i ↦ p i ≠ 2)
  have hs : s.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro i hi j hj
    apply hinj
    exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hj).2.symm
  have hsR : (s.card : ℝ) ≤ 1 := by exact_mod_cast hs
  have hbinary : (∑ _i ∈ s, (251 : ℝ) / 315) ≤ (251 : ℝ) / 315 := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hodd := a8DoubleCosetBudget_restricted_lt_one t p
    (fun i _ ↦ hp i) (fun i hi ↦ (Finset.mem_filter.mp hi).2)
    (fun _ _ _ _ hij ↦ hinj hij)
  calc
    _ = (∑ _i ∈ s, (251 : ℝ) / 315) +
        ∑ i ∈ t, alternatingSylowProfileQuadraticCost 8 (p i) := by
      rw [Finset.sum_ite]
    _ ≤ (251 : ℝ) / 315 + ∑ i ∈ t, alternatingSylowProfileQuadraticCost 8 (p i) :=
      by linarith
    _ < 1 := hodd

/-- One certified trivial Sylow-two intersection suffices for all mixed Sylow
families of A8. The witness and its subgroup order remain explicit inputs. -/
theorem exists_common_mixedSylowInter_bot_A8_of_one_pair
    (R : Sylow 2 (alternatingGroup (Fin 8)))
    (hcardR : Nat.card R = 64) (hR : ∃ g, sylowInter R g = ⊥)
    {I : Type*} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (alternatingGroup (Fin 8))) :
    ∃ x : alternatingGroup (Fin 8), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let := Fintype.ofFinite I
  apply exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt p P Q
  have hsum :
      (∑ i, ((mixedSylowPairBadConjugators (P i) (Q i)).ncard : ℝ) /
        Nat.card (alternatingGroup (Fin 8))) < 1 :=
    (Finset.sum_le_sum (fun i _ ↦
      a8_bad_probability_le_row_budget R hcardR hR (p i) (hp i) (P i) (Q i))).trans_lt
      (sum_a8_double_coset_row_budget_lt_one p hp hinj)
  have htotal :
      ((∑ i, (mixedSylowPairBadConjugators (P i) (Q i)).ncard : ℕ) : ℝ) /
        Nat.card (alternatingGroup (Fin 8)) < 1 := by
    simpa only [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul] using hsum
  have hpos : (0 : ℝ) < Nat.card (alternatingGroup (Fin 8)) := by
    exact_mod_cast (Nat.card_pos (α := alternatingGroup (Fin 8)))
  have hlt := (div_lt_one hpos).mp htotal
  exact_mod_cast hlt

/-- Original Lisi--Sabatini conclusion in degree eight, reduced to the one
explicit Sylow-two witness. -/
theorem hasLisiSabatini_A8_of_one_pair
    (R : Sylow 2 (alternatingGroup (Fin 8)))
    (hcardR : Nat.card R = 64) (hR : ∃ g, sylowInter R g = ⊥) :
    HasLisiSabatini (alternatingGroup (Fin 8)) := by
  intro I _ p hp hinj P
  obtain ⟨x, hx⟩ := exists_common_mixedSylowInter_bot_A8_of_one_pair R hcardR hR
    p hp hinj P P
  refine ⟨x, fun i ↦ ?_⟩
  have hbot : sylowInter (P i) x = ⊥ := by
    simpa only [mixedSylowInter, sylowInter] using hx i
  intro y _hy
  rw [hbot]
  exact bot_le

end LisiSabatini
