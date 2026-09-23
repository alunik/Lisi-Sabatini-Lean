module

public import LisiSabatini.FiniteCertificates.ConjugacySampling
public import LisiSabatini.SylowDoubleCosetBound
public import LisiSabatini.SymmetricFiniteCertificates.Family

/-!
# Transport of finite self-row counts to arbitrary mixed rows

Over the full group, independently conjugating the two Sylow rows preserves
the bad-conjugator count. The change of variable is left and right
multiplication, so no conjugacy-invariant proper sample is assumed here.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini.SymmetricFiniteCertificates

open FiniteCertificates
open scoped BigOperators

variable {G : Type*} [Group G]

/-- Full-group self-row sampling is the same finite set as the mixed bad
locus with the same subgroup in both slots. -/
theorem sampleBadConjugators_univ_card_eq_mixed_ncard [Fintype G]
    {p : ℕ} (P : Sylow p G) :
    (sampleBadConjugators Finset.univ P).card =
      (mixedSylowPairBadConjugators P P).ncard := by
  classical
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  change x ∈ sampleBadConjugators Finset.univ P ↔ mixedSylowInter P P x ≠ ⊥
  rw [mem_sampleBadConjugators_iff]
  simp only [Finset.mem_univ, true_and]
  rfl

/-- Independent row conjugation preserves triviality after the corresponding
left/right change of conjugator. -/
theorem mixedSylowInter_conjugate_rows_eq_bot_iff
    {p : ℕ} (P Q : Sylow p G) (a b x : G) :
    mixedSylowInter (a • P) (b • Q) (a * x * b⁻¹) = ⊥ ↔
      mixedSylowInter P Q x = ⊥ := by
  constructor
  · intro h
    have hback := mixedSylowInter_conjugate_rows_eq_bot (a • P) (b • Q) h a⁻¹ b⁻¹
    simpa only [inv_smul_smul, inv_inv, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel, mul_one] using hback
  · intro h
    exact mixedSylowInter_conjugate_rows_eq_bot P Q h a b

/-- Left/right multiplication gives an exact cardinality-preserving
transport of the full bad-conjugator locus. -/
theorem mixedSylowPairBadConjugators_ncard_conjugate_rows
    {p : ℕ} (P Q : Sylow p G) (a b : G) :
    (mixedSylowPairBadConjugators (a • P) (b • Q)).ncard =
      (mixedSylowPairBadConjugators P Q).ncard := by
  symm
  apply Set.ncard_congr (fun x _ ↦ a * x * b⁻¹)
  · intro x hx
    exact (not_congr (mixedSylowInter_conjugate_rows_eq_bot_iff P Q a b x)).mpr hx
  · intro x y hx hy hxy
    exact mul_left_cancel (mul_right_cancel hxy)
  · intro y hy
    let x := a⁻¹ * y * b
    have hxy : a * x * b⁻¹ = y := by
      dsimp [x]
      group
    have hx : x ∈ mixedSylowPairBadConjugators P Q := by
      apply (not_congr (mixedSylowInter_conjugate_rows_eq_bot_iff P Q a b x)).mp
      rwa [hxy]
    exact ⟨x, hx, hxy⟩

/-- Every mixed pair at a given prime has the same full-group bad count as
any chosen canonical self-row. -/
theorem mixedSylowPairBadConjugators_ncard_eq_self [Finite G]
    {p : ℕ} (hp : p.Prime) (P Q R : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard =
      (mixedSylowPairBadConjugators R R).ncard := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G R P
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G R Q
  exact mixedSylowPairBadConjugators_ncard_conjugate_rows R R a b

/-- A certified full-group self-row upper bound applies to any two prescribed
Sylow rows at the same prime. -/
theorem mixedSylowPairBadConjugators_ncard_le_of_sample_bound [Fintype G]
    {p b : ℕ} (hp : p.Prime) (R : Sylow p G)
    (hR : (sampleBadConjugators Finset.univ R).card ≤ b) (P Q : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard ≤ b := by
  rw [mixedSylowPairBadConjugators_ncard_eq_self hp P Q R,
    ← sampleBadConjugators_univ_card_eq_mixed_ncard]
  exact hR

private def mixed235Bound (b2 b3 b5 p : ℕ) : ℕ :=
  if p = 2 then b2 else if p = 3 then b3 else if p = 5 then b5 else 0

private theorem sum_mixed235Bound_le
    {I : Type*} [Fintype I] (p : I → ℕ) (hinj : Function.Injective p)
    (b2 b3 b5 : ℕ) :
    (∑ i, mixed235Bound b2 b3 b5 (p i)) ≤ b2 + b3 + b5 := by
  classical
  let S : Finset ℕ := {2, 3, 5}
  let T := Finset.univ.filter (fun i ↦ p i ∈ S)
  have hcut :
      (∑ i ∈ T, mixed235Bound b2 b3 b5 (p i)) =
        ∑ i, mixed235Bound b2 b3 b5 (p i) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i hi hnot
    have hout : p i ∉ S := by
      intro hmem
      exact hnot (Finset.mem_filter.mpr ⟨hi, hmem⟩)
    have h2 : p i ≠ 2 := by
      intro h
      apply hout
      simp [S, h]
    have h3 : p i ≠ 3 := by
      intro h
      apply hout
      simp [S, h]
    have h5 : p i ≠ 5 := by
      intro h
      apply hout
      simp [S, h]
    simp [mixed235Bound, h2, h3, h5]
  calc
    (∑ i, mixed235Bound b2 b3 b5 (p i)) =
        ∑ i ∈ T, mixed235Bound b2 b3 b5 (p i) := hcut.symm
    _ ≤ ∑ q ∈ S, mixed235Bound b2 b3 b5 q := by
      apply Finset.sum_le_sum_of_injOn p hinj.injOn
      · intro q hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        exact (Finset.mem_filter.mp hi).2
      · intro i hi
        exact le_rfl
      · intro q hq hnot
        exact Nat.zero_le _
    _ = b2 + b3 + b5 := by simp [S, mixed235Bound, Nat.add_assoc]

private theorem mixed_bad_ncard_cast {p q : ℕ} (h : p = q) (P Q : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard =
      (mixedSylowPairBadConjugators (h ▸ P) (h ▸ Q)).ncard := by
  subst q
  rfl

/-- Uniform mixed bad-count bounds at the three possible prime divisors
give simultaneous trivial intersections for every prescribed finite family. -/
theorem exists_common_mixedSylowInter_bot_of_235_bad_bounds [Finite G]
    (b2 b3 b5 : ℕ)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G →
      p = 2 ∨ p = 3 ∨ p = 5)
    (h2 : ∀ P Q : Sylow 2 G, (mixedSylowPairBadConjugators P Q).ncard ≤ b2)
    (h3 : ∀ P Q : Sylow 3 G, (mixedSylowPairBadConjugators P Q).ncard ≤ b3)
    (h5 : ∀ P Q : Sylow 5 G, (mixedSylowPairBadConjugators P Q).ncard ≤ b5)
    (hsum : b2 + b3 + b5 < Nat.card G)
    {I : Type*} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) G) :
    ∃ g : G, ∀ i, mixedSylowInter (P i) (Q i) g = ⊥ := by
  classical
  let := Fintype.ofFinite I
  have hbad : ∀ i, (mixedSylowPairBadConjugators (P i) (Q i)).ncard ≤
      mixed235Bound b2 b3 b5 (p i) := by
    intro i
    by_cases hpi2 : p i = 2
    · rw [mixed235Bound, ite_eq_left hpi2, mixed_bad_ncard_cast hpi2]
      exact h2 _ _
    by_cases hpi3 : p i = 3
    · rw [mixed235Bound, ite_eq_right hpi2, ite_eq_left hpi3, mixed_bad_ncard_cast hpi3]
      exact h3 _ _
    by_cases hpi5 : p i = 5
    · rw [mixed235Bound, ite_eq_right hpi2, ite_eq_right hpi3, ite_eq_left hpi5,
        mixed_bad_ncard_cast hpi5]
      exact h5 _ _
    have hnot : ¬ p i ∣ Nat.card G := by
      intro hdiv
      rcases hprimes (p i) (hp i) hdiv with h | h | h
      · exact hpi2 h
      · exact hpi3 h
      · exact hpi5 h
    have hP : (P i : Subgroup G) = ⊥ :=
      sylow_eq_bot_of_not_dvd_card (hp i) hnot (P i)
    have hempty : mixedSylowPairBadConjugators (P i) (Q i) = ∅ := by
      ext x
      simp [mixedSylowPairBadConjugators, mixedSylowInter, hP]
    rw [hempty, Set.ncard_empty]
    exact Nat.zero_le _
  apply exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt p P Q
  exact (Finset.sum_le_sum fun i _ ↦ hbad i).trans_lt
    ((sum_mixed235Bound_le p hinj b2 b3 b5).trans_lt hsum)

/-- The mixed-count criterion specializes to the original Lisi–Sabatini
conclusion without additional hypotheses. -/
theorem hasLisiSabatini_of_mixed_235_bad_bounds [Finite G]
    (b2 b3 b5 : ℕ)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G →
      p = 2 ∨ p = 3 ∨ p = 5)
    (h2 : ∀ P Q : Sylow 2 G, (mixedSylowPairBadConjugators P Q).ncard ≤ b2)
    (h3 : ∀ P Q : Sylow 3 G, (mixedSylowPairBadConjugators P Q).ncard ≤ b3)
    (h5 : ∀ P Q : Sylow 5 G, (mixedSylowPairBadConjugators P Q).ncard ≤ b5)
    (hsum : b2 + b3 + b5 < Nat.card G) : HasLisiSabatini G := by
  intro I _ p hp hinj P
  obtain ⟨g, hg⟩ := exists_common_mixedSylowInter_bot_of_235_bad_bounds
    b2 b3 b5 hprimes h2 h3 h5 hsum p hp hinj P P
  refine ⟨g, fun i y hy ↦ ?_⟩
  change mixedSylowInter (P i) (P i) g ≤ _
  rw [hg i]
  exact bot_le

end LisiSabatini.SymmetricFiniteCertificates
