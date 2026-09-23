module

public import LisiSabatini.FiniteCertificates.ConjugacySampling
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Family soundness for the small symmetric certificates

Exact counts for one Sylow subgroup at each of the primes 2, 3 and 5
give a common conjugator for every prescribed self-row family. Primes
outside the group order contribute no bad conjugators. The argument is
generic in the finite group and does not enumerate Sylow families.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini.SymmetricFiniteCertificates

open FiniteCertificates

variable {G : Type*} [Group G]

/-- A Sylow subgroup at a prime outside the group order is trivial. -/
theorem sylow_eq_bot_of_not_dvd_card {p : ℕ} (hp : p.Prime)
    (hnot : ¬ p ∣ Nat.card G) (P : Sylow p G) :
    (P : Subgroup G) = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  apply Subgroup.card_eq_one.mp
  rcases P.isPGroup'.card_eq_or_dvd with h | h
  · exact h
  · exact (hnot (h.trans (Subgroup.card_subgroup_dvd_card (P : Subgroup G)))).elim

/-- The finite sample has no bad elements for a trivial Sylow subgroup. -/
theorem sampleBadConjugators_eq_empty_of_eq_bot
    (C : Finset G) {p : ℕ} (P : Sylow p G)
    (hP : (P : Subgroup G) = ⊥) :
    sampleBadConjugators C P = ∅ := by
  classical
  ext g
  simp [sampleBadConjugators, sylowInter, hP]

private theorem sampleBadConjugators_card_cast
    (C : Finset G) {p q : ℕ} (h : p = q) (P : Sylow p G) :
    (sampleBadConjugators C P).card =
      (sampleBadConjugators C (h ▸ P)).card := by
  subst q
  rfl

private def prime235Bound (b2 b3 b5 p : ℕ) : ℕ :=
  if p = 2 then b2 else if p = 3 then b3 else if p = 5 then b5 else 0

private theorem sum_prime235Bound_le
    {I : Type*} [Fintype I] (p : I → ℕ) (hinj : Function.Injective p)
    (b2 b3 b5 : ℕ) :
    (∑ i, prime235Bound b2 b3 b5 (p i)) ≤ b2 + b3 + b5 := by
  classical
  let S : Finset ℕ := {2, 3, 5}
  let T := Finset.univ.filter (fun i ↦ p i ∈ S)
  have hcut :
      (∑ i ∈ T, prime235Bound b2 b3 b5 (p i)) =
        ∑ i, prime235Bound b2 b3 b5 (p i) := by
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
    simp [prime235Bound, h2, h3, h5]
  calc
    (∑ i, prime235Bound b2 b3 b5 (p i)) =
        ∑ i ∈ T, prime235Bound b2 b3 b5 (p i) := hcut.symm
    _ ≤ ∑ q ∈ S, prime235Bound b2 b3 b5 q := by
      apply Finset.sum_le_sum_of_injOn p hinj.injOn
      · intro q hq
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
        exact (Finset.mem_filter.mp hi).2
      · intro i hi
        exact le_rfl
      · intro q hq hnot
        exact Nat.zero_le _
    _ = b2 + b3 + b5 := by simp [S, prime235Bound, Nat.add_assoc]

variable [Fintype G]

/-- Canonical bad counts at 2, 3 and 5 imply trivial intersections for
every finite injectively prime-labelled Sylow self-row family. -/
theorem exists_common_sylowInter_bot_of_235_bad_bounds
    (P2 : Sylow 2 G) (P3 : Sylow 3 G) (P5 : Sylow 5 G)
    (b2 b3 b5 : ℕ)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G →
      p = 2 ∨ p = 3 ∨ p = 5)
    (h2 : (sampleBadConjugators Finset.univ P2).card ≤ b2)
    (h3 : (sampleBadConjugators Finset.univ P3).card ≤ b3)
    (h5 : (sampleBadConjugators Finset.univ P5).card ≤ b5)
    (hsum : b2 + b3 + b5 < Fintype.card G)
    {I : Type*} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P : ∀ i, Sylow (p i) G) :
    ∃ g : G, ∀ i, sylowInter (P i) g = ⊥ := by
  classical
  let := Fintype.ofFinite I
  have hC : ConjugacyInvariantSample (Finset.univ : Finset G) := by
    intro a g hg
    exact Finset.mem_univ _
  have hbad : ∀ i,
      (sampleBadConjugators Finset.univ (P i)).card ≤
        prime235Bound b2 b3 b5 (p i) := by
    intro i
    by_cases hpi2 : p i = 2
    · let Pi : Sylow 2 G := hpi2 ▸ P i
      have hcount := sampleBadConjugators_card_eq
        Finset.univ hC (by decide : Nat.Prime 2) Pi P2
      have hsame : (sampleBadConjugators Finset.univ (P i)).card =
          (sampleBadConjugators Finset.univ Pi).card :=
        sampleBadConjugators_card_cast Finset.univ hpi2 (P i)
      simpa [prime235Bound, hpi2, hsame, hcount] using h2
    by_cases hpi3 : p i = 3
    · let Pi : Sylow 3 G := hpi3 ▸ P i
      have hcount := sampleBadConjugators_card_eq
        Finset.univ hC (by decide : Nat.Prime 3) Pi P3
      have hsame : (sampleBadConjugators Finset.univ (P i)).card =
          (sampleBadConjugators Finset.univ Pi).card :=
        sampleBadConjugators_card_cast Finset.univ hpi3 (P i)
      simpa [prime235Bound, hpi2, hpi3, hsame, hcount] using h3
    by_cases hpi5 : p i = 5
    · let Pi : Sylow 5 G := hpi5 ▸ P i
      have hcount := sampleBadConjugators_card_eq
        Finset.univ hC (by decide : Nat.Prime 5) Pi P5
      have hsame : (sampleBadConjugators Finset.univ (P i)).card =
          (sampleBadConjugators Finset.univ Pi).card :=
        sampleBadConjugators_card_cast Finset.univ hpi5 (P i)
      simpa [prime235Bound, hpi2, hpi3, hpi5, hsame, hcount] using h5
    have hnot : ¬ p i ∣ Nat.card G := by
      intro hdiv
      rcases hprimes (p i) (hp i) hdiv with h | h | h
      · exact hpi2 h
      · exact hpi3 h
      · exact hpi5 h
    rw [sampleBadConjugators_eq_empty_of_eq_bot Finset.univ (P i)
      (sylow_eq_bot_of_not_dvd_card (hp i) hnot (P i))]
    exact Nat.zero_le _
  have htotal : ∑ i, (sampleBadConjugators Finset.univ (P i)).card <
      (Finset.univ : Finset G).card := by
    apply lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ hbad i)
    exact (sum_prime235Bound_le p hinj b2 b3 b5).trans_lt
      (by simpa using hsum)
  obtain ⟨g, hg, hgood⟩ :=
    exists_common_sylowInter_bot_in_sample_of_bad_sum_lt Finset.univ p P htotal
  exact ⟨g, hgood⟩

/-- The family soundness theorem in the paper's inclusion-minimal form. -/
theorem hasLisiSabatini_of_235_bad_bounds
    (P2 : Sylow 2 G) (P3 : Sylow 3 G) (P5 : Sylow 5 G)
    (b2 b3 b5 : ℕ)
    (hprimes : ∀ p : ℕ, p.Prime → p ∣ Nat.card G →
      p = 2 ∨ p = 3 ∨ p = 5)
    (h2 : (sampleBadConjugators Finset.univ P2).card ≤ b2)
    (h3 : (sampleBadConjugators Finset.univ P3).card ≤ b3)
    (h5 : (sampleBadConjugators Finset.univ P5).card ≤ b5)
    (hsum : b2 + b3 + b5 < Fintype.card G) :
    HasLisiSabatini G := by
  intro I _ p hp hinj P
  obtain ⟨g, hg⟩ := exists_common_sylowInter_bot_of_235_bad_bounds
    P2 P3 P5 b2 b3 b5 hprimes h2 h3 h5 hsum p hp hinj P
  refine ⟨g, fun i y hy ↦ ?_⟩
  rw [hg i]
  exact bot_le

end LisiSabatini.SymmetricFiniteCertificates
