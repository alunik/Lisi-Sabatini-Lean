module

public import LisiSabatini.SylowPairQuadraticAssembly
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Counting cyclic prime-order witnesses

Each nontrivial intersection of two Sylow `p`-subgroups contains all `p - 1`
nonidentity elements of a cyclic subgroup of order `p`.  Double counting
prime-order witnesses therefore improves the elementwise quadratic bound
by a factor of `p - 1`.  This argument applies to arbitrary finite groups
and independently prescribed Sylow rows.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini

universe uG uI

local instance cyclicQuadraticDecidableProp (P : Prop) : Decidable P :=
  Classical.propDecidable P

local instance cyclicQuadraticDecidableRel (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

variable {G : Type uG} [Group G]

/-- A bad Sylow-pair conjugator has at least `p - 1` prime-order witnesses. -/
theorem pred_prime_le_card_mixedSylowPair_primeOrder_witnesses
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q : Sylow p G) (x : G)
    (hx : x ∈ mixedSylowPairBadConjugators P Q) :
    p - 1 ≤ ((primeOrderElements p G).filter
      (fun g ↦ x ∈ mixedSylowPairPrimeWitnessConjugators P Q g)).card := by
  classical
  obtain ⟨g, hgOrder, hgP, hgQ⟩ :=
    (mixedSylowInter_ne_bot_iff_exists_primeOrder_mem P Q x).mp hx
  have hgPow : g ^ p = 1 := hgOrder ▸ pow_orderOf_eq_one g
  have hInj : (Set.Iio p).InjOn (g ^ ·) := by
    simpa only [hgOrder] using (pow_injOn_Iio_orderOf (x := g))
  have hpowOrder (n : ℕ) (hn : n ∈ Finset.Ico 1 p) : orderOf (g ^ n) = p := by
    obtain ⟨hnPos, hnLt⟩ := Finset.mem_Ico.mp hn
    apply orderOf_eq_prime
    · rw [pow_right_comm, hgPow, one_pow]
    · intro hnOne
      have hnZero : n = 0 :=
        hInj hnLt (Fact.out : p.Prime).pos (by simpa using hnOne)
      omega
  have hcard := Finset.card_le_card_of_injOn (g ^ ·)
    (s := Finset.Ico 1 p)
    (t := (primeOrderElements p G).filter
      (fun h ↦ x ∈ mixedSylowPairPrimeWitnessConjugators P Q h))
    (by
      intro n hn
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact (mem_primeOrderElements_iff _).mpr (hpowOrder n hn)
      · exact ⟨(P : Subgroup G).pow_mem hgP n,
          (((x • Q : Sylow p G) : Subgroup G)).pow_mem hgQ n⟩)
    (fun n hn m hm hnm ↦
      hInj (Finset.mem_Ico.mp hn).2 (Finset.mem_Ico.mp hm).2 hnm)
  simpa only [Nat.card_Ico] using hcard

/-- Double counting improves the transporter bound by the number of
nonidentity generators of a prime-order subgroup. -/
theorem pred_prime_mul_bad_ncard_le_transporter_sum
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q : Sylow p G) :
    (p - 1) * (mixedSylowPairBadConjugators P Q).ncard ≤
      ∑ g ∈ primeOrderElements p G,
        (if g ∈ (P : Subgroup G) then
          (sylowConjugatorMembershipSet Q g).ncard else 0) := by
  classical
  let B := (mixedSylowPairBadConjugators P Q).toFinset
  let T := primeOrderElements p G
  let R : G → G → Prop := fun x g ↦
    x ∈ mixedSylowPairPrimeWitnessConjugators P Q g
  have hlower : B.card * (p - 1) ≤
      ∑ x ∈ B, (T.bipartiteAbove R x).card := by
    simpa only [nsmul_eq_mul, Nat.cast_id] using
      B.card_nsmul_le_sum
        (fun x ↦ (T.bipartiteAbove R x).card) (p - 1)
        (fun x hx ↦ pred_prime_le_card_mixedSylowPair_primeOrder_witnesses
          P Q x (Set.mem_toFinset.mp hx))
  have hfiber (g : G) (hg : g ∈ T) :
      (B.bipartiteBelow R g).card =
        (mixedSylowPairPrimeWitnessConjugators P Q g).ncard := by
    have heq : B.bipartiteBelow R g =
        (mixedSylowPairPrimeWitnessConjugators P Q g).toFinset := by
      ext x
      simp only [Finset.mem_bipartiteBelow, B, Set.mem_toFinset, R]
      constructor
      · exact And.right
      · intro hx
        exact ⟨(mem_mixedSylowPairBadConjugators_iff_exists_primeOrder_witness
          P Q x).mpr ⟨g, (mem_primeOrderElements_iff g).mp hg, hx⟩, hx⟩
    rw [heq, Set.ncard_eq_toFinset_card']
  calc
    (p - 1) * (mixedSylowPairBadConjugators P Q).ncard =
        B.card * (p - 1) := by
          dsimp [B]
          rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
          exact Nat.mul_comm _ _
    _ ≤ ∑ x ∈ B, (T.bipartiteAbove R x).card := hlower
    _ = ∑ g ∈ T, (B.bipartiteBelow R g).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ = ∑ g ∈ primeOrderElements p G,
          (if g ∈ (P : Subgroup G) then
            (sylowConjugatorMembershipSet Q g).ncard else 0) := by
      apply Finset.sum_congr rfl
      intro g hg
      rw [hfiber g hg, ncard_mixedSylowPairPrimeWitnessConjugators]

/-- The cyclic-subgroup refinement of the exact quadratic class bound. -/
theorem pred_prime_mul_bad_ncard_le_quadraticClass_sum
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q : Sylow p G) :
    (p - 1) * (mixedSylowPairBadConjugators P Q).ncard ≤
      ∑ C : ConjClasses G, mixedSylowPairQuadraticClassTerm P Q C := by
  rw [← mixedSylowPair_transporter_sum_eq_quadraticClass_sum P Q]
  exact pred_prime_mul_bad_ncard_le_transporter_sum P Q

/-- The probability of failure for any prescribed Sylow pair is bounded
by the same-row quadratic cost divided by `p - 1`. -/
theorem bad_probability_le_cyclic_quadratic_cost
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q : Sylow p G) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) / (Nat.card G : ℝ) ≤
      normalizedSameRowSylowQuadraticCost G P / ((p - 1 : ℕ) : ℝ) := by
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hd : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hdNat
  have hc : (0 : ℝ) < (Nat.card G : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G)
  have hsame :
      (∑ C : ConjClasses G, mixedSylowPairQuadraticClassTerm P Q C) =
        ∑ C : ConjClasses G, mixedSylowPairQuadraticClassTerm P P C := by
    apply Finset.sum_congr rfl
    intro C _hC
    exact mixedSylowPairQuadraticClassTerm_eq_sameRow P Q P C
  have h := pred_prime_mul_bad_ncard_le_quadraticClass_sum P Q
  rw [hsame] at h
  have hcast :
      ((p - 1 : ℕ) : ℝ) * (mixedSylowPairBadConjugators P Q).ncard ≤
        ((∑ C : ConjClasses G,
          mixedSylowPairQuadraticClassTerm P P C : ℕ) : ℝ) := by
    exact_mod_cast h
  apply (le_div_iff₀ hd).2
  calc
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) / (Nat.card G : ℝ) *
        ((p - 1 : ℕ) : ℝ) =
        (((p - 1 : ℕ) : ℝ) * (mixedSylowPairBadConjugators P Q).ncard) /
          (Nat.card G : ℝ) := by ring
    _ ≤ normalizedSameRowSylowQuadraticCost G P :=
      div_le_div_of_nonneg_right hcast hc.le

/-- A strict sum of cyclic-witness costs supplies one conjugator for all
prescribed pairs. The labels need not be distinct for this counting result. -/
theorem exists_common_mixedSylowInter_bot_of_cyclic_cost_sum_lt_one
    [Fintype G] {I : Type uI} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (P Q : ∀ i, Sylow (p i) G)
    (hcost : (∑ i, normalizedSameRowSylowQuadraticCost G (P i) /
      ((p i - 1 : ℕ) : ℝ)) < 1) :
    ∃ x : G, ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  apply exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt p P Q
  have hc : (0 : ℝ) < (Nat.card G : ℝ) := by
    exact_mod_cast (Nat.card_pos : 0 < Nat.card G)
  have hratio :
      ((∑ i, (mixedSylowPairBadConjugators (P i) (Q i)).ncard : ℕ) : ℝ) /
        (Nat.card G : ℝ) < 1 := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine (Finset.sum_le_sum fun i _hi ↦ ?_).trans_lt hcost
    let : Fact (p i).Prime := ⟨hp i⟩
    exact bad_probability_le_cyclic_quadratic_cost (P i) (Q i)
  have hcast := (div_lt_one hc).1 hratio
  exact_mod_cast hcast

/-- Same-row form of the cyclic-witness budget criterion. -/
theorem exists_common_sylowInter_bot_of_cyclic_cost_sum_lt_one
    [Fintype G] {I : Type uI} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (P : ∀ i, Sylow (p i) G)
    (hcost : (∑ i, normalizedSameRowSylowQuadraticCost G (P i) /
      ((p i - 1 : ℕ) : ℝ)) < 1) :
    ∃ x : G, ∀ i, sylowInter (P i) x = ⊥ := by
  obtain ⟨x, hx⟩ := exists_common_mixedSylowInter_bot_of_cyclic_cost_sum_lt_one
    p hp P P hcost
  exact ⟨x, fun i ↦ by simpa only [mixedSylowInter, sylowInter] using hx i⟩

/-- Uniform cyclic-witness cost budgets imply the Lisi--Sabatini property. -/
theorem hasLisiSabatini_of_cyclic_cost_budget
    [Fintype G]
    (hbudget :
      ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
        (∀ i, Nat.Prime (p i)) → Function.Injective p →
        ∀ P : ∀ i, Sylow (p i) G,
          (∑ i, normalizedSameRowSylowQuadraticCost G (P i) /
            ((p i - 1 : ℕ) : ℝ)) < 1) :
    HasLisiSabatini.{uG, uI} G := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ := exists_common_sylowInter_bot_of_cyclic_cost_sum_lt_one
    p hp P (hbudget p hp hinjective P)
  refine ⟨x, fun i y _hy ↦ ?_⟩
  rw [hx i]
  exact bot_le

end LisiSabatini
