module

public import LisiSabatini.SylowPairQuadraticIndexTwo
public import Mathlib.Algebra.BigOperators.Field

/-!
# Assembling normalized quadratic Sylow-row budgets

The class-sum bound is naturally computed one prime row at a time and
normalized by the order of the group.  This file converts a strict
normalized real budget into the integral inequality required by
`exists_common_sylowInter_bot_of_quadraticClass_sum_lt`, then packages the
result as a criterion for the Lisi--Sabatini property.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uG uI

local instance quadraticAssemblyDecidableRel
    (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

/-- A strict normalized sum of same-row quadratic costs leaves a conjugator
outside every bad row.

The proof explicitly passes through the corresponding strict inequality in
`ℕ`; in particular, no rounding principle for real-valued probabilities is
being assumed. -/
theorem exists_common_sylowInter_bot_of_normalized_cost_sum_lt_one
    {G : Type uG} [Group G] [Fintype G]
    {I : Type uI} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (P : ∀ i, Sylow (p i) G)
    (hcost :
      (∑ i, normalizedSameRowSylowQuadraticCost G (P i)) < 1) :
    ∃ x : G, ∀ i, sylowInter (P i) x = ⊥ := by
  let rowTotal : I → ℕ := fun i ↦
    ∑ C : ConjClasses G,
      mixedSylowPairQuadraticClassTerm (P i) (P i) C
  have hcardPosNat : 0 < Nat.card G := Nat.card_pos
  have hcardPosReal : (0 : ℝ) < (Nat.card G : ℝ) := by
    exact_mod_cast hcardPosNat
  have hreal :
      ((∑ i, rowTotal i : ℕ) : ℝ) / (Nat.card G : ℝ) < 1 := by
    rw [Nat.cast_sum]
    simpa only [rowTotal, normalizedSameRowSylowQuadraticCost,
      Finset.sum_div] using hcost
  have hcast :
      ((∑ i, rowTotal i : ℕ) : ℝ) < (Nat.card G : ℝ) := by
    exact (div_lt_one hcardPosReal).mp hreal
  have hnat : (∑ i, rowTotal i) < Nat.card G := by
    exact_mod_cast hcast
  apply exists_common_sylowInter_bot_of_quadraticClass_sum_lt p hp P
  simpa only [rowTotal] using hnat

/-- Uniform normalized-budget criterion for the Lisi--Sabatini property.

It is enough to establish the strict cost bound for every finite,
injectively prime-labelled family of prescribed Sylow rows.  The resulting
trivial intersections are automatically inclusion-minimal. -/
theorem hasLisiSabatini_of_normalized_cost_budget
    {G : Type uG} [Group G] [Fintype G]
    (hbudget :
      ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
        (∀ i, Nat.Prime (p i)) →
        Function.Injective p →
        ∀ P : ∀ i, Sylow (p i) G,
          (∑ i, normalizedSameRowSylowQuadraticCost G (P i)) < 1) :
    HasLisiSabatini.{uG, uI} G := by
  intro I _ p hp hinjective P
  obtain ⟨x, hx⟩ :=
    exists_common_sylowInter_bot_of_normalized_cost_sum_lt_one
      p hp P (hbudget p hp hinjective P)
  refine ⟨x, fun i y _hy ↦ ?_⟩
  rw [hx i]
  exact bot_le

end LisiSabatini
