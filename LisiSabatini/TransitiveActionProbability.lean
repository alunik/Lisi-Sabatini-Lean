module

public import LisiSabatini.SylowPairQuadraticBound
public import Mathlib.Data.Real.Basic

/-!
# Uniform probabilities from a transitive finite action

The orbit map of a finite transitive group action has equally sized fibers.
Consequently, a uniformly chosen group element moves any prescribed point
into a set with probability equal to that set's proportion of the space.
-/

@[expose] public section

namespace LisiSabatini

/-- For a transitive action, each point of a set contributes one full
stabilizer fiber to the transporter count. -/
theorem ncard_smul_into_set_eq_ncard_mul_card_stabilizer
    {A X : Type*} [Group A] [MulAction A X]
    [Finite A] [Finite X] [MulAction.IsPretransitive A X]
    (b : X) (S : Set X) :
    {a : A | a • b ∈ S}.ncard =
      S.ncard * Nat.card (MulAction.stabilizer A b) := by
  simpa only [MulAction.orbit_eq_univ, Set.univ_inter] using
    ncard_smul_into_set_eq_inter_orbit_mul_card_stabilizer (A := A) b S

/-- A uniform group element sends a fixed point of a finite transitive
action into `S` with probability `|S| / |X|`. The point `b` supplies the
required nonemptiness of `X`. -/
theorem ncard_smul_into_set_div_card_eq
    {A X : Type*} [Group A] [MulAction A X]
    [Finite A] [Finite X] [MulAction.IsPretransitive A X]
    (b : X) (S : Set X) :
    ({a : A | a • b ∈ S}.ncard : ℝ) / Nat.card A =
      (S.ncard : ℝ) / Nat.card X := by
  have htotal : Nat.card A =
      Nat.card X * Nat.card (MulAction.stabilizer A b) := by
    simpa only [Set.mem_univ, Set.ofPred_true, Set.ncard_univ] using
      ncard_smul_into_set_eq_ncard_mul_card_stabilizer (A := A) b (Set.univ : Set X)
  have hstab : (Nat.card (MulAction.stabilizer A b) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := MulAction.stabilizer A b)).ne'
  rw [ncard_smul_into_set_eq_ncard_mul_card_stabilizer, htotal, Nat.cast_mul,
    Nat.cast_mul]
  exact mul_div_mul_right _ _ hstab

end LisiSabatini
