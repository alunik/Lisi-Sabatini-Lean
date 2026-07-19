import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group

/-!
# Elementary commutator identities in class-two groups

These four identities are the only part of the extraspecial-group structure
file used by the odd-order proof.
-/

namespace LisiSabatini

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left (a b c : G) :
    ⁅a * b, c⁆ = a * ⁅b, c⁆ * a⁻¹ * ⁅a, c⁆ := by
  simp only [commutatorElement_def, mul_inv_rev]
  group

theorem commutatorElement_mul_left_of_mem_center (a b c : G)
    (hbc : ⁅b, c⁆ ∈ Subgroup.center G) :
    ⁅a * b, c⁆ = ⁅b, c⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_left]
  have hcomm : a * ⁅b, c⁆ = ⁅b, c⁆ * a :=
    Subgroup.mem_center_iff.mp hbc a
  rw [hcomm]
  group

theorem commutatorElement_mul_right (a b c : G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * b * ⁅a, c⁆ * b⁻¹ := by
  simp only [commutatorElement_def, mul_inv_rev]
  group

theorem commutatorElement_mul_right_of_mem_center (a b c : G)
    (hac : ⁅a, c⁆ ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ * ⁅a, c⁆ := by
  rw [commutatorElement_mul_right]
  have hcomm : b * ⁅a, c⁆ = ⁅a, c⁆ * b :=
    Subgroup.mem_center_iff.mp hac b
  rw [mul_assoc ⁅a, b⁆ b ⁅a, c⁆]
  rw [hcomm]
  group

theorem commutatorElement_pow_left_of_mem_center (x y : G)
    (hxy : ⁅x, y⁆ ∈ Subgroup.center G) :
    ∀ n : ℕ, ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, commutatorElement_mul_left_of_mem_center _ _ _ hxy,
        ih, pow_succ']

theorem pow_mem_center_of_commutator_le_center
    (hclass : commutator G ≤ Subgroup.center G) (p : ℕ)
    (hpow : ∀ c : commutator G, (c : G) ^ p = 1) (x : G) :
    x ^ p ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro y
  rw [eq_comm, ← commutatorElement_eq_one_iff_mul_comm,
    commutatorElement_pow_left_of_mem_center x y]
  · exact hpow ⟨⁅x, y⁆,
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x)
        (Subgroup.mem_top y)⟩
  · exact hclass (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y))

end LisiSabatini
