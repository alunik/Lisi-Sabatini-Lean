module

public import LisiSabatini.Basic
public import Mathlib.GroupTheory.Index

/-!
# The cardinality step for index-two minimal intersections

A subgroup meeting an index-two subgroup trivially has order at most two.
The argument uses relative indices and does not require normality. This
provides the cardinality input for the separate minimal-intersection lemma.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

variable {G : Type*} [Group G] [Finite G]

/-- A subgroup disjoint from a subgroup of finite index has order bounded
by that index. -/
theorem subgroup_card_le_index_of_inf_eq_bot (K H : Subgroup G)
    (hdisjoint : K ⊓ H = ⊥) : Nat.card K ≤ H.index := by
  have hindex : H.relIndex (⊤ : Subgroup G) ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact H.index_ne_zero_of_finite
  have hle : H.relIndex K ≤ H.relIndex (⊤ : Subgroup G) :=
    Subgroup.relIndex_le_of_le_right (H := H) (L := ⊤) le_top hindex
  have hmeet : H ⊓ K = ⊥ := by rwa [inf_comm]
  rw [← Subgroup.inf_relIndex_right H K, hmeet,
    Subgroup.relIndex_bot_left, Subgroup.relIndex_top_right] at hle
  exact hle

/-- No normality assumption is needed for the index-two cardinality bound. -/
theorem subgroup_card_le_two_of_inf_eq_bot (K H : Subgroup G)
    (hindex : H.index ≤ 2) (hdisjoint : K ⊓ H = ⊥) : Nat.card K ≤ 2 :=
  (subgroup_card_le_index_of_inf_eq_bot K H hdisjoint).trans hindex

/-- The index-two argument applied to a prescribed Sylow self-intersection. -/
theorem sylowInter_card_le_two_of_inf_eq_bot (H : Subgroup G)
    (hindex : H.index ≤ 2) {p : ℕ} (P : Sylow p G) (x : G)
    (hdisjoint : sylowInter P x ⊓ H = ⊥) : Nat.card (sylowInter P x) ≤ 2 :=
  subgroup_card_le_two_of_inf_eq_bot (sylowInter P x) H hindex hdisjoint

end LisiSabatini
