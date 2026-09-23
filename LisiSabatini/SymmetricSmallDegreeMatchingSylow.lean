module

public import LisiSabatini.SymmetricSmallDegreeMatching
public import Mathlib.GroupTheory.Sylow

/-!
# Sylow overgroups of matching flip subgroups

Every matching flip subgroup is a 2-group. For a perfect matching, its
transpositions are exactly the transpositions of any 2-subgroup containing it:
an additional transposition would meet a matching edge in one endpoint, and
their product would have order three.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open Equiv

variable {α : Type*}

/-- Independent flips of matching edges form a 2-group, even without a
finiteness assumption on the underlying set. -/
theorem isPGroup_matchingFlipSubgroup (τ : Perm α) (hτ : Function.Involutive τ) :
    IsPGroup 2 (matchingFlipSubgroup τ hτ) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  exact sq_eq_one_of_mem_matchingFlipSubgroup τ hτ g.property

/-- A matching flip subgroup is contained in an actual Sylow 2-subgroup. -/
theorem exists_sylow_two_ge_matchingFlipSubgroup
    (τ : Perm α) (hτ : Function.Involutive τ) :
    ∃ P : Sylow 2 (Perm α), matchingFlipSubgroup τ hτ ≤ P :=
  (isPGroup_matchingFlipSubgroup τ hτ).exists_le_sylow

/-- Distinct transpositions in a 2-subgroup cannot share exactly one endpoint. -/
theorem eq_of_swaps_mem_two_subgroup [Finite α] [DecidableEq α]
    (H : Subgroup (Perm α)) (hH : IsPGroup 2 H)
    {a b c : α} (hab : a ≠ b) (hac : a ≠ c)
    (habH : swap a b ∈ H) (hacH : swap a c ∈ H) : b = c := by
  classical
  let : Fintype α := Fintype.ofFinite α
  by_contra hbc
  let g : H := ⟨swap a b * swap a c, H.mul_mem habH hacH⟩
  have hg : orderOf g = 3 := by
    rw [Subgroup.orderOf_mk]
    exact (Perm.isThreeCycle_swap_mul_swap_same hab hac hbc).orderOf
  have hcop := hH.orderOf_coprime (show Nat.Coprime 2 3 by decide) g
  rw [hg] at hcop
  norm_num at hcop

/-- In a 2-subgroup containing a perfect matching's flips, a transposition
must exchange the endpoints of one of the matching's own edges. -/
theorem matching_partner_eq_of_swap_mem_two_subgroup [Finite α] [DecidableEq α]
    (τ : Perm α) (hτ : Function.Involutive τ) (hfixed : ∀ a, τ a ≠ a)
    (H : Subgroup (Perm α)) (hH : IsPGroup 2 H)
    (hmatching : matchingFlipSubgroup τ hτ ≤ H)
    {a b : α} (hab : a ≠ b) (hswap : swap a b ∈ H) : b = τ a :=
  eq_of_swaps_mem_two_subgroup H hH hab (hfixed a).symm hswap
    (hmatching (swap_mem_matchingFlipSubgroup τ hτ a))

/-- Passing from perfect-matching flips to a containing 2-subgroup adds no
transpositions. -/
theorem isSwap_mem_two_subgroup_iff_mem_matchingFlipSubgroup
    [Finite α] [DecidableEq α]
    (τ : Perm α) (hτ : Function.Involutive τ) (hfixed : ∀ a, τ a ≠ a)
    (H : Subgroup (Perm α)) (hH : IsPGroup 2 H)
    (hmatching : matchingFlipSubgroup τ hτ ≤ H)
    {s : Perm α} (hs : s.IsSwap) :
    s ∈ H ↔ s ∈ matchingFlipSubgroup τ hτ := by
  constructor
  · intro hsH
    obtain ⟨a, b, hab, rfl⟩ := hs
    have hb := matching_partner_eq_of_swap_mem_two_subgroup τ hτ hfixed
      H hH hmatching hab hsH
    rw [hb]
    exact swap_mem_matchingFlipSubgroup τ hτ a
  · intro hsm
    exact hmatching hsm

/-- Exact transposition membership in any Sylow 2-subgroup extending a
perfect matching's flip subgroup. -/
theorem isSwap_mem_sylow_two_iff_mem_matchingFlipSubgroup
    [Finite α] [DecidableEq α]
    (τ : Perm α) (hτ : Function.Involutive τ) (hfixed : ∀ a, τ a ≠ a)
    (P : Sylow 2 (Perm α)) (hmatching : matchingFlipSubgroup τ hτ ≤ P)
    {s : Perm α} (hs : s.IsSwap) :
    s ∈ P ↔ s ∈ matchingFlipSubgroup τ hτ :=
  isSwap_mem_two_subgroup_iff_mem_matchingFlipSubgroup τ hτ hfixed P P.isPGroup'
    hmatching hs

end LisiSabatini
