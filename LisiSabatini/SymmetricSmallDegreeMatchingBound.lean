module

public import LisiSabatini.SymmetricSmallDegreeMatching
public import LisiSabatini.SymmetricSmallDegreeSubgroupCost
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Matching-base compression of the binary Sylow bound

The generic incidence correction applies to any two matching flip
subgroups inside the prescribed binary Sylow rows. Its primitive witnesses
are precisely single transpositions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini

local instance matchingBoundDecidableProp (P : Prop) : Decidable P := Classical.propDecidable P
local instance matchingBoundDecidableRel (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _

/-- Relabeling a matching relabels its full flip subgroup. -/
theorem pointwise_conj_matchingFlipSubgroup
    {α : Type*} (τ : Equiv.Perm α) (hτ : Function.Involutive τ) (x : Equiv.Perm α) :
    MulAut.conj x • matchingFlipSubgroup τ hτ =
      matchingFlipSubgroup (x * τ * x⁻¹) (involutive_conj_matching τ hτ x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (MulAut.conj x).symm g ∈ matchingFlipSubgroup τ hτ ↔ _
  have h := conj_mem_matchingFlipSubgroup_iff τ hτ x ((MulAut.conj x).symm g)
  change MulAut.conj x ((MulAut.conj x).symm g) ∈ _ ↔ _ at h
  rw [(MulAut.conj x).apply_symm_apply] at h
  exact h.symm

/-- Any prime-order incidence between two matching bases can be replaced
by a single-transposition incidence between the same bases. -/
theorem exists_swap_of_matching_primeWitness
    {α : Type*} [Finite α] [DecidableEq α]
    (τ υ : Equiv.Perm α) (hτ : Function.Involutive τ) (hυ : Function.Involutive υ)
    (x g : Equiv.Perm α) (hgOrder : orderOf g = 2)
    (hgτ : g ∈ matchingFlipSubgroup τ hτ)
    (hgυ : g ∈ MulAut.conj x • matchingFlipSubgroup υ hυ) :
    ∃ s : Equiv.Perm α, orderOf s = 2 ∧ s ∈ matchingFlipSubgroup τ hτ ∧
      s ∈ MulAut.conj x • matchingFlipSubgroup υ hυ ∧ s.IsSwap := by
  let : Fintype α := Fintype.ofFinite α
  rw [pointwise_conj_matchingFlipSubgroup] at hgυ ⊢
  have hne : matchingFlipSubgroup τ hτ ⊓
      matchingFlipSubgroup (x * υ * x⁻¹) (involutive_conj_matching υ hυ x) ≠ ⊥ := by
    intro hbot
    have hg1 : g = 1 := Subgroup.mem_bot.mp (hbot ▸ (show g ∈
      matchingFlipSubgroup τ hτ ⊓ matchingFlipSubgroup (x * υ * x⁻¹)
        (involutive_conj_matching υ hυ x) from ⟨hgτ, hgυ⟩))
    simp only [hg1, orderOf_one] at hgOrder
    norm_num at hgOrder
  obtain ⟨s, hs, hsτ, hsυ⟩ :=
    (matchingFlipSubgroup_inf_ne_bot_iff_exists_isSwap τ (x * υ * x⁻¹)
      hτ (involutive_conj_matching υ hυ x)).mp hne
  exact ⟨s, hs.orderOf, hsτ, hsυ, hs⟩

/-- Actual binary Sylow bad-set bound with all common matching flips
compressed to common transpositions. -/
theorem bad_ncard_add_matching_le_quadratic_add_swaps
    {α : Type*} [Fintype α] [DecidableEq α]
    (P Q : Sylow 2 (Equiv.Perm α))
    (τ υ : Equiv.Perm α) (hτ : Function.Involutive τ) (hυ : Function.Involutive υ)
    (hP : matchingFlipSubgroup τ hτ ≤ (P : Subgroup (Equiv.Perm α)))
    (hQ : matchingFlipSubgroup υ hυ ≤ (Q : Subgroup (Equiv.Perm α))) :
    (mixedSylowPairBadConjugators P Q).ncard +
        ∑ C : ConjClasses (Equiv.Perm α), subgroupPrimeIncidenceClassTerm 2
          (matchingFlipSubgroup τ hτ) (matchingFlipSubgroup υ hυ) (fun _ ↦ True) C ≤
      (∑ C : ConjClasses (Equiv.Perm α), mixedSylowPairQuadraticClassTerm P Q C) +
        ∑ C : ConjClasses (Equiv.Perm α), subgroupPrimeIncidenceClassTerm 2
          (matchingFlipSubgroup τ hτ) (matchingFlipSubgroup υ hυ) Equiv.Perm.IsSwap C := by
  have h := bad_ncard_add_structured_le_quadratic_add_primitive P Q
    (matchingFlipSubgroup τ hτ) (matchingFlipSubgroup υ hυ) hP hQ
    Equiv.Perm.IsSwap (exists_swap_of_matching_primeWitness τ υ hτ hυ)
  rwa [sum_subgroupPrimeWitness_eq_quadraticClass_sum_all,
    sum_subgroupPrimeWitness_eq_quadraticClass_sum] at h

end LisiSabatini
