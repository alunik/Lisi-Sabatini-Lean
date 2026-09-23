module

public import LisiSabatini.SymmetricSmallDegreeWitnessCompression

/-!
# Exact subgroup incidence costs

The transporter and conjugacy-class identities are valid for arbitrary
subgroups. This version permits a predicate on the source witnesses, so it
can count either all matching flips or only the primitive transpositions.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini

universe uG

local instance subgroupCostDecidableProp (P : Prop) : Decidable P := Classical.propDecidable P
local instance subgroupCostDecidableRel (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _
local instance subgroupCostFiniteConjAct (G : Type*) [Group G] [Finite G] :
    Finite (ConjAct G) := Finite.of_equiv G ConjAct.toConjAct.toEquiv

variable {G : Type uG} [Group G]

/-- Exact transporter count for an arbitrary subgroup. -/
theorem ncard_subgroup_conjugator_membership
    [Finite G] (B : Subgroup G) (g : G) :
    {x : G | g ∈ MulAut.conj x • B}.ncard =
      Nat.card (Subgroup.centralizer {g}) * (conjugacyClassInter B g).ncard := by
  have hmem (x : G) :
      g ∈ MulAut.conj x • B ↔ invToConjActEquiv G x • g ∈ B := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    change (MulAut.conj x)⁻¹ g ∈ B ↔ invToConjActEquiv G x • g ∈ B
    rw [← map_inv]
    change MulAut.conj x⁻¹ g ∈ B ↔ (ConjAct.toConjAct x⁻¹ : ConjAct G) • g ∈ B
    rw [ConjAct.toConjAct_smul_eq_mulAut_conj]
  have heq : {x : G | g ∈ MulAut.conj x • B}.ncard =
      {a : ConjAct G | a • g ∈ B}.ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr ((invToConjActEquiv G).subtypeEquiv hmem)
  rw [heq]
  change {a : ConjAct G | a • g ∈ (B : Set G)}.ncard = _
  rw [ncard_smul_into_set_eq_inter_orbit_mul_card_stabilizer]
  rw [← card_centralizer_eq_card_conjAct_stabilizer]
  exact Nat.mul_comm _ _

/-- Prime-order incidence count with the source element fixed. -/
theorem ncard_subgroupPrimeWitnessConjugators
    [Finite G] (p : ℕ) (A B : Subgroup G) (g : G) :
    (subgroupPrimeWitnessConjugators p A B g).ncard =
      if orderOf g = p ∧ g ∈ A then
        Nat.card (Subgroup.centralizer {g}) * (conjugacyClassInter B g).ncard
      else 0 := by
  by_cases hg : orderOf g = p ∧ g ∈ A
  · rw [ite_eq_left hg]
    have heq : subgroupPrimeWitnessConjugators p A B g =
        {x : G | g ∈ MulAut.conj x • B} := by
      ext x
      simp only [subgroupPrimeWitnessConjugators, Set.mem_ofPred_eq, hg.1, hg.2, true_and]
    rw [heq, ncard_subgroup_conjugator_membership]
  · rw [ite_eq_right hg]
    have heq : subgroupPrimeWitnessConjugators p A B g = ∅ := by
      ext x
      simp only [subgroupPrimeWitnessConjugators, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
        iff_false]
      exact fun h ↦ hg ⟨h.1, h.2.1⟩
    rw [heq, Set.ncard_empty]

/-- One exact quadratic term for a restricted source row in an arbitrary
pair of subgroups. -/
def subgroupPrimeIncidenceClassTerm [Fintype G]
    (p : ℕ) (A B : Subgroup G) (primitive : G → Prop) (C : ConjClasses G) : ℕ :=
  (Nat.card G / C.carrier.ncard) *
    {g : G | ConjClasses.mk g = C ∧ orderOf g = p ∧ g ∈ A ∧ primitive g}.ncard *
      (C.carrier ∩ (B : Set G)).ncard

/-- Regrouping the restricted incidence count by conjugacy class is exact;
the predicate need not itself be invariant under conjugacy. -/
theorem sum_subgroupPrimeWitness_eq_quadraticClass_sum
    [Fintype G] (p : ℕ) (A B : Subgroup G) (primitive : G → Prop) :
    (∑ g : G, if primitive g then
      (subgroupPrimeWitnessConjugators p A B g).ncard else 0) =
      ∑ C : ConjClasses G, subgroupPrimeIncidenceClassTerm p A B primitive C := by
  classical
  let S : Finset G := Finset.univ.filter fun g ↦
    orderOf g = p ∧ g ∈ A ∧ primitive g
  let F : ConjClasses G → ℕ := fun C ↦
    (Nat.card G / C.carrier.ncard) * (C.carrier ∩ (B : Set G)).ncard
  have hstart :
      (∑ g : G, if primitive g then
        (subgroupPrimeWitnessConjugators p A B g).ncard else 0) =
      ∑ g ∈ S, F (ConjClasses.mk g) := by
    dsimp only [S]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g _hg
    rw [ncard_subgroupPrimeWitnessConjugators,
      card_centralizer_eq_card_div_conjugacyClass_ncard,
      conjugacyClassInter_eq_carrier_inter]
    dsimp [F]
    split_ifs <;> simp_all
  rw [hstart]
  calc
    (∑ g ∈ S, F (ConjClasses.mk g)) =
        ∑ C : ConjClasses G, ∑ g ∈ S with ConjClasses.mk g = C,
          F (ConjClasses.mk g) := by
      symm
      simpa only [Finset.mem_univ, ite_true, Finset.filter_true] using
        Finset.sum_fiberwise_eq_sum_filter S (Finset.univ : Finset (ConjClasses G))
          ConjClasses.mk (fun g ↦ F (ConjClasses.mk g))
    _ = ∑ C : ConjClasses G, (S.filter (fun g ↦ ConjClasses.mk g = C)).card * F C := by
      apply Finset.sum_congr rfl
      intro C _hC
      rw [← Finset.sum_const_nat]
      intro g hg
      exact congrArg F (Finset.mem_filter.mp hg).2
    _ = ∑ C : ConjClasses G, subgroupPrimeIncidenceClassTerm p A B primitive C := by
      apply Finset.sum_congr rfl
      intro C _hC
      have hrow : (S.filter (fun g ↦ ConjClasses.mk g = C)).card =
          {g : G | ConjClasses.mk g = C ∧ orderOf g = p ∧ g ∈ A ∧ primitive g}.ncard := by
        rw [Set.ncard_eq_toFinset_card']
        congr 1
        ext g
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_toFinset,
          Set.mem_ofPred_eq]
        tauto
      rw [hrow]
      dsimp [F, subgroupPrimeIncidenceClassTerm]
      ring

/-- Unrestricted structured witnesses are the special case of the
constant-true source predicate. -/
theorem sum_subgroupPrimeWitness_eq_quadraticClass_sum_all
    [Fintype G] (p : ℕ) (A B : Subgroup G) :
    (∑ g : G, (subgroupPrimeWitnessConjugators p A B g).ncard) =
      ∑ C : ConjClasses G, subgroupPrimeIncidenceClassTerm p A B (fun _ ↦ True) C := by
  simpa only [ite_true] using
    sum_subgroupPrimeWitness_eq_quadraticClass_sum p A B (fun _ ↦ True)

end LisiSabatini
