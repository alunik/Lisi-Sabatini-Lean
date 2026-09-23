module

public import LisiSabatini.AlternatingSylowQuadraticFormula
public import LisiSabatini.TransitiveActionProbability

/-!
# Exact quadratic costs in normal subgroups

Frattini's argument makes the ambient conjugation action transitive on the
Sylow subgroups of a normal subgroup. Uniform averaging on this action avoids
any separate analysis of splitting conjugacy classes.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini

universe uG

local instance normalCostDecidableIsConj (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _

local instance normalCostDecidableProp (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Ambient conjugation acts on the Sylow subgroups of a normal subgroup. -/
@[instance_reducible] def normalSubgroupSylowAction
    {G : Type uG} [Group G] (H : Subgroup G) [H.Normal] (p : ℕ) :
    MulAction G (Sylow p H) :=
  MulAction.compHom (Sylow p H) (MulAut.conjNormal (H := H))

/-- The ambient action contains the transitive conjugation action of H. -/
theorem normalSubgroupSylowAction_pretransitive
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] {p : ℕ} [Fact p.Prime] :
    letI := normalSubgroupSylowAction H p
    MulAction.IsPretransitive G (Sylow p H) := by
  have htrans : ∀ Q R : Sylow p H, ∃ h : H, h • Q = R :=
    fun Q R ↦ MulAction.exists_smul_eq H Q R
  let := normalSubgroupSylowAction H p
  constructor
  intro Q R
  obtain ⟨h, hh⟩ := htrans Q R
  refine ⟨(h : G), ?_⟩
  change (MulAut.conjNormal (H := H) (h : G)) • Q = R
  rw [MulAut.conjNormal_val]
  exact hh

/-- Intersecting an ambient conjugate with H gives the conjugate under the
normal-subgroup action. -/
theorem normalSubgroupSylowAction_mem_iff
    {G : Type uG} [Group G]
    (H : Subgroup G) [H.Normal] {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) (x : G) (y : H) :
    letI := normalSubgroupSylowAction H p
    y ∈ ((x • Q : Sylow p H) : Subgroup H) ↔
      (y : G) ∈ ((x • P : Sylow p G) : Subgroup G) := by
  let := normalSubgroupSylowAction H p
  change y ∈ (MulAut.conjNormal (H := H) x) • (Q : Subgroup H) ↔
    (y : G) ∈ (MulAut.conj x) • (P : Subgroup G)
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  rw [← hPQ]
  change ((MulAut.conjNormal (H := H) x)⁻¹ y : G) ∈ (P : Subgroup G) ↔
    (MulAut.conj x)⁻¹ (y : G) ∈ (P : Subgroup G)
  rw [← map_inv, ← map_inv, MulAut.conjNormal_apply]
  rfl

/-- The probability that a conjugate contains a fixed element of H is
unchanged by passage from G to H. -/
theorem sylowMembership_probability_eq_of_normal
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) (y : H) :
    ((sylowConjugatorMembershipSet P (y : G)).ncard : ℝ) / Nat.card G =
      ((sylowConjugatorMembershipSet Q y).ncard : ℝ) / Nat.card H := by
  let S : Set (Sylow p H) := {R | y ∈ (R : Subgroup H)}
  have hH : ((sylowConjugatorMembershipSet Q y).ncard : ℝ) / Nat.card H =
      (S.ncard : ℝ) / Nat.card (Sylow p H) :=
    ncard_smul_into_set_div_card_eq (A := H) Q S
  let := normalSubgroupSylowAction H p
  let := normalSubgroupSylowAction_pretransitive H (p := p)
  have hG := ncard_smul_into_set_div_card_eq (A := G) Q S
  have heq : {x : G | x • Q ∈ S} = sylowConjugatorMembershipSet P (y : G) := by
    ext x
    exact normalSubgroupSylowAction_mem_iff H P Q hPQ x y
  rw [heq] at hG
  exact hG.trans hH.symm

/-- Regrouping remains exact after restricting to ambient classes meeting a
normal subgroup. -/
theorem restricted_transporter_sum_eq_quadraticClass_sum
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] {p : ℕ} (P : Sylow p G) :
    (∑ g ∈ primeOrderElements p G,
      if g ∈ (P : Subgroup G) ∧ g ∈ H then
        (sylowConjugatorMembershipSet P g).ncard else 0) =
      ∑ C : ConjClasses G,
        if ambientConjClassMeetsSubgroup H C then
          mixedSylowPairQuadraticClassTerm P P C else 0 := by
  classical
  rw [← Finset.sum_filter]
  let S := (primeOrderElements p G).filter
    (fun g ↦ g ∈ (P : Subgroup G) ∧ g ∈ H)
  simp_rw [ncard_sylowConjugatorMembershipSet_eq_centralizer_mul_classInter,
    card_centralizer_eq_card_div_conjugacyClass_ncard,
    conjugacyClassInter_eq_carrier_inter]
  let F : ConjClasses G → ℕ := fun C ↦
    (Nat.card G / C.carrier.ncard) *
      (C.carrier ∩ ((P : Subgroup G) : Set G)).ncard
  change (∑ g ∈ S, F (ConjClasses.mk g)) = _
  rw [← Finset.sum_fiberwise S ConjClasses.mk (fun g ↦ F (ConjClasses.mk g))]
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : ambientConjClassMeetsSubgroup H C
  · rw [ite_eq_left hC]
    have hfilter : S.filter (fun g ↦ ConjClasses.mk g = C) =
        ((primeOrderElements p G).filter (fun g ↦ g ∈ (P : Subgroup G))).filter
          (fun g ↦ ConjClasses.mk g = C) := by
      ext g
      simp only [S, Finset.mem_filter]
      constructor
      · tauto
      · rintro ⟨⟨hg, hgP⟩, hgC⟩
        refine ⟨⟨hg, hgP, ?_⟩, hgC⟩
        apply (ambientConjClassMeetsSubgroup_mk_iff H g).mp
        rwa [hgC]
    calc
      _ = (S.filter (fun g ↦ ConjClasses.mk g = C)).card * F C := by
        rw [← Finset.sum_const_nat]
        intro g hg
        exact congrArg F (Finset.mem_filter.mp hg).2
      _ = _ := by
        rw [hfilter, card_primeOrderElements_filter_sylow_filter_mk_eq]
        simp only [F, mixedSylowPairQuadraticClassTerm]
        ring
  · rw [ite_eq_right hC]
    apply Finset.sum_eq_zero
    intro g hg
    have hg' := Finset.mem_filter.mp hg
    have hgH : g ∈ H := (Finset.mem_filter.mp hg'.1).2.2
    apply False.elim
    apply hC
    rw [← hg'.2]
    exact (ambientConjClassMeetsSubgroup_mk_iff H g).mpr hgH

/-- Summing a pointwise quantity over the linked rows can be performed either
in H or in the ambient group with the H-membership restriction. -/
theorem sum_primeOrder_linked_rows
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q)
    (fG : G → ℝ) (fH : H → ℝ) (hf : ∀ y : H, fG y = fH y) :
    (∑ y ∈ primeOrderElements p H,
      if y ∈ (Q : Subgroup H) then fH y else 0) =
    ∑ g ∈ primeOrderElements p G,
      if g ∈ (P : Subgroup G) ∧ g ∈ H then fG g else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  refine Finset.sum_bij (fun y _ ↦ (y : G)) ?_ ?_ ?_ ?_
  · intro y hy
    have hy' := Finset.mem_filter.mp hy
    apply Finset.mem_filter.mpr
    refine ⟨?_, ?_, y.property⟩
    · rw [mem_primeOrderElements_iff] at hy' ⊢
      simpa only [orderOf_submonoid] using hy'.1
    · change y ∈ P.comap H.subtype
      rw [hPQ]
      exact hy'.2
  · intro y _ z _ hyz
    exact Subtype.coe_injective hyz
  · intro g hg
    have hg' := Finset.mem_filter.mp hg
    refine ⟨⟨g, hg'.2.2⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · rw [mem_primeOrderElements_iff] at hg' ⊢
      change orderOf (⟨g, hg'.2.2⟩ : H) = p
      rw [← orderOf_submonoid]
      exact hg'.1
    · rw [← hPQ]
      exact hg'.2.1
  · intro y _
    exact (hf y).symm

/-- Exact equality of normalized quadratic class costs across any normal
subgroup. The ambient sum is restricted to classes meeting that subgroup. -/
theorem normalizedQuadraticCost_normal_subgroup_eq
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] [Fintype H] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) :
    normalizedSameRowSylowQuadraticCost H Q =
      normalizedSameRowSylowQuadraticCostMeetingSubgroup H P := by
  unfold normalizedSameRowSylowQuadraticCost normalizedSameRowSylowQuadraticCostMeetingSubgroup
  rw [← mixedSylowPair_transporter_sum_eq_quadraticClass_sum Q Q,
    ← restricted_transporter_sum_eq_quadraticClass_sum H P]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, div_eq_mul_inv,
    Finset.sum_mul, ite_mul, zero_mul]
  simpa only [div_eq_mul_inv] using sum_primeOrder_linked_rows H P Q hPQ
    (fun g ↦ ((sylowConjugatorMembershipSet P g).ncard : ℝ) / Nat.card G)
    (fun y ↦ ((sylowConjugatorMembershipSet Q y).ncard : ℝ) / Nat.card H)
    (sylowMembership_probability_eq_of_normal H P Q hPQ)

/-- For odd p every contributing symmetric class already consists of even
permutations. Restricting the ambient quadratic sum therefore changes nothing. -/
theorem quadraticCostMeetingAlternating_eq_of_odd
    {n p : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    (P : Sylow p (Equiv.Perm (Fin n))) :
    normalizedSameRowSylowQuadraticCostMeetingSubgroup (alternatingGroup (Fin n)) P =
      normalizedSameRowSylowQuadraticCost (Equiv.Perm (Fin n)) P := by
  unfold normalizedSameRowSylowQuadraticCostMeetingSubgroup normalizedSameRowSylowQuadraticCost
  congr 2
  apply Finset.sum_congr rfl
  intro C _
  by_cases hC : ambientConjClassMeetsSubgroup (alternatingGroup (Fin n)) C
  · exact ite_eq_left hC
  · rw [ite_eq_right hC]
    have hrow : primeOrderConjugacyClassRow p C (P : Subgroup (Equiv.Perm (Fin n))) = ∅ := by
      apply Set.not_nonempty_iff_eq_empty.mp
      intro hnonempty
      have hmem := primeOrderConjugacyClassRow_nonempty_implies_mem_primeCycleTypeClass_image
        hp P C hnonempty
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hmem
      have hpj : p * j ≤ n := by
        simpa only [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hp.pos).mp (Finset.mem_Icc.mp hj).2
      exact hC (ambientConjClassMeetsAlternating_primeCycleTypeClass_of_odd hp hpOdd hpj)
    simp only [mixedSylowPairQuadraticClassTerm, hrow, Set.ncard_empty, mul_zero, zero_mul]

/-- The alternating Sylow quadratic cost equals the restricted symmetric
cycle profile exactly, with no index-two loss and no degree restriction. -/
theorem normalizedQuadraticCost_alternating_eq_profile
    {n p : ℕ} (hp : p.Prime)
    (Q : Sylow p (alternatingGroup (Fin n))) :
    normalizedSameRowSylowQuadraticCost (alternatingGroup (Fin n)) Q =
      alternatingSylowProfileQuadraticCost n p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPQ⟩ := Q.exists_comap_subtype_eq
  rw [normalizedQuadraticCost_normal_subgroup_eq (alternatingGroup (Fin n)) P Q hPQ]
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    exact normalizedSameRowSylowQuadraticCostMeetingAlternating_perm_eq_profile P
  · have hpOdd : Odd p := Nat.odd_iff.mpr hodd
    rw [quadraticCostMeetingAlternating_eq_of_odd hp hpOdd P,
      normalizedSameRowSylowQuadraticCost_perm_eq_profile hp P,
      alternatingSylowProfileQuadraticCost, ite_eq_right (by omega : p ≠ 2)]

end LisiSabatini
