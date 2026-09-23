module

public import LisiSabatini.CyclicSylowQuadraticBound

/-!
# Compressing redundant prime-order witnesses

A structured subgroup can supply many simultaneous witnesses for the same
bad conjugator. If its nontrivial intersections always have a primitive
witness, replace the structured incidence count by the primitive incidence
count. This retains an exact integral inequality and avoids subtraction in
natural numbers.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini

universe uG uI uX

local instance compressionDecidableProp (P : Prop) : Decidable P := Classical.propDecidable P
local instance compressionDecidableEq (X : Type*) : DecidableEq X := Classical.decEq X
local instance compressionDecidableRel (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _

/-- A union bound with a family of redundant witnesses replaced by a
covering family of primitive witnesses. -/
theorem card_biUnion_add_redundant_le_sum_add_primitive
    {I : Type uI} {X : Type uX} [Fintype I] [Finite X]
    (F D E : I → Finset X)
    (hDF : ∀ i, D i ⊆ F i)
    (hcover : ∀ x, (∃ i, x ∈ D i) → ∃ i, x ∈ E i) :
    (Finset.univ.biUnion F).card + ∑ i, (D i).card ≤
      (∑ i, (F i).card) + ∑ i, (E i).card := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let degree : (I → Finset X) → X → ℕ := fun W x ↦
    (Finset.univ.filter fun i ↦ x ∈ W i).card
  have hsum (W : I → Finset X) : ∑ x, degree W x = ∑ i, (W i).card := by
    simp only [degree, Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [← Finset.sum_filter]
    simp
  have hunion :
      ∑ x : X, (if x ∈ Finset.univ.biUnion F then 1 else 0 : ℕ) =
        (Finset.univ.biUnion F).card := by
    simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter, Nat.cast_id]
  have hpoint (x : X) :
      (if x ∈ Finset.univ.biUnion F then 1 else 0 : ℕ) + degree D x ≤
        degree F x + degree E x := by
    have hle : degree D x ≤ degree F x := by
      apply Finset.card_le_card
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hDF i (Finset.mem_filter.mp hi).2⟩
    by_cases hFx : x ∈ Finset.univ.biUnion F
    · rw [ite_eq_left hFx]
      by_cases hDx : ∃ i, x ∈ D i
      · obtain ⟨i, hi⟩ := hcover x hDx
        have hE : 0 < degree E x := Finset.card_pos.mpr
          ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
        omega
      · have hD : degree D x = 0 := by
          apply Finset.card_eq_zero.mpr
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro i hi
          exact hDx ⟨i, (Finset.mem_filter.mp hi).2⟩
        have hF : 0 < degree F x := by
          obtain ⟨i, _hi, hxi⟩ := Finset.mem_biUnion.mp hFx
          exact Finset.card_pos.mpr ⟨i,
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxi⟩⟩
        omega
    · rw [ite_eq_right hFx]
      omega
  have h := Finset.sum_le_sum (fun x (_hx : x ∈ (Finset.univ : Finset X)) ↦ hpoint x)
  simpa only [Finset.sum_add_distrib, hunion, hsum] using h

/-- Prime-order incidences for two prescribed subgroups. -/
def subgroupPrimeWitnessConjugators
    {G : Type uG} [Group G] (p : ℕ) (A B : Subgroup G) (g : G) : Set G :=
  {x | orderOf g = p ∧ g ∈ A ∧ g ∈ MulAut.conj x • B}

/-- A primitive-witness compression of the full Sylow quadratic bound.

The input says precisely that every nontrivial prime-order intersection of
`A` with a conjugate of `B` has a witness satisfying `primitive`. The other
hypotheses are literal subgroup inclusions. -/
theorem bad_ncard_add_structured_le_quadratic_add_primitive
    {G : Type uG} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) (A B : Subgroup G)
    (hAP : A ≤ (P : Subgroup G)) (hBQ : B ≤ (Q : Subgroup G))
    (primitive : G → Prop)
    (hprimitive : ∀ (x g : G), orderOf g = p → g ∈ A → g ∈ MulAut.conj x • B →
      ∃ h, orderOf h = p ∧ h ∈ A ∧ h ∈ MulAut.conj x • B ∧ primitive h) :
    (mixedSylowPairBadConjugators P Q).ncard +
        ∑ g : G, (subgroupPrimeWitnessConjugators p A B g).ncard ≤
      (∑ C : ConjClasses G, mixedSylowPairQuadraticClassTerm P Q C) +
        ∑ g : G, (if primitive g then
          (subgroupPrimeWitnessConjugators p A B g).ncard else 0) := by
  classical
  let F : G → Finset G := fun g ↦
    (subgroupPrimeWitnessConjugators p (P : Subgroup G) (Q : Subgroup G) g).toFinset
  let D : G → Finset G := fun g ↦ (subgroupPrimeWitnessConjugators p A B g).toFinset
  let E : G → Finset G := fun g ↦ if primitive g then D g else ∅
  have hDF : ∀ g, D g ⊆ F g := by
    intro g x hx
    obtain ⟨hg, hA, hB⟩ := Set.mem_toFinset.mp hx
    refine Set.mem_toFinset.mpr ⟨hg, hAP hA, ?_⟩
    exact (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hBQ) hB
  have hcover : ∀ x, (∃ g, x ∈ D g) → ∃ g, x ∈ E g := by
    rintro x ⟨g, hxg⟩
    obtain ⟨hg, hA, hB⟩ := Set.mem_toFinset.mp hxg
    obtain ⟨h, hh, hhA, hhB, hprim⟩ := hprimitive x g hg hA hB
    refine ⟨h, ?_⟩
    simp only [E, ite_eq_left hprim]
    exact Set.mem_toFinset.mpr ⟨hh, hhA, hhB⟩
  have hunion : Finset.univ.biUnion F = (mixedSylowPairBadConjugators P Q).toFinset := by
    ext x
    rw [Finset.mem_biUnion, Set.mem_toFinset,
      mem_mixedSylowPairBadConjugators_iff_exists_primeOrder_witness]
    constructor
    · rintro ⟨g, _hg, hxg⟩
      have hxg' : orderOf g = p ∧ g ∈ (P : Subgroup G) ∧
          g ∈ MulAut.conj x • (Q : Subgroup G) :=
        (Set.mem_toFinset (s := subgroupPrimeWitnessConjugators p
          (P : Subgroup G) (Q : Subgroup G) g)).mp hxg
      exact ⟨g, hxg'.1, hxg'.2⟩
    · rintro ⟨g, hg, hxg⟩
      exact ⟨g, Finset.mem_univ _, Set.mem_toFinset.mpr ⟨hg, hxg⟩⟩
  have htotal : (∑ g, (F g).card) =
      ∑ C : ConjClasses G, mixedSylowPairQuadraticClassTerm P Q C := by
    rw [← mixedSylowPair_transporter_sum_eq_quadraticClass_sum P Q]
    rw [primeOrderElements, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro g _hg
    by_cases ho : orderOf g = p
    · rw [ite_eq_left ho]
      have heq : F g = (mixedSylowPairPrimeWitnessConjugators P Q g).toFinset := by
        ext x
        change x ∈ (subgroupPrimeWitnessConjugators p
            (P : Subgroup G) (Q : Subgroup G) g).toFinset ↔ _
        rw [Set.mem_toFinset, Set.mem_toFinset]
        change (orderOf g = p ∧ g ∈ (P : Subgroup G) ∧
          g ∈ MulAut.conj x • (Q : Subgroup G)) ↔
          (g ∈ (P : Subgroup G) ∧ g ∈ ((x • Q : Sylow p G) : Subgroup G))
        simp only [ho, true_and, Sylow.coe_subgroup_smul]
      rw [heq, ← Set.ncard_eq_toFinset_card', ncard_mixedSylowPairPrimeWitnessConjugators]
    · rw [ite_eq_right ho]
      have heq : F g = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        exact ho (Set.mem_toFinset.mp hx).1
      rw [heq, Finset.card_empty]
  have hDcard : (∑ g, (D g).card) =
      ∑ g : G, (subgroupPrimeWitnessConjugators p A B g).ncard := by
    apply Finset.sum_congr rfl
    intro g _hg
    exact (Set.ncard_eq_toFinset_card' _).symm
  have hEcard : (∑ g, (E g).card) =
      ∑ g : G, (if primitive g then
        (subgroupPrimeWitnessConjugators p A B g).ncard else 0) := by
    apply Finset.sum_congr rfl
    intro g _hg
    dsimp [E]
    split_ifs
    · exact (Set.ncard_eq_toFinset_card' _).symm
    · exact Finset.card_empty
  have h := card_biUnion_add_redundant_le_sum_add_primitive F D E hDF hcover
  rwa [hunion, ← Set.ncard_eq_toFinset_card', htotal, hDcard, hEcard] at h

end LisiSabatini
