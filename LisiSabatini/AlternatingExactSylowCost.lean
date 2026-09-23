module

public import LisiSabatini.AlternatingSylowQuadraticFormula

/-!
# Sharper transfer of quadratic Sylow costs

Conjugacy classes of a subgroup over one ambient conjugacy class give disjoint
rows. Summing their row sizes before estimating the quadratic terms avoids the
extraneous factor coming from the number of classes in a fiber. The resulting
normalized transfer loses only the subgroup index, hence only two for `A_n`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uG

local instance exactCostDecidableIsConj (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _

local instance exactCostDecidableProp (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- The order-`p` rows in a fiber of the map on conjugacy classes are disjoint;
their total cardinality is at most the corresponding ambient row. -/
theorem sum_primeOrderRow_fiber_le
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) [Fintype H] (p : ℕ)
    (K : Subgroup G) (L : Subgroup H)
    (hKL : K.comap H.subtype = L) (C : ConjClasses G) :
    (∑ D ∈ (Finset.univ : Finset (ConjClasses H)).filter
        (fun D ↦ ConjClasses.map H.subtype D = C),
      (primeOrderConjugacyClassRow p D L).ncard) ≤
        (primeOrderConjugacyClassRow p C K).ncard := by
  classical
  let := Fintype.ofFinite G
  let S := (Finset.univ : Finset (ConjClasses H)).filter
    (fun D ↦ ConjClasses.map H.subtype D = C)
  let row := fun D : ConjClasses H ↦
    (primeOrderConjugacyClassRow p D L).toFinset.image H.subtype
  have hrowcard (D : ConjClasses H) :
      (row D).card = (primeOrderConjugacyClassRow p D L).ncard := by
    dsimp [row]
    rw [Finset.card_image_of_injective _ Subtype.coe_injective]
    exact (Set.ncard_eq_toFinset_card' _).symm
  have hdisjoint : (S : Set (ConjClasses H)).PairwiseDisjoint row := by
    intro D _ E _ hDE
    apply Finset.disjoint_left.mpr
    intro x hxD hxE
    obtain ⟨d, hd, hdx⟩ := Finset.mem_image.mp hxD
    obtain ⟨e, he, hex⟩ := Finset.mem_image.mp hxE
    have hde : d = e := Subtype.coe_injective (hdx.trans hex.symm)
    subst e
    have hd' := (mem_primeOrderConjugacyClassRow_iff p D L d).mp
      (Set.mem_toFinset.mp hd)
    have he' := (mem_primeOrderConjugacyClassRow_iff p E L d).mp
      (Set.mem_toFinset.mp he)
    exact hDE (hd'.1.symm.trans he'.1)
  have hsubset : S.biUnion row ⊆ (primeOrderConjugacyClassRow p C K).toFinset := by
    intro x hx
    obtain ⟨D, hD, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    have hd' := (mem_primeOrderConjugacyClassRow_iff p D L d).mp
      (Set.mem_toFinset.mp hd)
    apply Set.mem_toFinset.mpr
    apply (mem_primeOrderConjugacyClassRow_iff p C K (d : G)).mpr
    refine ⟨?_, ?_, ?_⟩
    · exact (congrArg (ConjClasses.map H.subtype) hd'.1).trans
        (Finset.mem_filter.mp hD).2
    · change d ∈ K.comap H.subtype
      rw [hKL]
      exact hd'.2.1
    · simpa only [orderOf_submonoid] using hd'.2.2
  calc
    _ = ∑ D ∈ S, (row D).card := by
      apply Finset.sum_congr rfl
      intro D _
      exact (hrowcard D).symm
    _ = (S.biUnion row).card := (Finset.card_biUnion hdisjoint).symm
    _ ≤ (primeOrderConjugacyClassRow p C K).toFinset.card :=
      Finset.card_le_card hsubset
    _ = _ := (Set.ncard_eq_toFinset_card' _).symm

/-- The unnormalized same-row quadratic sum cannot increase under passage to
a linked Sylow row in a subgroup. No index or normality assumption is needed. -/
theorem quadraticClassSum_subgroup_le_restricted
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) :
    (∑ D : ConjClasses H, mixedSylowPairQuadraticClassTerm Q Q D) ≤
      ∑ C : ConjClasses G,
        if ambientConjClassMeetsSubgroup H C then
          mixedSylowPairQuadraticClassTerm P P C else 0 := by
  classical
  let f : ConjClasses H → ConjClasses G := ConjClasses.map H.subtype
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (ConjClasses H))
    f (mixedSylowPairQuadraticClassTerm Q Q)]
  apply Finset.sum_le_sum
  intro C _
  by_cases hC : ambientConjClassMeetsSubgroup H C
  · rw [ite_eq_left hC]
    let a := Nat.card G / C.carrier.ncard
    let b := (C.carrier ∩ ((P : Subgroup G) : Set G)).ncard
    calc
      _ ≤ ∑ D ∈ (Finset.univ : Finset (ConjClasses H)).filter (fun D ↦ f D = C),
          a * (primeOrderConjugacyClassRow p D (Q : Subgroup H)).ncard * b := by
        apply Finset.sum_le_sum
        intro D hD
        have hmap : ConjClasses.map H.subtype D = C := (Finset.mem_filter.mp hD).2
        have ha := card_div_conjClass_subgroup_le H D
        have hb := ncard_conjClass_inter_comap_le H P Q hPQ D
        rw [hmap] at ha hb
        exact Nat.mul_le_mul
          (Nat.mul_le_mul_right _ ha) hb
      _ = a * (∑ D ∈ (Finset.univ : Finset (ConjClasses H)).filter (fun D ↦ f D = C),
          (primeOrderConjugacyClassRow p D (Q : Subgroup H)).ncard) * b := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ a * (primeOrderConjugacyClassRow p C (P : Subgroup G)).ncard * b :=
        Nat.mul_le_mul_right b (Nat.mul_le_mul_left a
          (sum_primeOrderRow_fiber_le H p P Q hPQ C))
      _ = _ := rfl
  · rw [ite_eq_right hC]
    apply Nat.le_zero.mpr
    apply Finset.sum_eq_zero
    intro D hD
    exact False.elim (hC (carrier_inter_subgroup_nonempty_of_map_subtype_eq H
      (Finset.mem_filter.mp hD).2))

/-- Normalization costs only the subgroup index. In particular the linked
alternating row loses at most two, rather than the previous factor four. -/
theorem normalizedQuadraticCost_subgroup_le_index_mul
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [Fintype H] {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) :
    normalizedSameRowSylowQuadraticCost H Q ≤
      (H.index : ℝ) * normalizedSameRowSylowQuadraticCostMeetingSubgroup H P := by
  have hsum := quadraticClassSum_subgroup_le_restricted H P Q hPQ
  have hsumR :
      ((∑ D : ConjClasses H, mixedSylowPairQuadraticClassTerm Q Q D : ℕ) : ℝ) ≤
        ((∑ C : ConjClasses G,
          if ambientConjClassMeetsSubgroup H C then
            mixedSylowPairQuadraticClassTerm P P C else 0 : ℕ) : ℝ) := by
    exact_mod_cast hsum
  have hcard : (H.index : ℝ) * (Nat.card H : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast H.index_mul_card
  have hpos : (0 : ℝ) < Nat.card H := by exact_mod_cast (Nat.card_pos (α := H))
  have hindex : (H.index : ℝ) ≠ 0 := by
    have hG : (0 : ℝ) < Nat.card G := by exact_mod_cast (Nat.card_pos (α := G))
    intro hz
    rw [hz, zero_mul] at hcard
    linarith
  unfold normalizedSameRowSylowQuadraticCost normalizedSameRowSylowQuadraticCostMeetingSubgroup
  calc
    _ ≤ _ := div_le_div_of_nonneg_right hsumR hpos.le
    _ = _ := by rw [← hcard]; field_simp

/-- The factor-two alternating transfer, restricted to even ambient classes. -/
theorem alternatingLinkedRowQuadraticTransfer_two
    {n p : ℕ} (hn : 2 ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n)))
    (Q : Sylow p (alternatingGroup (Fin n)))
    (hPQ : P.comap (alternatingGroup (Fin n)).subtype = Q) :
    normalizedSameRowSylowQuadraticCost (alternatingGroup (Fin n)) Q ≤
      2 * normalizedSameRowSylowQuadraticCostMeetingSubgroup
        (alternatingGroup (Fin n)) P := by
  let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  simpa only [alternatingGroup.index_eq_two, Nat.cast_ofNat] using
    normalizedQuadraticCost_subgroup_le_index_mul (alternatingGroup (Fin n)) P Q hPQ

/-- Restricting to classes meeting a subgroup only lowers the ambient cost. -/
theorem normalizedQuadraticCostMeetingSubgroup_le
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) {p : ℕ} (P : Sylow p G) :
    normalizedSameRowSylowQuadraticCostMeetingSubgroup H P ≤
      normalizedSameRowSylowQuadraticCost G P := by
  unfold normalizedSameRowSylowQuadraticCostMeetingSubgroup
    normalizedSameRowSylowQuadraticCost
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.sum_le_sum fun C (_ : C ∈ (Finset.univ : Finset (ConjClasses G))) ↦
    show (if ambientConjClassMeetsSubgroup H C then
      mixedSylowPairQuadraticClassTerm P P C else 0) ≤
        mixedSylowPairQuadraticClassTerm P P C from
      by split_ifs <;> omega)

/-- The sharpened pointwise bound consumed by finite alternating budgets. -/
theorem normalizedQuadraticCost_alternating_le_two_profile
    {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (Q : Sylow p (alternatingGroup (Fin n))) :
    normalizedSameRowSylowQuadraticCost (alternatingGroup (Fin n)) Q ≤
      2 * alternatingSylowProfileQuadraticCost n p := by
  obtain ⟨P, hPQ⟩ := Q.exists_comap_subtype_eq
  have htransfer := alternatingLinkedRowQuadraticTransfer_two hn P Q hPQ
  by_cases htwo : p = 2
  · subst p
    rwa [normalizedSameRowSylowQuadraticCostMeetingAlternating_perm_eq_profile P] at htransfer
  · calc
      _ ≤ 2 * normalizedSameRowSylowQuadraticCostMeetingSubgroup
          (alternatingGroup (Fin n)) P := htransfer
      _ ≤ 2 * normalizedSameRowSylowQuadraticCost (Equiv.Perm (Fin n)) P :=
        mul_le_mul_of_nonneg_left
          (normalizedQuadraticCostMeetingSubgroup_le (alternatingGroup (Fin n)) P) (by norm_num)
      _ = 2 * alternatingSylowProfileQuadraticCost n p := by
        rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile hp P,
          alternatingSylowProfileQuadraticCost, ite_eq_right htwo]

end LisiSabatini
