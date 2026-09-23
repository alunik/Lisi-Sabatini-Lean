module

public import LisiSabatini.SymmetricSmallDegreeMatchingProfile
public import LisiSabatini.SymmetricSmallDegreeSubgroupCost
public import LisiSabatini.AlternatingSylowQuadraticFormula

/-!
# Exact incidence costs for matching subgroups

The matching subgroup on `2 * m` points has `choose m j` elements of
cycle type `2^j`. Consequently its full involution incidence cost is
the sum of the squares of these binomial coefficients divided by the
corresponding symmetric-group conjugacy-class sizes.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

open Equiv

local instance matchingCostDecidableIsConj (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) := fun _ _ ↦ Classical.propDecidable _

private theorem matchingCost_orderOf_two_of_cycleType
    {n j : ℕ} {g : Perm (Fin n)} (hj : 0 < j)
    (hcycle : g.cycleType = Multiset.replicate j 2) : orderOf g = 2 := by
  have hpow : g ^ 2 = 1 := by
    apply Perm.pow_prime_eq_one_iff.2
    intro c hc
    rw [hcycle] at hc
    exact Multiset.eq_of_mem_replicate hc
  apply (Nat.prime_two.eq_one_or_self_of_dvd (orderOf g)
    (orderOf_dvd_of_pow_eq_one hpow)).resolve_left
  rw [orderOf_eq_one_iff]
  intro hg
  subst g
  have hjzero : j = 0 := by
    simpa using (congrArg Multiset.card hcycle).symm
  exact hj.ne' hjzero

/-- The unrestricted source row on a nonidentity matching class has the
same cardinal as the whole matching intersection with that class. -/
theorem ncard_matching_sourceRow_primeCycleTypeClass
    (m j : ℕ) (hj : 0 < j) (hjm : j ≤ m) :
    {g : Perm (Fin (2 * m)) |
      ConjClasses.mk g = primeCycleTypeClass (2 * m) 2 j ∧
      orderOf g = 2 ∧ g ∈ finPairFlipSubgroup m ∧ True}.ncard =
        Nat.choose m j := by
  have heq : {g : Perm (Fin (2 * m)) |
      ConjClasses.mk g = primeCycleTypeClass (2 * m) 2 j ∧
      orderOf g = 2 ∧ g ∈ finPairFlipSubgroup m ∧ True} =
      (primeCycleTypeClass (2 * m) 2 j).carrier ∩
        (finPairFlipSubgroup m : Set _) := by
    ext g
    constructor
    · rintro ⟨hclass, _, hmem, _⟩
      exact ⟨ConjClasses.mem_carrier_iff_mk_eq.mpr hclass, hmem⟩
    · rintro ⟨hclass, hmem⟩
      have hcycle : g.cycleType = Multiset.replicate j 2 := by
        rwa [carrier_primeCycleTypeClass
          (isValidPrimeCycleType_of_prime Nat.prime_two
            (Nat.mul_le_mul_left 2 hjm))] at hclass
      exact ⟨ConjClasses.mem_carrier_iff_mk_eq.mp hclass,
        matchingCost_orderOf_two_of_cycleType hj hcycle, hmem, trivial⟩
  rw [heq, ncard_primeCycleTypeClass_inter_finPairFlipSubgroup m j hjm]

/-- A canonical class contributes its class-index factor times the
square of the matching binomial coefficient. -/
theorem matchingIncidenceClassTerm_primeCycleTypeClass
    (m j : ℕ) (hj : 0 < j) (hjm : j ≤ m) :
    subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
      (finPairFlipSubgroup m) (fun _ ↦ True) (primeCycleTypeClass (2 * m) 2 j) =
      ((2 * m).factorial / primeCycleClassCard (2 * m) 2 j) *
        (Nat.choose m j) ^ 2 := by
  rw [subgroupPrimeIncidenceClassTerm, natCard_perm_fin,
    ncard_carrier_primeCycleTypeClass Nat.prime_two hj (Nat.mul_le_mul_left 2 hjm),
    ncard_matching_sourceRow_primeCycleTypeClass m j hj hjm,
    ncard_primeCycleTypeClass_inter_finPairFlipSubgroup m j hjm]
  ring

private theorem matching_sourceRow_eq_empty_of_not_mem_class_image
    (m : ℕ) (C : ConjClasses (Perm (Fin (2 * m))))
    (hC : C ∉ (Finset.Icc 1 m).image (primeCycleTypeClass (2 * m) 2)) :
    {g : Perm (Fin (2 * m)) | ConjClasses.mk g = C ∧
      orderOf g = 2 ∧ g ∈ finPairFlipSubgroup m ∧ True} = ∅ := by
  obtain ⟨P, hP⟩ := exists_sylow_two_ge_finPairFlipSubgroup m
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro g ⟨hclass, horder, hmem, _⟩
  have hrow : (primeOrderConjugacyClassRow 2 C (P : Subgroup _)).Nonempty := by
    exact ⟨g, (mem_primeOrderConjugacyClassRow_iff 2 C (P : Subgroup _) g).mpr
      ⟨hclass, hP hmem, horder⟩⟩
  have himage := primeOrderConjugacyClassRow_nonempty_implies_mem_primeCycleTypeClass_image
    Nat.prime_two P C hrow
  have hdiv : 2 * m / 2 = m := by omega
  exact hC (by simpa only [hdiv] using himage)

/-- Exact integer-scaled full matching incidence sum. -/
theorem sum_matchingIncidenceClassTerm_eq_binomial_sum (m : ℕ) :
    (∑ C : ConjClasses (Perm (Fin (2 * m))),
      subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
        (finPairFlipSubgroup m) (fun _ ↦ True) C) =
      ∑ j ∈ Finset.Icc 1 m,
        ((2 * m).factorial / primeCycleClassCard (2 * m) 2 j) *
          (Nat.choose m j) ^ 2 := by
  classical
  let classes := (Finset.Icc 1 m).image (primeCycleTypeClass (2 * m) 2)
  calc
    (∑ C : ConjClasses (Perm (Fin (2 * m))),
      subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
        (finPairFlipSubgroup m) (fun _ ↦ True) C) =
        ∑ C ∈ classes, subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
          (finPairFlipSubgroup m) (fun _ ↦ True) C := by
      symm
      apply Finset.sum_subset (Finset.subset_univ classes)
      intro C _ hC
      have hrow := matching_sourceRow_eq_empty_of_not_mem_class_image m C hC
      simp only [subgroupPrimeIncidenceClassTerm, hrow, Set.ncard_empty, mul_zero, zero_mul]
    _ = ∑ j ∈ Finset.Icc 1 m,
        subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
          (finPairFlipSubgroup m) (fun _ ↦ True) (primeCycleTypeClass (2 * m) 2 j) := by
      have hinj : Set.InjOn (primeCycleTypeClass (2 * m) 2)
          (↑(Finset.Icc 1 m) : Set ℕ) := by
        simpa using (primeCycleTypeClass_injective (n := 2 * m) Nat.prime_two)
      rw [Finset.sum_image hinj]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      exact matchingIncidenceClassTerm_primeCycleTypeClass m j
        (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

private theorem normalized_matching_factorial_term
    (m j r : ℕ) (hj : 0 < j) (hjm : j ≤ m) :
    ((((2 * m).factorial / primeCycleClassCard (2 * m) 2 j) * r ^ 2 : ℕ) : ℝ) /
        (Nat.card (Perm (Fin (2 * m))) : ℝ) =
      (r : ℝ) ^ 2 / (primeCycleClassCard (2 * m) 2 j : ℝ) := by
  have hpj := Nat.mul_le_mul_left 2 hjm
  obtain ⟨g, hgclass, _⟩ := cycleType_rep_primeCycleTypeClass
    (isValidPrimeCycleType_of_prime Nat.prime_two hpj)
  have hcpos : 0 < primeCycleClassCard (2 * m) 2 j := by
    rw [← ncard_carrier_primeCycleTypeClass Nat.prime_two hj hpj]
    exact Nat.pos_of_ne_zero <| Set.ncard_ne_zero_of_mem
      (ConjClasses.mem_carrier_iff_mk_eq.mpr hgclass)
  have hcard := conjugacyClass_ncard_mul_card_centralizer g
  rw [hgclass, ncard_carrier_primeCycleTypeClass Nat.prime_two hj hpj,
    natCard_perm_fin] at hcard
  have hcdvd : primeCycleClassCard (2 * m) 2 j ∣ (2 * m).factorial :=
    ⟨Nat.card (Subgroup.centralizer {g}), hcard.symm⟩
  have hcne : (primeCycleClassCard (2 * m) 2 j : ℝ) ≠ 0 := by
    exact_mod_cast hcpos.ne'
  have hnne : ((2 * m).factorial : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.factorial_pos (2 * m)).ne'
  rw [natCard_perm_fin, Nat.cast_mul, Nat.cast_pow, Nat.cast_div hcdvd hcne]
  field_simp

/-- The normalized full matching incidence cost is the binomial
quadratic class sum. -/
theorem normalized_matchingIncidenceCost_eq_binomial_sum (m : ℕ) :
    ((∑ C : ConjClasses (Perm (Fin (2 * m))),
      subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
        (finPairFlipSubgroup m) (fun _ ↦ True) C : ℕ) : ℝ) /
        (Nat.card (Perm (Fin (2 * m))) : ℝ) =
      ∑ j ∈ Finset.Icc 1 m,
        (Nat.choose m j : ℝ) ^ 2 / (primeCycleClassCard (2 * m) 2 j : ℝ) := by
  rw [sum_matchingIncidenceClassTerm_eq_binomial_sum, Nat.cast_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  exact normalized_matching_factorial_term m j (Nat.choose m j)
    (Finset.mem_Icc.mp hj).1 (Finset.mem_Icc.mp hj).2

/-- Restricting the matching source row to transpositions leaves one
conjugacy class and exactly `m` witnesses on each side. -/
theorem sum_matchingSwapIncidenceClassTerm_eq (m : ℕ) (hm : 0 < m) :
    (∑ C : ConjClasses (Perm (Fin (2 * m))),
      subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
        (finPairFlipSubgroup m) (fun g ↦ g.IsSwap) C) =
      ((2 * m).factorial / primeCycleClassCard (2 * m) 2 1) * m ^ 2 := by
  classical
  let C₁ := primeCycleTypeClass (2 * m) 2 1
  have hpj : 2 * 1 ≤ 2 * m := by omega
  have hclass (g : Perm (Fin (2 * m))) : ConjClasses.mk g = C₁ ↔ g.IsSwap := by
    rw [← ConjClasses.mem_carrier_iff_mk_eq,
      carrier_primeCycleTypeClass (isValidPrimeCycleType_of_prime Nat.prime_two hpj)]
    simp only [Set.mem_ofPred_eq, Multiset.replicate_one, Perm.isSwap_iff_cycleType]
  have hcollapse :
      (∑ C : ConjClasses (Perm (Fin (2 * m))),
        subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
          (finPairFlipSubgroup m) (fun g ↦ g.IsSwap) C) =
        subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
          (finPairFlipSubgroup m) (fun g ↦ g.IsSwap) C₁ := by
    apply Finset.sum_eq_single C₁
    · intro C _ hC
      have hrow : {g : Perm (Fin (2 * m)) | ConjClasses.mk g = C ∧
          orderOf g = 2 ∧ g ∈ finPairFlipSubgroup m ∧ g.IsSwap} = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro g ⟨hgclass, _, _, hswap⟩
        exact hC (hgclass.symm.trans ((hclass g).mpr hswap))
      simp only [subgroupPrimeIncidenceClassTerm, hrow, Set.ncard_empty, mul_zero, zero_mul]
    · simp
  have hrow : {g : Perm (Fin (2 * m)) | ConjClasses.mk g = C₁ ∧
      orderOf g = 2 ∧ g ∈ finPairFlipSubgroup m ∧ g.IsSwap} =
      {g : Perm (Fin (2 * m)) | g ∈ finPairFlipSubgroup m ∧ g.IsSwap} := by
    ext g
    constructor
    · rintro ⟨_, _, hmem, hswap⟩
      exact ⟨hmem, hswap⟩
    · rintro ⟨hmem, hswap⟩
      exact ⟨(hclass g).mpr hswap, hswap.orderOf, hmem, hswap⟩
  rw [hcollapse, subgroupPrimeIncidenceClassTerm, hrow,
    ncard_finPairFlipSubgroup_isSwap, natCard_perm_fin]
  dsimp only [C₁]
  rw [ncard_carrier_primeCycleTypeClass Nat.prime_two (by decide) hpj,
    ncard_primeCycleTypeClass_inter_finPairFlipSubgroup m 1 (by omega), Nat.choose_one_right]
  ring

/-- The normalized primitive matching incidence cost is the square of
the number of edges divided by the transposition conjugacy-class size. -/
theorem normalized_matchingSwapIncidenceCost_eq (m : ℕ) (hm : 0 < m) :
    ((∑ C : ConjClasses (Perm (Fin (2 * m))),
      subgroupPrimeIncidenceClassTerm 2 (finPairFlipSubgroup m)
        (finPairFlipSubgroup m) (fun g ↦ g.IsSwap) C : ℕ) : ℝ) /
        (Nat.card (Perm (Fin (2 * m))) : ℝ) =
      (m : ℝ) ^ 2 / (primeCycleClassCard (2 * m) 2 1 : ℝ) := by
  rw [sum_matchingSwapIncidenceClassTerm_eq m hm]
  exact normalized_matching_factorial_term m 1 m (by decide) (by omega)

end LisiSabatini
