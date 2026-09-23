module

public import LisiSabatini.AlternatingSylowBasePBlocks
public import LisiSabatini.SylowPairQuadraticIndexTwo

/-!
# Exact quadratic class sums for symmetric Sylow rows

This file identifies the normalized quadratic conjugacy-class sum of a
Sylow `p`-subgroup of `S_n` with the arithmetic cycle-profile cost from
`AlternatingSylowCycleProfile`.

The proof has two parts.  First, an order-`p` permutation has cycle type
`p^j` for a unique `1 ≤ j ≤ n / p`, so every other conjugacy-class term
vanishes.  Second, the base-`p` block Sylow construction identifies the
intersection cardinal of that class with the corresponding coefficient
of `sylowCycleProfile`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

local instance alternatingQuadraticFormulaDecidableIsConj
    (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

local instance alternatingQuadraticFormulaDecidableProp
    (P : Prop) : Decidable P :=
  Classical.propDecidable P

private theorem orderOf_eq_prime_of_cycleType_eq_replicate
    {n p j : ℕ} {g : Equiv.Perm (Fin n)}
    (hp : p.Prime)
    (hj : 0 < j)
    (hcycle : g.cycleType = Multiset.replicate j p) :
    orderOf g = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hpow : g ^ p = 1 := by
    apply Equiv.Perm.pow_prime_eq_one_iff.2
    intro c hc
    rw [hcycle] at hc
    exact Multiset.eq_of_mem_replicate hc
  have hdvd : orderOf g ∣ p :=
    orderOf_dvd_of_pow_eq_one hpow
  exact
    (hp.eq_one_or_self_of_dvd (orderOf g) hdvd).resolve_left <| by
      rw [orderOf_eq_one_iff]
      intro hg
      subst g
      have hjzero : j = 0 := by
        simpa using (congrArg Multiset.card hcycle).symm
      exact hj.ne' hjzero

/-- The conjugacy classes which can contribute to an order-`p` Sylow
row in `S_n` are precisely among the canonical prime-cycle classes. -/
theorem primeOrderConjugacyClassRow_nonempty_implies_mem_primeCycleTypeClass_image
    {n p : ℕ} (hp : p.Prime)
    (P : Sylow p (Equiv.Perm (Fin n)))
    (C : ConjClasses (Equiv.Perm (Fin n)))
    (hC :
      (primeOrderConjugacyClassRow p C
        (P : Subgroup (Equiv.Perm (Fin n)))).Nonempty) :
    C ∈ (Finset.Icc 1 (n / p)).image (primeCycleTypeClass n p) := by
  classical
  obtain ⟨g, hg⟩ := hC
  rw [mem_primeOrderConjugacyClassRow_iff] at hg
  have hgOrderPrime : (orderOf g).Prime := by
    simpa only [hg.2.2] using hp
  obtain ⟨k, hk⟩ :=
    Equiv.Perm.cycleType_prime_order
      (σ := g) hgOrderPrime
  let j := k + 1
  have hjpos : 0 < j := Nat.succ_pos k
  have hcycle : g.cycleType = Multiset.replicate j p := by
    simpa [j, hg.2.2] using hk
  have hpj : p * j ≤ n := by
    have hsum := g.sum_cycleType_le
    rw [hcycle, Multiset.sum_replicate, nsmul_eq_mul,
      Nat.cast_id, Fintype.card_fin] at hsum
    simpa [Nat.mul_comm] using hsum
  have hjle : j ≤ n / p :=
    (Nat.le_div_iff_mul_le hp.pos).2 (by
      simpa [Nat.mul_comm] using hpj)
  have hjmem : j ∈ Finset.Icc 1 (n / p) :=
    Finset.mem_Icc.2 ⟨hjpos, hjle⟩
  refine Finset.mem_image.2 ⟨j, hjmem, ?_⟩
  have hgclass :
      ConjClasses.mk g = primeCycleTypeClass n p j := by
    rw [← ConjClasses.mem_carrier_iff_mk_eq,
      carrier_primeCycleTypeClass
        (isValidPrimeCycleType_of_prime hp hpj)]
    exact hcycle
  exact hgclass.symm.trans hg.1

/-- Outside the canonical prime-cycle classes, the order-`p` row is
empty. -/
theorem primeOrderConjugacyClassRow_eq_empty_of_not_mem_primeCycleTypeClass_image
    {n p : ℕ} (hp : p.Prime)
    (P : Sylow p (Equiv.Perm (Fin n)))
    (C : ConjClasses (Equiv.Perm (Fin n)))
    (hC :
      C ∉ (Finset.Icc 1 (n / p)).image (primeCycleTypeClass n p)) :
    primeOrderConjugacyClassRow p C
      (P : Subgroup (Equiv.Perm (Fin n))) = ∅ := by
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hnonempty
  exact hC
    (primeOrderConjugacyClassRow_nonempty_implies_mem_primeCycleTypeClass_image
      hp P C hnonempty)

/-- On a valid prime-cycle class, imposing order exactly `p` adds no
condition beyond lying in the class. -/
theorem ncard_primeOrderConjugacyClassRow_primeCycleTypeClass
    {n p j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hpj : p * j ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n))) :
    (primeOrderConjugacyClassRow p
      (primeCycleTypeClass n p j)
      (P : Subgroup (Equiv.Perm (Fin n)))).ncard =
        (primeCycleTypeSylowRow n p j P).card := by
  rw [card_primeCycleTypeSylowRow_eq_ncard_inter hp hpj]
  congr 1
  ext g
  rw [mem_primeOrderConjugacyClassRow_iff,
    Set.mem_inter_iff]
  constructor
  · rintro ⟨hgclass, hgP, _hgorder⟩
    exact
      ⟨ConjClasses.mem_carrier_iff_mk_eq.2 hgclass, hgP⟩
  · rintro ⟨hgclass, hgP⟩
    have hgmk :=
      ConjClasses.mem_carrier_iff_mk_eq.1 hgclass
    have hvalid := isValidPrimeCycleType_of_prime hp hpj
    have hgcycle : g.cycleType = Multiset.replicate j p := by
      rw [carrier_primeCycleTypeClass hvalid] at hgclass
      exact hgclass
    exact
      ⟨hgmk, hgP,
        orderOf_eq_prime_of_cycleType_eq_replicate hp hj hgcycle⟩

/-- The same class intersection, without the redundant order
condition, has the cycle-profile cardinal. -/
theorem ncard_primeCycleTypeClass_inter_sylow_eq_coeff
    {n p j : ℕ} (hp : p.Prime)
    (hpj : p * j ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n)))
    (hcoeff :
      (primeCycleTypeSylowRow n p j P).card =
        (sylowCycleProfile n p).coeff j) :
    ((primeCycleTypeClass n p j).carrier ∩
      ((P : Subgroup (Equiv.Perm (Fin n))) : Set _)).ncard =
        (sylowCycleProfile n p).coeff j := by
  rw [← card_primeCycleTypeSylowRow_eq_ncard_inter hp hpj]
  exact hcoeff

/-- Every Sylow `p`-subgroup of `S_n` has the cycle-profile
coefficients computed by the canonical base-`p` block construction. -/
theorem card_primeCycleTypeSylowRow_eq_coeff_of_prime
    {n p j : ℕ} (hp : p.Prime) (hpj : p * j ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n))) :
    (primeCycleTypeSylowRow n p j P).card =
      (sylowCycleProfile n p).coeff j := by
  let : Fact p.Prime := ⟨hp⟩
  let P₀ := basePBlockSylow n p hp
  obtain ⟨g, hg⟩ :=
    MulAction.exists_smul_eq
      (Equiv.Perm (Fin n)) P₀ P
  classical
  calc
    (primeCycleTypeSylowRow n p j P).card =
        ((primeCycleTypeClass n p j).carrier ∩
          ((P : Subgroup (Equiv.Perm (Fin n))) : Set _)).ncard := by
      exact card_primeCycleTypeSylowRow_eq_ncard_inter hp hpj P
    _ =
        ((primeCycleTypeClass n p j).carrier ∩
          ((P₀ : Subgroup (Equiv.Perm (Fin n))) : Set _)).ncard := by
      exact
        (ncard_conjClass_inter_sylow_eq_of_smul_eq
          P₀ P (primeCycleTypeClass n p j) g hg).symm
    _ = (primeCycleTypeSylowRow n p j P₀).card := by
      exact
        (card_primeCycleTypeSylowRow_eq_ncard_inter
          hp hpj P₀).symm
    _ = (sylowCycleProfile n p).coeff j :=
      card_primeCycleTypeSylowRow_eq_coeff n p j

/-- One canonical prime-cycle class contributes exactly its factorial
quotient times the square of the matching profile coefficient. -/
theorem mixedSylowPairQuadraticClassTerm_primeCycleTypeClass
    {n p j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hpj : p * j ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n))) :
    mixedSylowPairQuadraticClassTerm P P
        (primeCycleTypeClass n p j) =
      (n.factorial / primeCycleClassCard n p j) *
        ((sylowCycleProfile n p).coeff j) ^ 2 := by
  rw [mixedSylowPairQuadraticClassTerm,
    natCard_perm_fin,
    ncard_carrier_primeCycleTypeClass hp hj hpj,
    ncard_primeOrderConjugacyClassRow_primeCycleTypeClass
      hp hj hpj P,
    card_primeCycleTypeSylowRow_eq_coeff_of_prime hp hpj P,
    ncard_primeCycleTypeClass_inter_sylow_eq_coeff
      hp hpj P
      (card_primeCycleTypeSylowRow_eq_coeff_of_prime hp hpj P)]
  ring

/-- The integer-scaled same-row class sum is the finite sum of its
prime-cycle profile terms. -/
theorem sum_mixedSylowPairQuadraticClassTerm_eq_profile_sum
    {n p : ℕ} (hp : p.Prime)
    (P : Sylow p (Equiv.Perm (Fin n))) :
    (∑ C : ConjClasses (Equiv.Perm (Fin n)),
        mixedSylowPairQuadraticClassTerm P P C) =
      ∑ j ∈ Finset.Icc 1 (n / p),
        (n.factorial / primeCycleClassCard n p j) *
          ((sylowCycleProfile n p).coeff j) ^ 2 := by
  classical
  let classes :=
    (Finset.Icc 1 (n / p)).image (primeCycleTypeClass n p)
  calc
    (∑ C : ConjClasses (Equiv.Perm (Fin n)),
        mixedSylowPairQuadraticClassTerm P P C) =
        ∑ C ∈ classes,
          mixedSylowPairQuadraticClassTerm P P C := by
      symm
      apply Finset.sum_subset (Finset.subset_univ classes)
      intro C _hC hCnot
      have hrow :=
        primeOrderConjugacyClassRow_eq_empty_of_not_mem_primeCycleTypeClass_image
          hp P C (by simpa only [classes] using hCnot)
      simp [mixedSylowPairQuadraticClassTerm, hrow]
    _ =
        ∑ j ∈ Finset.Icc 1 (n / p),
          mixedSylowPairQuadraticClassTerm P P
            (primeCycleTypeClass n p j) := by
      rw [Finset.sum_image (primeCycleTypeClass_injective hp)]
    _ =
        ∑ j ∈ Finset.Icc 1 (n / p),
          (n.factorial / primeCycleClassCard n p j) *
            ((sylowCycleProfile n p).coeff j) ^ 2 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjpos := (Finset.mem_Icc.1 hj).1
      have hpj : p * j ≤ n := by
        simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le hp.pos).1
            (Finset.mem_Icc.1 hj).2
      exact
        mixedSylowPairQuadraticClassTerm_primeCycleTypeClass
          hp hjpos hpj P

private theorem primeCycleClassCard_pos
    {n p j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    0 < primeCycleClassCard n p j := by
  rw [← ncard_carrier_primeCycleTypeClass hp hj hpj]
  obtain ⟨g, hgclass, _hgcycle⟩ :=
    cycleType_rep_primeCycleTypeClass
      (isValidPrimeCycleType_of_prime hp hpj)
  exact Nat.pos_of_ne_zero <|
    Set.ncard_ne_zero_of_mem
      (ConjClasses.mem_carrier_iff_mk_eq.2 hgclass)

private theorem primeCycleClassCard_dvd_factorial
    {n p j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    primeCycleClassCard n p j ∣ n.factorial := by
  obtain ⟨g, hgclass, _hgcycle⟩ :=
    cycleType_rep_primeCycleTypeClass
      (isValidPrimeCycleType_of_prime hp hpj)
  have hcard :=
    conjugacyClass_ncard_mul_card_centralizer g
  rw [hgclass,
    ncard_carrier_primeCycleTypeClass hp hj hpj,
    natCard_perm_fin] at hcard
  exact ⟨Nat.card (Subgroup.centralizer {g}), hcard.symm⟩

private theorem normalized_primeCycle_profile_term
    {n p j r : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    ((((n.factorial / primeCycleClassCard n p j) * r ^ 2 :
        ℕ) : ℝ) / (n.factorial : ℝ)) =
      (r : ℝ) ^ 2 / (primeCycleClassCard n p j : ℝ) := by
  have hcpos := primeCycleClassCard_pos hp hj hpj
  have hcdvd := primeCycleClassCard_dvd_factorial hp hj hpj
  have hnpos : 0 < n.factorial := Nat.factorial_pos n
  have hcposReal :
      (0 : ℝ) < primeCycleClassCard n p j := by
    exact_mod_cast hcpos
  have hcneReal :
      (primeCycleClassCard n p j : ℝ) ≠ 0 :=
    ne_of_gt hcposReal
  have hnposReal : (0 : ℝ) < n.factorial := by
    exact_mod_cast hnpos
  have hnneReal : (n.factorial : ℝ) ≠ 0 :=
    ne_of_gt hnposReal
  rw [Nat.cast_mul, Nat.cast_pow,
    Nat.cast_div hcdvd hcneReal, div_eq_mul_inv]
  calc
    ((n.factorial : ℝ) *
          (primeCycleClassCard n p j : ℝ)⁻¹ *
          (r : ℝ) ^ 2) *
        (n.factorial : ℝ)⁻¹ =
        ((n.factorial : ℝ) * (n.factorial : ℝ)⁻¹) *
          ((r : ℝ) ^ 2 *
            (primeCycleClassCard n p j : ℝ)⁻¹) := by
      ring
    _ = (r : ℝ) ^ 2 *
        (primeCycleClassCard n p j : ℝ)⁻¹ := by
      rw [mul_inv_cancel₀ hnneReal, one_mul]

/-- Exact arithmetic formula for the normalized same-row quadratic
class sum of an arbitrary Sylow `p`-subgroup of `S_n`. -/
theorem normalizedSameRowSylowQuadraticCost_perm_eq_profile
    {n p : ℕ} (hp : p.Prime)
    (P : Sylow p (Equiv.Perm (Fin n))) :
    normalizedSameRowSylowQuadraticCost
        (Equiv.Perm (Fin n)) P =
      symmetricSylowProfileQuadraticCost n p := by
  unfold normalizedSameRowSylowQuadraticCost
  rw [sum_mixedSylowPairQuadraticClassTerm_eq_profile_sum hp P,
    natCard_perm_fin, symmetricSylowProfileQuadraticCost,
    Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos := (Finset.mem_Icc.1 hj).1
  have hpj : p * j ≤ n := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hp.pos).1
        (Finset.mem_Icc.1 hj).2
  simpa only [div_eq_mul_inv] using
    normalized_primeCycle_profile_term
      (r := (sylowCycleProfile n p).coeff j) hp hjpos hpj

/-- Canonical base-`p` block specialization of the exact normalized
quadratic formula. -/
theorem normalizedSameRowSylowQuadraticCost_basePBlockSylow_eq_profile
    (n p : ℕ) (hp : p.Prime) :
    normalizedSameRowSylowQuadraticCost
        (Equiv.Perm (Fin n)) (basePBlockSylow n p hp) =
      symmetricSylowProfileQuadraticCost n p :=
  normalizedSameRowSylowQuadraticCost_perm_eq_profile
    hp (basePBlockSylow n p hp)

/-! ## Restriction to classes meeting the alternating group -/

/-- A class of permutations with `j` transpositions meets `A_n`
exactly when `j` is even. -/
theorem ambientConjClassMeetsAlternating_primeCycleTypeClass_two_iff
    {n j : ℕ} (hj2 : 2 * j ≤ n) :
    ambientConjClassMeetsSubgroup
        (alternatingGroup (Fin n))
        (primeCycleTypeClass n 2 j) ↔
      Even j := by
  obtain ⟨g, hgclass, hgcycle⟩ :=
    cycleType_rep_primeCycleTypeClass
      (isValidPrimeCycleType_of_prime Nat.prime_two hj2)
  rw [← hgclass,
    ambientConjClassMeetsSubgroup_mk_iff,
    Equiv.Perm.mem_alternatingGroup,
    Equiv.Perm.sign_of_cycleType,
    hgcycle, Multiset.sum_replicate,
    Multiset.card_replicate, nsmul_eq_mul, Nat.cast_id,
    neg_one_pow_eq_one_iff_even (by norm_num : (-1 : ℤˣ) ≠ 1)]
  simp [parity_simps]

/-- Every nontrivial prime-cycle class for an odd prime consists of
even permutations. -/
theorem ambientConjClassMeetsAlternating_primeCycleTypeClass_of_odd
    {n p j : ℕ} (hp : p.Prime) (hpOdd : Odd p)
    (hpj : p * j ≤ n) :
    ambientConjClassMeetsSubgroup
        (alternatingGroup (Fin n))
        (primeCycleTypeClass n p j) := by
  obtain ⟨g, hgclass, hgcycle⟩ :=
    cycleType_rep_primeCycleTypeClass
      (isValidPrimeCycleType_of_prime hp hpj)
  rw [← hgclass,
    ambientConjClassMeetsSubgroup_mk_iff,
    Equiv.Perm.mem_alternatingGroup]
  have hcycle :
      g.cycleType =
        Multiset.replicate g.cycleType.card p := by
    rw [hgcycle, Multiset.card_replicate]
  rw [Equiv.Perm.sign_of_cycleType_eq_replicate
    hp.pos hcycle, ite_eq_left hpOdd]

/-- The integer-scaled symmetric-group class sum, restricted to classes
meeting `A_n`, is exactly the even-transposition part of the cycle
profile. -/
theorem sum_mixedSylowPairQuadraticClassTerm_meetingAlternating_two_eq_profile_sum
    {n : ℕ} (P : Sylow 2 (Equiv.Perm (Fin n))) :
    (∑ C : ConjClasses (Equiv.Perm (Fin n)),
        if ambientConjClassMeetsSubgroup
            (alternatingGroup (Fin n)) C then
          mixedSylowPairQuadraticClassTerm P P C
        else 0) =
      ∑ j ∈ Finset.Icc 1 (n / 2),
        if Even j then
          (n.factorial / primeCycleClassCard n 2 j) *
            ((sylowCycleProfile n 2).coeff j) ^ 2
        else 0 := by
  classical
  let classes :=
    (Finset.Icc 1 (n / 2)).image (primeCycleTypeClass n 2)
  let term : ConjClasses (Equiv.Perm (Fin n)) → ℕ :=
    fun C ↦
      if ambientConjClassMeetsSubgroup
          (alternatingGroup (Fin n)) C then
        mixedSylowPairQuadraticClassTerm P P C
      else 0
  calc
    (∑ C : ConjClasses (Equiv.Perm (Fin n)),
        if ambientConjClassMeetsSubgroup
            (alternatingGroup (Fin n)) C then
          mixedSylowPairQuadraticClassTerm P P C
        else 0) =
        ∑ C ∈ classes, term C := by
      change (∑ C : ConjClasses (Equiv.Perm (Fin n)), term C) =
        ∑ C ∈ classes, term C
      symm
      apply Finset.sum_subset (Finset.subset_univ classes)
      intro C _hC hCnot
      have hrow :=
        primeOrderConjugacyClassRow_eq_empty_of_not_mem_primeCycleTypeClass_image
          Nat.prime_two P C (by simpa only [classes] using hCnot)
      simp [term, mixedSylowPairQuadraticClassTerm, hrow]
    _ =
        ∑ j ∈ Finset.Icc 1 (n / 2),
          term (primeCycleTypeClass n 2 j) := by
      rw [Finset.sum_image
        (primeCycleTypeClass_injective Nat.prime_two)]
    _ =
        ∑ j ∈ Finset.Icc 1 (n / 2),
          if Even j then
            (n.factorial / primeCycleClassCard n 2 j) *
              ((sylowCycleProfile n 2).coeff j) ^ 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjpos := (Finset.mem_Icc.1 hj).1
      have h2j : 2 * j ≤ n := by
        simpa [Nat.mul_comm] using
          (Nat.le_div_iff_mul_le Nat.zero_lt_two).1
            (Finset.mem_Icc.1 hj).2
      dsimp only [term]
      rw [ambientConjClassMeetsAlternating_primeCycleTypeClass_two_iff
          h2j]
      by_cases heven : Even j
      · rw [ite_eq_left heven, ite_eq_left heven]
        exact
          mixedSylowPairQuadraticClassTerm_primeCycleTypeClass
            Nat.prime_two hjpos h2j P
      · rw [ite_eq_right heven, ite_eq_right heven]

/-- Exact restricted normalized formula for the Sylow `2` row of
`S_n`.  This is the profile consumed by the index-two transfer to
`A_n`. -/
theorem normalizedSameRowSylowQuadraticCostMeetingAlternating_perm_eq_profile
    {n : ℕ} (P : Sylow 2 (Equiv.Perm (Fin n))) :
    normalizedSameRowSylowQuadraticCostMeetingSubgroup
        (alternatingGroup (Fin n)) P =
      alternatingSylowProfileQuadraticCost n 2 := by
  unfold normalizedSameRowSylowQuadraticCostMeetingSubgroup
  rw [
    sum_mixedSylowPairQuadraticClassTerm_meetingAlternating_two_eq_profile_sum
      P,
    natCard_perm_fin,
    alternatingSylowProfileQuadraticCost, ite_eq_left rfl,
    Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have hjpos := (Finset.mem_Icc.1 hj).1
  have h2j : 2 * j ≤ n := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le Nat.zero_lt_two).1
        (Finset.mem_Icc.1 hj).2
  by_cases heven : Even j
  · simp only [heven, ite_true, Nat.cast_mul, Nat.cast_pow]
    simpa only [Nat.cast_mul, Nat.cast_pow, div_eq_mul_inv] using
      normalized_primeCycle_profile_term
        (r := (sylowCycleProfile n 2).coeff j)
        Nat.prime_two hjpos h2j
  · simp only [heven, ite_false, Nat.cast_zero, zero_mul]

end LisiSabatini
