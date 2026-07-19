import LisiSabatini.OddRegularListColoringArithmetic
import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Binary list colourings for odd semiregular permutation groups

This file isolates the finite combinatorics behind the active-top case of
recursive imprimitive orbit avoidance.  At every block one has two locally
admissible orbit colours.  For a fixed top permutation, compatibility along
one cycle is deterministic after the value at a single block is chosen.
Consequently the compatible binary choices are bounded by two to the number
of cycles.

The statements are deliberately phrased for arbitrary deterministic edge
relations.  In the imprimitive application the relation says that two
chosen block values lie in the exact common-base fibre associated to a
fixed top permutation.
-/

noncomputable section

namespace LisiSabatini

universe uI

variable {I : Type uI} [Fintype I]

/-- Binary choices compatible with a deterministic relation along the
directed edges of a permutation. -/
def BinaryRelationAssignments (sigma : Equiv.Perm I)
    (R : I → Bool → Bool → Prop) :=
  {epsilon : I → Bool //
    ∀ i, R i (epsilon (sigma.symm i)) (epsilon i)}

noncomputable instance binaryRelationAssignmentsFintype
    (sigma : Equiv.Perm I) (R : I → Bool → Bool → Prop) :
    Fintype (BinaryRelationAssignments sigma R) :=
  @Fintype.ofFinite _
    (Finite.of_injective Subtype.val Subtype.val_injective)

namespace BinaryRelationAssignments

/-- Restriction to one chosen point in every cycle is injective for a
functional edge relation.  Fixed points are excluded so that the cycle
basis covers the whole permutation domain. -/
private theorem card_le_two_pow_cycleFactors
    [DecidableEq I]
    (sigma : Equiv.Perm I) (R : I → Bool → Bool → Prop)
    (hfixed : ∀ i, sigma i ≠ i)
    (hfun : ∀ i x y z, R i x y → R i x z → y = z) :
    Fintype.card (BinaryRelationAssignments sigma R) ≤
      2 ^ Fintype.card sigma.cycleFactorsFinset := by
  classical
  let a : sigma.Basis :=
    Classical.choice (Equiv.Perm.Basis.nonempty sigma)
  let restrictToBasis : BinaryRelationAssignments sigma R →
      (sigma.cycleFactorsFinset → Bool) :=
    fun epsilon c ↦ epsilon.1 (a c)
  have hinjective : Function.Injective restrictToBasis := by
    intro epsilon delta heq
    apply Subtype.ext
    funext i
    have hiSupport : i ∈ sigma.support :=
      Equiv.Perm.mem_support.mpr (hfixed i)
    have hiCycle : sigma.cycleOf i ∈ sigma.cycleFactorsFinset :=
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hiSupport
    let c : sigma.cycleFactorsFinset :=
      ⟨sigma.cycleOf i, hiCycle⟩
    have hsame : sigma.SameCycle (a c) i := a.sameCycle hiCycle
    obtain ⟨n, hn⟩ := hsame.exists_nat_pow_eq
    have hpow : ∀ m : ℕ,
        epsilon.1 ((sigma ^ m) (a c)) =
          delta.1 ((sigma ^ m) (a c)) := by
      intro m
      induction m with
      | zero =>
          simpa [restrictToBasis] using congrFun heq c
      | succ m ih =>
          let k : I := (sigma ^ m) (a c)
          have hepsilon := epsilon.2 (sigma k)
          have hdelta := delta.2 (sigma k)
          simp only [Equiv.symm_apply_apply] at hepsilon hdelta
          have hfirst : epsilon.1 k = delta.1 k := by
            simpa [k] using ih
          rw [hfirst] at hepsilon
          have hlast := hfun (sigma k) (delta.1 k)
            (epsilon.1 (sigma k)) (delta.1 (sigma k))
            hepsilon hdelta
          simpa [k, pow_succ'] using hlast
    rw [← hn]
    exact hpow n
  calc
    Fintype.card (BinaryRelationAssignments sigma R) ≤
        Fintype.card (sigma.cycleFactorsFinset → Bool) :=
      Fintype.card_le_of_injective restrictToBasis hinjective
    _ = 2 ^ Fintype.card sigma.cycleFactorsFinset := by
      simp

end BinaryRelationAssignments

/-! ## Cycle count for odd fixed-point-free permutations -/

/-- A fixed-point-free permutation of odd order has at most one cycle for
every three points. -/
private theorem card_cycleFactorsFinset_le_card_div_three
    [DecidableEq I]
    (sigma : Equiv.Perm I)
    (hfixed : ∀ i, sigma i ≠ i)
    (hodd : Odd (orderOf sigma)) :
    Fintype.card sigma.cycleFactorsFinset ≤ Fintype.card I / 3 := by
  classical
  have hcycleLength : ∀ n ∈ sigma.cycleType, 3 ≤ n := by
    intro n hn
    have htwo : 2 ≤ n := Equiv.Perm.two_le_of_mem_cycleType hn
    have hnodd : Odd n :=
      hodd.of_dvd_nat (Equiv.Perm.dvd_of_mem_cycleType hn)
    obtain ⟨k, hk⟩ := hnodd
    omega
  have hsumLower : sigma.cycleType.card * 3 ≤ sigma.cycleType.sum := by
    have h := Multiset.card_nsmul_le_sum
      (s := sigma.cycleType) (a := 3) hcycleLength
    simpa [nsmul_eq_mul, Nat.mul_comm] using h
  have hsupport : sigma.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact Equiv.Perm.mem_support.mpr (hfixed i)
  have hsum : sigma.cycleType.sum = Fintype.card I := by
    rw [Equiv.Perm.sum_cycleType, hsupport, Finset.card_univ]
  have hcycleCard :
      Fintype.card sigma.cycleFactorsFinset = sigma.cycleType.card := by
    rw [Fintype.card_coe, Equiv.Perm.cycleType_def,
      Multiset.card_map, Finset.card_def]
  rw [hcycleCard]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 3)).2
  simpa [hsum] using hsumLower

/-! ## A finite union bound for arbitrary two-element block lists -/

/-- Odd semiregular top permutations and one external orbit cannot exhaust
all binary list choices once the displayed sharp budget holds.

`R sigma i x y` is the compatibility relation along the `sigma`-edge into
`i`; functionality in `y` is the exact-fibre property.  `E sigma i y`
records compatibility of the choice `y` with a prescribed external vector
under top permutation `sigma`; it is pointwise functional because the two
entries of a block list represent distinct base-orbit colours. -/
theorem exists_binaryChoice_avoiding_deterministicTop_and_external
    (T : Subgroup (Equiv.Perm I))
    (R : T → I → Bool → Bool → Prop)
    (E : T → I → Bool → Prop)
    (hodd : Odd (Nat.card T))
    (hsemi : ∀ sigma : T, sigma ≠ 1 → ∀ i,
      (sigma.1 : Equiv.Perm I) i ≠ i)
    (hRfun : ∀ sigma i x y z,
      R sigma i x y → R sigma i x z → y = z)
    (hEfun : ∀ sigma i x y,
      E sigma i x → E sigma i y → x = y)
    (hbudget :
      (Nat.card T - 1) * 2 ^ (Fintype.card I / 3) + Nat.card T <
        2 ^ Fintype.card I) :
    ∃ epsilon : I → Bool,
      (∀ sigma : T, sigma ≠ 1 →
        ¬ ∀ i, R sigma i
          (epsilon ((sigma.1 : Equiv.Perm I).symm i)) (epsilon i)) ∧
      (∀ sigma : T, ¬ ∀ i, E sigma i (epsilon i)) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let Choices := I → Bool
  let nonidentity : Finset T := Finset.univ.filter (fun sigma ↦ sigma ≠ 1)
  let topBad (sigma : T) : Finset Choices :=
    Finset.univ.filter (fun epsilon ↦
      ∀ i, R sigma i
        (epsilon ((sigma.1 : Equiv.Perm I).symm i)) (epsilon i))
  let externalBad (sigma : T) : Finset Choices :=
    Finset.univ.filter (fun epsilon ↦
      ∀ i, E sigma i (epsilon i))
  have htopBad (sigma : T) (hsigma : sigma ≠ 1) :
      (topBad sigma).card ≤ 2 ^ (Fintype.card I / 3) := by
    have horderOdd : Odd (orderOf (sigma.1 : Equiv.Perm I)) := by
      have horderSub : Odd (orderOf sigma) :=
        hodd.of_dvd_nat (orderOf_dvd_natCard sigma)
      rwa [Subgroup.orderOf_coe]
    have hcycles :
        Fintype.card (sigma.1 : Equiv.Perm I).cycleFactorsFinset ≤
          Fintype.card I / 3 :=
      card_cycleFactorsFinset_le_card_div_three
        (sigma.1 : Equiv.Perm I) (hsemi sigma hsigma) horderOdd
    calc
      (topBad sigma).card =
          Fintype.card {epsilon : I → Bool //
            ∀ i, R sigma i
              (epsilon ((sigma.1 : Equiv.Perm I).symm i))
              (epsilon i)} := by
        exact (Fintype.card_subtype _).symm
      _ = Fintype.card (BinaryRelationAssignments
            (sigma.1 : Equiv.Perm I) (R sigma)) := by
        exact Fintype.card_congr (Equiv.refl _)
      _ ≤ 2 ^ Fintype.card
          (sigma.1 : Equiv.Perm I).cycleFactorsFinset :=
        BinaryRelationAssignments.card_le_two_pow_cycleFactors
          (sigma.1 : Equiv.Perm I) (R sigma)
          (hsemi sigma hsigma) (hRfun sigma)
      _ ≤ 2 ^ (Fintype.card I / 3) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) hcycles
  have hexternalBad (sigma : T) : (externalBad sigma).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro epsilon hepsilon delta hdelta
    simp only [externalBad, Finset.mem_filter, Finset.mem_univ,
      true_and] at hepsilon hdelta
    funext i
    exact hEfun sigma i _ _ (hepsilon i) (hdelta i)
  let topUnion : Finset Choices := nonidentity.biUnion topBad
  let externalUnion : Finset Choices := Finset.univ.biUnion externalBad
  let forbidden : Finset Choices := topUnion ∪ externalUnion
  have hnonidentityCard : nonidentity.card = Nat.card T - 1 := by
    rw [show nonidentity = (Finset.univ : Finset T).erase 1 by
      simpa [nonidentity] using
        Finset.filter_ne' (Finset.univ : Finset T) 1]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1),
      Finset.card_univ, ← Nat.card_eq_fintype_card]
  have htopUnion :
      topUnion.card ≤
        (Nat.card T - 1) * 2 ^ (Fintype.card I / 3) := by
    calc
      topUnion.card ≤ ∑ sigma ∈ nonidentity, (topBad sigma).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _sigma ∈ nonidentity,
          2 ^ (Fintype.card I / 3) := by
        apply Finset.sum_le_sum
        intro sigma hsigma
        exact htopBad sigma (Finset.mem_filter.mp hsigma).2
      _ = (Nat.card T - 1) * 2 ^ (Fintype.card I / 3) := by
        simp [hnonidentityCard]
  have hexternalUnion : externalUnion.card ≤ Nat.card T := by
    calc
      externalUnion.card ≤
          ∑ sigma ∈ (Finset.univ : Finset T),
            (externalBad sigma).card := Finset.card_biUnion_le
      _ ≤ ∑ _sigma ∈ (Finset.univ : Finset T), 1 := by
        apply Finset.sum_le_sum
        intro sigma _hsigma
        exact hexternalBad sigma
      _ = Nat.card T := by
        simp [Nat.card_eq_fintype_card]
  have hforbiddenCard : forbidden.card < 2 ^ Fintype.card I := by
    apply lt_of_le_of_lt _ hbudget
    calc
      forbidden.card ≤ topUnion.card + externalUnion.card :=
        Finset.card_union_le _ _
      _ ≤ (Nat.card T - 1) * 2 ^ (Fintype.card I / 3) +
          Nat.card T := Nat.add_le_add htopUnion hexternalUnion
  have hunivCard : (Finset.univ : Finset Choices).card =
      2 ^ Fintype.card I := by
    simp [Choices]
  have hnotSubset :
      ¬ (Finset.univ : Finset Choices) ⊆ forbidden := by
    intro hsubset
    have := Finset.card_le_card hsubset
    rw [hunivCard] at this
    exact (not_le_of_gt hforbiddenCard) this
  obtain ⟨epsilon, hepsilonMem⟩ :=
    Finset.sdiff_nonempty.mpr hnotSubset
  have ⟨_hepsilonUniv, hepsilon⟩ :=
    Finset.mem_sdiff.mp hepsilonMem
  refine ⟨epsilon, ?_, ?_⟩
  · intro sigma hsigma hrelation
    apply hepsilon
    apply Finset.mem_union_left
    apply Finset.mem_biUnion.mpr
    refine ⟨sigma, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsigma⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrelation⟩
  · intro sigma hexternal
    apply hepsilon
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨sigma, Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hexternal⟩

/-- Regular odd-top specialization of the union theorem.  Equality of the
top and block cardinalities turns the arithmetic budget into the universal
odd regular-list inequality. -/
theorem exists_binaryChoice_avoiding_regularOddTop_and_external
    (T : Subgroup (Equiv.Perm I))
    (R : T → I → Bool → Bool → Prop)
    (E : T → I → Bool → Prop)
    (hcard : Nat.card T = Fintype.card I)
    (hodd : Odd (Nat.card T))
    (hthree : 3 ≤ Nat.card T)
    (hsemi : ∀ sigma : T, sigma ≠ 1 → ∀ i,
      (sigma.1 : Equiv.Perm I) i ≠ i)
    (hRfun : ∀ sigma i x y z,
      R sigma i x y → R sigma i x z → y = z)
    (hEfun : ∀ sigma i x y,
      E sigma i x → E sigma i y → x = y) :
    ∃ epsilon : I → Bool,
      (∀ sigma : T, sigma ≠ 1 →
        ¬ ∀ i, R sigma i
          (epsilon ((sigma.1 : Equiv.Perm I).symm i)) (epsilon i)) ∧
      (∀ sigma : T, ¬ ∀ i, E sigma i (epsilon i)) := by
  apply exists_binaryChoice_avoiding_deterministicTop_and_external
    T R E hodd hsemi hRfun hEfun
  rw [hcard]
  exact oddRegularListColoring_union_add_orbit_lt_twoPow
    (Fintype.card I) (by simpa [hcard] using hodd)
    (by simpa [hcard] using hthree)

end LisiSabatini
