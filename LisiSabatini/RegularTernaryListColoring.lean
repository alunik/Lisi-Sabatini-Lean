import LisiSabatini.RegularTernaryListColoringArithmetic
import Mathlib.GroupTheory.Perm.Centralizer

/-!
# Ternary list colourings for regular permutation groups

This is the parity-free counterpart of `OddRegularListColoring`.
At every block there are three locally admissible orbit colours.  For a
fixed top permutation, compatibility along one cycle is deterministic after
the value at a single block is chosen, so compatible assignments are
bounded by `3^(number of cycles)`.

Every nonidentity element of a regular top is fixed-point-free, hence has at
most half as many cycles as points.  The resulting union bound leaves a
choice which simultaneously distinguishes the top and avoids two prescribed
external orbits.  This is the finite combinatorial input required by an
even-top affine two-base propagation.
-/

noncomputable section

namespace LisiSabatini

universe uI uC

variable {I : Type uI} [Fintype I]

/-- Choices compatible with a deterministic relation along the directed
edges of a permutation. -/
def FiniteRelationAssignments
    (Colour : Type uC) [Fintype Colour]
    (sigma : Equiv.Perm I)
    (R : I → Colour → Colour → Prop) :=
  {epsilon : I → Colour //
    ∀ i, R i (epsilon (sigma.symm i)) (epsilon i)}

noncomputable instance finiteRelationAssignmentsFintype
    (Colour : Type uC) [Fintype Colour]
    (sigma : Equiv.Perm I)
    (R : I → Colour → Colour → Prop) :
    Fintype (FiniteRelationAssignments Colour sigma R) :=
  @Fintype.ofFinite _
    (Finite.of_injective Subtype.val Subtype.val_injective)

namespace FiniteRelationAssignments

/-- Restriction to one chosen point in every cycle is injective for a
functional edge relation. -/
theorem card_le_card_pow_cycleFactors
    (Colour : Type uC) [Fintype Colour]
    [DecidableEq I]
    (sigma : Equiv.Perm I)
    (R : I → Colour → Colour → Prop)
    (hfixed : ∀ i, sigma i ≠ i)
    (hfun : ∀ i x y z, R i x y → R i x z → y = z) :
    Fintype.card (FiniteRelationAssignments Colour sigma R) ≤
      Fintype.card Colour ^
        Fintype.card sigma.cycleFactorsFinset := by
  classical
  let a : sigma.Basis :=
    Classical.choice (Equiv.Perm.Basis.nonempty sigma)
  let restrictToBasis :
      FiniteRelationAssignments Colour sigma R →
        (sigma.cycleFactorsFinset → Colour) :=
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
    Fintype.card (FiniteRelationAssignments Colour sigma R) ≤
        Fintype.card (sigma.cycleFactorsFinset → Colour) :=
      Fintype.card_le_of_injective restrictToBasis hinjective
    _ = Fintype.card Colour ^
        Fintype.card sigma.cycleFactorsFinset := by
      simp

end FiniteRelationAssignments

/-- A fixed-point-free permutation has at most one cycle for every two
points. -/
private theorem card_cycleFactorsFinset_le_card_div_two
    [DecidableEq I]
    (sigma : Equiv.Perm I)
    (hfixed : ∀ i, sigma i ≠ i) :
    Fintype.card sigma.cycleFactorsFinset ≤
      Fintype.card I / 2 := by
  classical
  have hcycleLength : ∀ n ∈ sigma.cycleType, 2 ≤ n :=
    fun n hn ↦ Equiv.Perm.two_le_of_mem_cycleType hn
  have hsumLower :
      sigma.cycleType.card * 2 ≤ sigma.cycleType.sum := by
    have h := Multiset.card_nsmul_le_sum
      (s := sigma.cycleType) (a := 2) hcycleLength
    simpa [nsmul_eq_mul, Nat.mul_comm] using h
  have hsupport : sigma.support = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    exact Equiv.Perm.mem_support.mpr (hfixed i)
  have hsum : sigma.cycleType.sum = Fintype.card I := by
    rw [Equiv.Perm.sum_cycleType, hsupport, Finset.card_univ]
  have hcycleCard :
      Fintype.card sigma.cycleFactorsFinset =
        sigma.cycleType.card := by
    rw [Fintype.card_coe, Equiv.Perm.cycleType_def,
      Multiset.card_map, Finset.card_def]
  rw [hcycleCard]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  simpa [hsum] using hsumLower

/-- Three-colour deterministic list assignments and two external orbits
cannot exhaust all choices for a nontrivial regular top. -/
theorem exists_ternaryChoice_avoiding_deterministicTop_and_twoExternal
    (T : Subgroup (Equiv.Perm I))
    (R : T → I → Fin 3 → Fin 3 → Prop)
    (E : Fin 2 → T → I → Fin 3 → Prop)
    (hcard : Nat.card T = Fintype.card I)
    (hcardTwo : 2 ≤ Nat.card T)
    (hsemi : ∀ sigma : T, sigma ≠ 1 → ∀ i,
      (sigma.1 : Equiv.Perm I) i ≠ i)
    (hRfun : ∀ sigma i x y z,
      R sigma i x y → R sigma i x z → y = z)
    (hEfun : ∀ k sigma i x y,
      E k sigma i x → E k sigma i y → x = y) :
    ∃ epsilon : I → Fin 3,
      (∀ sigma : T, sigma ≠ 1 →
        ¬ ∀ i, R sigma i
          (epsilon ((sigma.1 : Equiv.Perm I).symm i))
          (epsilon i)) ∧
      (∀ k sigma, ¬ ∀ i, E k sigma i (epsilon i)) := by
  classical
  letI : Fintype T := Fintype.ofFinite T
  let Choices := I → Fin 3
  let nonidentity : Finset T :=
    Finset.univ.filter (fun sigma ↦ sigma ≠ 1)
  let topBad (sigma : T) : Finset Choices :=
    Finset.univ.filter (fun epsilon ↦
      ∀ i, R sigma i
        (epsilon ((sigma.1 : Equiv.Perm I).symm i))
        (epsilon i))
  let externalBad (z : Fin 2 × T) : Finset Choices :=
    Finset.univ.filter (fun epsilon ↦
      ∀ i, E z.1 z.2 i (epsilon i))
  have htopBad (sigma : T) (hsigma : sigma ≠ 1) :
      (topBad sigma).card ≤
        3 ^ (Fintype.card I / 2) := by
    have hcycles :
        Fintype.card
            (sigma.1 : Equiv.Perm I).cycleFactorsFinset ≤
          Fintype.card I / 2 :=
      card_cycleFactorsFinset_le_card_div_two
        (sigma.1 : Equiv.Perm I) (hsemi sigma hsigma)
    calc
      (topBad sigma).card =
          Fintype.card {epsilon : I → Fin 3 //
            ∀ i, R sigma i
              (epsilon ((sigma.1 : Equiv.Perm I).symm i))
              (epsilon i)} := by
        exact (Fintype.card_subtype _).symm
      _ = Fintype.card
          (FiniteRelationAssignments
            (Fin 3) (sigma.1 : Equiv.Perm I) (R sigma)) := by
        exact Fintype.card_congr (Equiv.refl _)
      _ ≤ 3 ^ Fintype.card
          (sigma.1 : Equiv.Perm I).cycleFactorsFinset := by
        simpa using
          FiniteRelationAssignments.card_le_card_pow_cycleFactors
            (Fin 3) (sigma.1 : Equiv.Perm I) (R sigma)
            (hsemi sigma hsigma) (hRfun sigma)
      _ ≤ 3 ^ (Fintype.card I / 2) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 3) hcycles
  have hexternalBad (z : Fin 2 × T) :
      (externalBad z).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro epsilon hepsilon delta hdelta
    simp only [externalBad, Finset.mem_filter, Finset.mem_univ,
      true_and] at hepsilon hdelta
    funext i
    exact hEfun z.1 z.2 i _ _
      (hepsilon i) (hdelta i)
  let topUnion : Finset Choices :=
    nonidentity.biUnion topBad
  let externalUnion : Finset Choices :=
    Finset.univ.biUnion externalBad
  let forbidden : Finset Choices :=
    topUnion ∪ externalUnion
  have hnonidentityCard :
      nonidentity.card = Nat.card T - 1 := by
    rw [show nonidentity =
        (Finset.univ : Finset T).erase 1 by
      simpa [nonidentity] using
        Finset.filter_ne' (Finset.univ : Finset T) 1]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1),
      Finset.card_univ, ← Nat.card_eq_fintype_card]
  have htopUnion :
      topUnion.card ≤
        (Nat.card T - 1) *
          3 ^ (Fintype.card I / 2) := by
    calc
      topUnion.card ≤
          ∑ sigma ∈ nonidentity,
            (topBad sigma).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _sigma ∈ nonidentity,
          3 ^ (Fintype.card I / 2) := by
        apply Finset.sum_le_sum
        intro sigma hsigma
        exact htopBad sigma
          (Finset.mem_filter.mp hsigma).2
      _ = (Nat.card T - 1) *
          3 ^ (Fintype.card I / 2) := by
        simp [hnonidentityCard]
  have hexternalUnion :
      externalUnion.card ≤ 2 * Nat.card T := by
    calc
      externalUnion.card ≤
          ∑ z ∈ (Finset.univ : Finset (Fin 2 × T)),
            (externalBad z).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _z ∈ (Finset.univ : Finset (Fin 2 × T)), 1 := by
        apply Finset.sum_le_sum
        intro z _hz
        exact hexternalBad z
      _ = 2 * Nat.card T := by
        simp [Nat.card_eq_fintype_card]
  have hbudget :
      (Nat.card T - 1) *
            3 ^ (Fintype.card I / 2) +
          2 * Nat.card T <
        3 ^ Fintype.card I := by
    rw [← hcard]
    exact
      regularTernaryListColoring_union_add_twoOrbits_lt_threePow
        (Nat.card T) hcardTwo
  have hforbiddenCard :
      forbidden.card < 3 ^ Fintype.card I := by
    apply lt_of_le_of_lt _ hbudget
    calc
      forbidden.card ≤
          topUnion.card + externalUnion.card :=
        Finset.card_union_le _ _
      _ ≤ (Nat.card T - 1) *
              3 ^ (Fintype.card I / 2) +
            2 * Nat.card T :=
        Nat.add_le_add htopUnion hexternalUnion
  have hunivCard :
      (Finset.univ : Finset Choices).card =
        3 ^ Fintype.card I := by
    simp [Choices]
  have hnotSubset :
      ¬(Finset.univ : Finset Choices) ⊆ forbidden := by
    intro hsubset
    have hle := Finset.card_le_card hsubset
    rw [hunivCard] at hle
    exact (not_le_of_gt hforbiddenCard) hle
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
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hsigma⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hrelation⟩
  · intro k sigma hexternal
    apply hepsilon
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    refine ⟨(k, sigma), Finset.mem_univ _, ?_⟩
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hexternal⟩

end LisiSabatini
