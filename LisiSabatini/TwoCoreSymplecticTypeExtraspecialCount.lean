module

public import LisiSabatini.TwoCoreSymplecticTypeMixedHeadCount
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Sign-free square counts in extraspecial two-groups

This file proves the last finite-group input in the mixed
central-product active-involution count.  The argument is intrinsic: the
square map on the central quotient is a nondegenerate quadratic form,
and its elementary Gauss-sum calculation is carried out directly on the
group.  No classification of extraspecial groups by central products is
used.
-/

@[expose] public section

noncomputable section

open scoped BigOperators commutatorElement

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The sign character of a group of order two. -/
def orderTwoSign
    {K : Type*} [Group K] (x : K) : ℤ := by
  classical
  exact if x = 1 then 1 else -1

private theorem orderTwoSign_one
    {K : Type*} [Group K] :
    orderTwoSign (1 : K) = 1 := by
  simp [orderTwoSign]

private theorem orderTwoSign_sq
    {K : Type*} [Group K] (x : K) :
    orderTwoSign x * orderTwoSign x = 1 := by
  by_cases hx : x = 1 <;> simp [orderTwoSign, hx]

/-- On a group of order two, the elementary sign is multiplicative. -/
private theorem orderTwoSign_mul
    {K : Type*} [Group K] [Finite K]
    (hcard : Nat.card K = 2) (x y : K) :
    orderTwoSign (x * y) =
      orderTwoSign x * orderTwoSign y := by
  by_cases hx : x = 1
  · subst x
    rw [one_mul, orderTwoSign_one, one_mul]
  by_cases hy : y = 1
  · subst y
    rw [mul_one, orderTwoSign_one, mul_one]
  have hxy : x = y := by
    obtain ⟨z, hzNe, hzUnique⟩ :=
      (Nat.card_eq_two_iff' (1 : K)).mp hcard
    exact (hzUnique x hx).trans (hzUnique y hy).symm
  have hySq : y ^ 2 = 1 := by
    have hpow : y ^ Nat.card K = 1 := pow_card_eq_one'
    simpa [hcard] using hpow
  have hmul : x * y = 1 := by
    rw [hxy, ← pow_two, hySq]
  simp [orderTwoSign, hx, hy, hmul]

namespace IsExtraspecial

variable {E : Type u} [Group E] [Finite E]

/-- The unique nonidentity element of the center of an extraspecial
two-group. -/
def centralInvolution
    (h : IsExtraspecial 2 E) : Subgroup.center E :=
  Classical.choose
    ((Nat.card_eq_two_iff' (1 : Subgroup.center E)).mp
      h.card_center)

theorem centralInvolution_ne_one
    (h : IsExtraspecial 2 E) :
    h.centralInvolution ≠ 1 :=
  (Classical.choose_spec
    ((Nat.card_eq_two_iff' (1 : Subgroup.center E)).mp
      h.card_center)).1

theorem eq_centralInvolution_of_ne_one
    (h : IsExtraspecial 2 E)
    (z : Subgroup.center E) (hz : z ≠ 1) :
    z = h.centralInvolution := by
  exact
    (Classical.choose_spec
      ((Nat.card_eq_two_iff' (1 : Subgroup.center E)).mp
        h.card_center)).2 z hz

theorem centralInvolution_sq
    (h : IsExtraspecial 2 E) :
    h.centralInvolution ^ 2 = 1 := by
  have hpow :
      h.centralInvolution ^
          Nat.card (Subgroup.center E) = 1 :=
    pow_card_eq_one'
  simpa [h.card_center] using hpow

/-- Every element of the derived subgroup has square one. -/
private theorem commutatorElement_sq
    (h : IsExtraspecial 2 E)
    (c : commutator E) :
    c ^ 2 = 1 := by
  have hpow : c ^ Nat.card (commutator E) = 1 :=
    pow_card_eq_one'
  have hcard : Nat.card (commutator E) = 2 := by
    rw [h.commutator_eq_center]
    exact h.card_center
  simpa [hcard] using hpow

/-- Squares are central in an extraspecial two-group. -/
theorem sq_mem_center
    (h : IsExtraspecial 2 E) (x : E) :
    x ^ 2 ∈ Subgroup.center E := by
  apply pow_mem_center_of_commutator_le_center
    (by rw [h.commutator_eq_center]) 2
  intro c
  exact congrArg Subtype.val (h.commutatorElement_sq c)

/-- Every square is either one or the unique central involution. -/
theorem square_dichotomy
    (h : IsExtraspecial 2 E) (x : E) :
    x ^ 2 = 1 ∨ x ^ 2 = h.centralInvolution.1 := by
  let z : Subgroup.center E := ⟨x ^ 2, h.sq_mem_center x⟩
  by_cases hz : z = 1
  · left
    exact congrArg Subtype.val hz
  · right
    exact congrArg Subtype.val
      (h.eq_centralInvolution_of_ne_one z hz)

/-- A commutator, as an element of the derived subgroup. -/
private def commutatorValue
    (x y : E) : commutator E :=
  ⟨⁅x, y⁆,
    Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

/-- A square, as an element of the center. -/
def squareValue
    (h : IsExtraspecial 2 E) (x : E) :
    Subgroup.center E :=
  ⟨x ^ 2, h.sq_mem_center x⟩

/-- The `{±1}`-valued square character. -/
def squareSign
    (h : IsExtraspecial 2 E) (x : E) : ℤ :=
  orderTwoSign (h.squareValue x)

/-- The `{±1}`-valued commutator character. -/
private def commutatorSign
    (x y : E) : ℤ :=
  orderTwoSign (commutatorValue x y)

private theorem card_commutator
    (h : IsExtraspecial 2 E) :
    Nat.card (commutator E) = 2 := by
  rw [h.commutator_eq_center]
  exact h.card_center

private theorem squareSign_sq
    (h : IsExtraspecial 2 E) (x : E) :
    h.squareSign x * h.squareSign x = 1 :=
  orderTwoSign_sq _

omit [Finite E] in
private theorem commutatorSign_sq
    (x y : E) :
    commutatorSign x y * commutatorSign x y = 1 :=
  orderTwoSign_sq _

private theorem commutatorSign_mul_left
    (h : IsExtraspecial 2 E) (x₁ x₂ y : E) :
    commutatorSign (x₁ * x₂) y =
      commutatorSign x₁ y *
        commutatorSign x₂ y := by
  have hvalue :
      commutatorValue (x₁ * x₂) y =
        commutatorValue x₂ y * commutatorValue x₁ y := by
    apply Subtype.ext
    exact commutatorElement_mul_left_of_mem_center x₁ x₂ y
      (by
        rw [← h.commutator_eq_center]
        exact (commutatorValue x₂ y).2)
  rw [commutatorSign, hvalue,
    orderTwoSign_mul h.card_commutator]
  exact mul_comm _ _

private theorem commutatorSign_mul_right
    (h : IsExtraspecial 2 E) (x y₁ y₂ : E) :
    commutatorSign x (y₁ * y₂) =
      commutatorSign x y₁ *
        commutatorSign x y₂ := by
  have hvalue :
      commutatorValue x (y₁ * y₂) =
        commutatorValue x y₁ * commutatorValue x y₂ := by
    apply Subtype.ext
    exact commutatorElement_mul_right_of_mem_center x y₁ y₂
      (by
        rw [← h.commutator_eq_center]
        exact (commutatorValue x y₂).2)
  change
    orderTwoSign (commutatorValue x (y₁ * y₂)) =
      orderTwoSign (commutatorValue x y₁) *
        orderTwoSign (commutatorValue x y₂)
  rw [hvalue, orderTwoSign_mul h.card_commutator]

omit [Finite E] in
private theorem commutatorSign_self
    (x : E) :
    commutatorSign x x = 1 := by
  simp [commutatorSign, commutatorValue, orderTwoSign]

/-- The class-two square identity, with the commutator interpreted in
the center. -/
private theorem squareValue_mul
    (h : IsExtraspecial 2 E) (x y : E) :
    h.squareValue (x * y) =
      h.squareValue x * h.squareValue y *
        ⟨⁅x, y⁆, by
          rw [← h.commutator_eq_center]
          exact (commutatorValue x y).2⟩ := by
  let c : E := ⁅x, y⁆
  have hcCenter : c ∈ Subgroup.center E := by
    rw [← h.commutator_eq_center]
    exact (commutatorValue x y).2
  have hcSq : c ^ 2 = 1 := by
    exact congrArg Subtype.val
      (h.commutatorElement_sq (commutatorValue x y))
  have hxy : x * y = c * y * x := by
    dsimp only [c]
    simp only [commutatorElement_def]
    group
  have hyx : y * x = c * x * y := by
    calc
      y * x = c ^ 2 * (y * x) := by rw [hcSq, one_mul]
      _ = c * (c * y * x) := by rw [pow_two]; group
      _ = c * (x * y) := by rw [← hxy]
      _ = c * x * y := by group
  apply Subtype.ext
  change (x * y) ^ 2 = x ^ 2 * y ^ 2 * c
  rw [pow_two]
  calc
    x * y * (x * y) = x * (y * x) * y := by group
    _ = x * (c * x * y) * y := by rw [hyx]
    _ =
        c * (x * x * (y * y)) := by
      have hcx :
          x * c = c * x :=
        Subgroup.mem_center_iff.mp hcCenter x
      calc
        x * (c * x * y) * y =
            (x * c) * x * y * y := by group
        _ = (c * x) * x * y * y := by rw [hcx]
        _ = c * (x * x * (y * y)) := by group
    _ = (x * x * (y * y)) * c :=
      (Subgroup.mem_center_iff.mp hcCenter (x * x * (y * y))).symm
    _ = x ^ 2 * y ^ 2 * c := by rw [pow_two, pow_two]

private theorem centerSign_commutatorValue
    (h : IsExtraspecial 2 E) (x y : E) :
    orderTwoSign
        (⟨⁅x, y⁆, by
          rw [← h.commutator_eq_center]
          exact (commutatorValue x y).2⟩ :
          Subgroup.center E) =
      commutatorSign x y := by
  change
    orderTwoSign
        (⟨⁅x, y⁆, _⟩ : Subgroup.center E) =
      orderTwoSign (commutatorValue x y)
  unfold orderTwoSign
  congr 1
  apply propext
  constructor
  · intro hc
    apply Subtype.ext
    exact congrArg
      (fun z : Subgroup.center E ↦ z.1) hc
  · intro hc
    apply Subtype.ext
    exact congrArg
      (fun z : commutator E ↦ z.1) hc

/-- Polarization of the square sign by the commutator sign. -/
private theorem squareSign_mul
    (h : IsExtraspecial 2 E) (x y : E) :
    h.squareSign (x * y) =
      h.squareSign x * h.squareSign y *
        commutatorSign x y := by
  change
    orderTwoSign (h.squareValue (x * y)) =
      orderTwoSign (h.squareValue x) *
        orderTwoSign (h.squareValue y) *
          commutatorSign x y
  rw [h.squareValue_mul,
    orderTwoSign_mul h.card_center,
    orderTwoSign_mul h.card_center,
    h.centerSign_commutatorValue]

/-- A central second argument gives the trivial commutator sign. -/
private theorem commutatorSign_eq_one_of_mem_center
    {F : Type*} [Group F]
    (x t : F) (ht : t ∈ Subgroup.center F) :
    commutatorSign x t = 1 := by
  have hcomm : ⁅x, t⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact Subgroup.mem_center_iff.mp ht x
  have hvalue : commutatorValue x t = 1 := by
    apply Subtype.ext
    exact hcomm
  rw [commutatorSign, hvalue, orderTwoSign_one]

/-- Orthogonality of the nondegenerate commutator characters. -/
private theorem sum_commutatorSign_left
    [Fintype E]
    (h : IsExtraspecial 2 E) (t : E) :
    (t ∈ Subgroup.center E →
        (∑ x : E, commutatorSign x t) =
          (Nat.card E : ℤ)) ∧
      (t ∉ Subgroup.center E →
        (∑ x : E, commutatorSign x t) = 0) := by
  classical
  constructor
  · intro ht
    simp_rw [commutatorSign_eq_one_of_mem_center _ t ht]
    simp [Nat.card_eq_fintype_card]
  · intro ht
    have hnotAll :
        ¬ ∀ a : E, a * t = t * a := by
      intro hcomm
      exact ht (Subgroup.mem_center_iff.mpr hcomm)
    push Not at hnotAll
    obtain ⟨a, ha⟩ := hnotAll
    have haSign : commutatorSign a t = -1 := by
      have hcomm : ⁅a, t⁆ ≠ 1 := by
        exact mt commutatorElement_eq_one_iff_mul_comm.mp ha
      have hvalue : commutatorValue a t ≠ 1 := by
        intro hv
        exact hcomm (congrArg Subtype.val hv)
      simp [commutatorSign, orderTwoSign, hvalue]
    have hflip (x : E) :
        commutatorSign (a * x) t =
          -commutatorSign x t := by
      rw [h.commutatorSign_mul_left, haSign]
      ring
    have htranslate :
        (∑ x : E, commutatorSign x t) =
          ∑ x : E, commutatorSign (a * x) t := by
      exact
        (Fintype.sum_equiv (Equiv.mulLeft a)
          (fun x : E ↦ commutatorSign (a * x) t)
          (fun x : E ↦ commutatorSign x t)
          (fun _ ↦ rfl)).symm
    have hneg :
        (∑ x : E, commutatorSign x t) =
          -(∑ x : E, commutatorSign x t) := by
      calc
        (∑ x : E, commutatorSign x t) =
            ∑ x : E, commutatorSign (a * x) t :=
          htranslate
        _ = ∑ x : E, -commutatorSign x t := by
          apply Fintype.sum_congr
          intro x
          exact hflip x
        _ = -(∑ x : E, commutatorSign x t) := by
          rw [Finset.sum_neg_distrib]
    linarith

/-- Central elements have square sign one. -/
private theorem squareSign_eq_one_of_mem_center
    (h : IsExtraspecial 2 E)
    (t : E) (ht : t ∈ Subgroup.center E) :
    h.squareSign t = 1 := by
  let z : Subgroup.center E := ⟨t, ht⟩
  have hzSq : z ^ 2 = 1 := by
    have hpow :
        z ^ Nat.card (Subgroup.center E) = 1 :=
      pow_card_eq_one'
    simpa [h.card_center] using hpow
  have htSq : t ^ 2 = 1 :=
    congrArg Subtype.val hzSq
  have hvalue : h.squareValue t = 1 := by
    apply Subtype.ext
    exact htSq
  rw [squareSign, hvalue, orderTwoSign_one]

/-- The polarized square identity, rearranged for the Gauss sum. -/
private theorem squareSign_mul_rearranged
    (h : IsExtraspecial 2 E) (x y : E) :
    h.squareSign x * h.squareSign y =
      h.squareSign (x * y) * commutatorSign x y := by
  have hpolar := h.squareSign_mul x y
  have hcommSq := commutatorSign_sq x y
  calc
    h.squareSign x * h.squareSign y =
        (h.squareSign x * h.squareSign y *
            commutatorSign x y) *
          commutatorSign x y := by
      rw [mul_assoc, hcommSq, mul_one]
    _ = h.squareSign (x * y) *
          commutatorSign x y := by rw [← hpolar]

/-- The direct group-level Gauss-sum identity for the extraspecial
square map. -/
theorem squareSign_gauss_sq
    [Fintype E]
    (h : IsExtraspecial 2 E) :
    (∑ x : E, h.squareSign x) *
        (∑ x : E, h.squareSign x) =
      2 * (Nat.card E : ℤ) := by
  classical
  calc
    (∑ x : E, h.squareSign x) *
          (∑ x : E, h.squareSign x) =
        ∑ x : E, ∑ y : E,
          h.squareSign x * h.squareSign y :=
      Fintype.sum_mul_sum _ _
    _ = ∑ x : E, ∑ y : E,
          h.squareSign (x * y) *
            commutatorSign x y := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_congr
      intro y
      exact h.squareSign_mul_rearranged x y
    _ = ∑ x : E, ∑ t : E,
          h.squareSign t *
            commutatorSign x t := by
      apply Fintype.sum_congr
      intro x
      apply Fintype.sum_equiv (Equiv.mulLeft x)
      intro y
      change
        h.squareSign (x * y) * commutatorSign x y =
          h.squareSign (x * y) *
            commutatorSign x (x * y)
      rw [h.commutatorSign_mul_right,
        commutatorSign_self, one_mul]
    _ = ∑ t : E, ∑ x : E,
          h.squareSign t *
            commutatorSign x t := by
      rw [Finset.sum_comm]
    _ = ∑ t : E,
          h.squareSign t *
            (∑ x : E, commutatorSign x t) := by
      apply Fintype.sum_congr
      intro t
      rw [Finset.mul_sum]
    _ = ∑ t : E,
          if t ∈ Subgroup.center E then
            h.squareSign t * (Nat.card E : ℤ)
          else 0 := by
      apply Fintype.sum_congr
      intro t
      by_cases ht : t ∈ Subgroup.center E
      · simp only [if_pos ht,
          (h.sum_commutatorSign_left t).1 ht]
      · simp only [if_neg ht,
          (h.sum_commutatorSign_left t).2 ht, mul_zero]
    _ = ∑ t ∈
          (Finset.univ.filter
            fun t : E ↦ t ∈ Subgroup.center E),
          h.squareSign t * (Nat.card E : ℤ) := by
      exact
        (Finset.sum_filter
          (s := Finset.univ)
          (fun t : E ↦ t ∈ Subgroup.center E)
          (fun t : E ↦
            h.squareSign t * (Nat.card E : ℤ))).symm
    _ = ∑ _t ∈
          (Finset.univ.filter
            fun t : E ↦ t ∈ Subgroup.center E),
          (Nat.card E : ℤ) := by
      apply Finset.sum_congr rfl
      intro t ht
      have htCenter : t ∈ Subgroup.center E := by
        simpa using ht
      rw [h.squareSign_eq_one_of_mem_center t htCenter,
        one_mul]
    _ = 2 * (Nat.card E : ℤ) := by
      have hfilter :
          ((Finset.univ.filter
            fun t : E ↦ t ∈ Subgroup.center E).card) = 2 := by
        rw [← Fintype.card_subtype]
        change Fintype.card (Subgroup.center E) = 2
        rw [← Nat.card_eq_fintype_card]
        exact h.card_center
      rw [Finset.sum_const, Finset.card_filter]
      simp [hfilter]

/-- The order of an extraspecial two-group is intrinsically twice a
nontrivial square.

The proof avoids classification.  The group-level Gauss sum above has
square `2 * |E|`.  Its evenness lets us divide the Gauss sum by two, and
the resulting absolute value is the required degree.  Degrees zero and
one would give a group of order zero or two; the latter is cyclic, in
contradiction with extraspecial noncommutativity. -/
theorem exists_degree_card_eq_two_mul_sq
    (h : IsExtraspecial 2 E) :
    ∃ e : ℕ, 2 ≤ e ∧ Nat.card E = 2 * e * e := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let S : ℤ := ∑ x : E, h.squareSign x
  have hSq :
      S * S = 2 * (Nat.card E : ℤ) := by
    simpa only [S] using h.squareSign_gauss_sq
  have hSqEven : Even (S * S) := by
    rw [hSq]
    exact even_two_mul _
  have hEven : Even S :=
    (Int.even_mul.mp hSqEven).elim id id
  obtain ⟨t, ht⟩ := hEven
  have hCardInt :
      (Nat.card E : ℤ) = 2 * t * t := by
    rw [ht] at hSq
    nlinarith
  have hCardNat :
      Nat.card E = 2 * t.natAbs * t.natAbs := by
    have := congrArg Int.natAbs hCardInt
    simpa [Int.natAbs_mul] using this
  have htAbsNeZero : t.natAbs ≠ 0 := by
    intro htZero
    rw [htZero] at hCardNat
    simp at hCardNat
  have htAbsNeOne : t.natAbs ≠ 1 := by
    intro htOne
    have hCardTwo : Nat.card E = 2 := by
      simpa [htOne] using hCardNat
    letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    letI : IsCyclic E := isCyclic_of_prime_card hCardTwo
    exact h.not_isMulCommutative ⟨IsCyclic.commutative⟩
  exact ⟨t.natAbs, by omega, hCardNat⟩

/-- The square-sign sum is the difference of the two square-fiber
cardinalities. -/
theorem sum_squareSign_eq_fiber_difference
    [Fintype E]
    (h : IsExtraspecial 2 E) :
    (∑ x : E, h.squareSign x) =
      (Nat.card (SquareFiber E 1) : ℤ) -
        Nat.card
          (SquareFiber E h.centralInvolution.1) := by
  classical
  let p : E → Prop := fun x ↦ x ^ 2 = 1
  have hnot (x : E) :
      ¬p x ↔ x ^ 2 = h.centralInvolution.1 := by
    constructor
    · intro hx
      rcases h.square_dichotomy x with hone | hcentral
      · exact False.elim (hx hone)
      · exact hcentral
    · intro hcentral hone
      apply h.centralInvolution_ne_one
      apply Subtype.ext
      exact hcentral.symm.trans hone
  have hsign (x : E) :
      h.squareSign x =
        if p x then 1 else -1 := by
    change
      orderTwoSign (h.squareValue x) =
        if p x then 1 else -1
    unfold orderTwoSign
    congr 1
    apply propext
    constructor
    · intro hx
      exact congrArg Subtype.val hx
    · intro hx
      apply Subtype.ext
      exact hx
  have hpoint (x : E) :
      (if p x then (1 : ℤ) else -1) =
        (if p x then 1 else 0) -
          (if ¬p x then 1 else 0) := by
    by_cases hx : p x <;> simp [hx]
  have hcardOne :
      (Finset.univ.filter p).card =
        Nat.card (SquareFiber E 1) := by
    calc
      (Finset.univ.filter p).card =
          Fintype.card {x : E // p x} :=
        (Fintype.card_subtype p).symm
      _ = Nat.card (SquareFiber E 1) :=
        Nat.card_eq_fintype_card.symm
  have hcardCentral :
      (Finset.univ.filter fun x : E ↦ ¬p x).card =
        Nat.card
          (SquareFiber E h.centralInvolution.1) := by
    have hfilter :
        (Finset.univ.filter fun x : E ↦ ¬p x) =
          Finset.univ.filter
            (fun x : E ↦
              x ^ 2 = h.centralInvolution.1) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnot x
    rw [hfilter]
    calc
      (Finset.univ.filter
          (fun x : E ↦
            x ^ 2 = h.centralInvolution.1)).card =
          Fintype.card
            {x : E //
              x ^ 2 = h.centralInvolution.1} :=
        (Fintype.card_subtype _).symm
      _ = Nat.card
          (SquareFiber E h.centralInvolution.1) :=
        Nat.card_eq_fintype_card.symm
  simp_rw [hsign, hpoint]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_boole, hcardOne, hcardCentral]

/-- The two square fibers partition an extraspecial two-group. -/
theorem card_squareFibers
    (h : IsExtraspecial 2 E) :
    Nat.card (SquareFiber E 1) +
        Nat.card
          (SquareFiber E h.centralInvolution.1) =
      Nat.card E := by
  classical
  letI : Fintype E := Fintype.ofFinite E
  let p : E → Prop := fun x ↦ x ^ 2 = 1
  have hnot (x : E) :
      ¬p x ↔ x ^ 2 = h.centralInvolution.1 := by
    constructor
    · intro hx
      rcases h.square_dichotomy x with hone | hcentral
      · exact False.elim (hx hone)
      · exact hcentral
    · intro hcentral hone
      apply h.centralInvolution_ne_one
      apply Subtype.ext
      exact hcentral.symm.trans hone
  have hcardOne :
      Nat.card (SquareFiber E 1) =
        (Finset.univ.filter p).card := by
    calc
      Nat.card (SquareFiber E 1) =
          Fintype.card {x : E // p x} :=
        Nat.card_eq_fintype_card
      _ = (Finset.univ.filter p).card :=
        Fintype.card_subtype p
  have hcardCentral :
      Nat.card
          (SquareFiber E h.centralInvolution.1) =
        (Finset.univ.filter fun x : E ↦ ¬p x).card := by
    calc
      Nat.card
          (SquareFiber E h.centralInvolution.1) =
          Fintype.card
            {x : E //
              x ^ 2 = h.centralInvolution.1} :=
        Nat.card_eq_fintype_card
      _ = (Finset.univ.filter
          (fun x : E ↦
            x ^ 2 = h.centralInvolution.1)).card :=
        Fintype.card_subtype _
      _ = (Finset.univ.filter fun x : E ↦ ¬p x).card := by
        congr 1
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact (hnot x).symm
  rw [hcardOne, hcardCentral,
    Finset.card_filter_add_card_filter_not]
  exact Nat.card_eq_fintype_card.symm

/-- The sign-free square count required by the mixed central-product
bookkeeping.  This is the intrinsic extraspecial quadratic-form count:
the two fibers have sizes `e² ± e`, although only the symmetric upper
bounds are recorded. -/
def extraspecialTwoSquareCountData
    (h : IsExtraspecial 2 E)
    (e : ℕ) (hcard : Nat.card E = 2 * e * e) :
    ExtraspecialTwoSquareCountData E e := by
  letI : Fintype E := Fintype.ofFinite E
  let A := Nat.card (SquareFiber E 1)
  let B :=
    Nat.card
      (SquareFiber E h.centralInvolution.1)
  have hsum : A + B = 2 * e * e := by
    calc
      A + B = Nat.card E := h.card_squareFibers
      _ = 2 * e * e := hcard
  have hgauss :
      ((A : ℤ) - B) * ((A : ℤ) - B) =
        2 * (2 * (e : ℤ) * e) := by
    have hgaussRaw := h.squareSign_gauss_sq
    rw [h.sum_squareSign_eq_fiber_difference] at hgaussRaw
    calc
      ((A : ℤ) - B) * ((A : ℤ) - B) =
          2 * (Nat.card E : ℤ) := by
        simpa only [A, B] using hgaussRaw
      _ = 2 * (2 * (e : ℤ) * e) := by
        rw [hcard]
        push_cast
        ring
  have heNonneg : (0 : ℤ) ≤ e := by positivity
  have hdiffUpper :
      (A : ℤ) - B ≤ 2 * e := by
    nlinarith
  have hdiffLower :
      -(2 * (e : ℤ)) ≤ (A : ℤ) - B := by
    nlinarith
  have hsumInt :
      (A : ℤ) + B = 2 * (e : ℤ) * e := by
    exact_mod_cast hsum
  have hAle :
      A ≤ e * e + e := by
    have hAleInt :
        (A : ℤ) ≤ (e : ℤ) * e + e := by
      linarith
    exact_mod_cast hAleInt
  have hBle :
      B ≤ e * e + e := by
    have hBleInt :
        (B : ℤ) ≤ (e : ℤ) * e + e := by
      linarith
    exact_mod_cast hBleInt
  exact {
    centralInvolution := h.centralInvolution
    centralInvolution_ne_one :=
      h.centralInvolution_ne_one
    centralInvolution_sq :=
      h.centralInvolution_sq
    square_dichotomy := h.square_dichotomy
    card_fibers := by
      simpa only [A, B] using hsum
    card_one_le := by
      simpa only [A] using hAle
    card_central_le := by
      simpa only [B] using hBle
  }

end IsExtraspecial

namespace BergerMixedCentralProductData

variable {r d : ℕ} [Fact r.Prime]
  (P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
  [Fintype P]

/-- The mixed active-involution count with both finite square-count
inputs discharged internally. -/
theorem active_card_le_countingEnvelope_of_extraspecialOrder
    (data : BergerMixedCentralProductData P)
    (e : ℕ)
    (hcard :
      Nat.card data.extraspecialPart = 2 * e * e) :
    (activePrimeOrderElements 2 P).card ≤
      data.head.countingEnvelope e := by
  exact data.active_card_le_countingEnvelope_of_extraSquareData
    P e (data.extraspecial.extraspecialTwoSquareCountData e hcard)

end BergerMixedCentralProductData

end LisiSabatini
