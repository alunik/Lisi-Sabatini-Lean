import LisiSabatini.AffineTwoBaseTranslates
import LisiSabatini.ActiveFixedSpaceSpectrum
import LisiSabatini.CyclicCenterOperatorFixedSpaceRowCore
import LisiSabatini.ExtraspecialFamilyArithmeticCore

/-!
# Direct pair-spectrum bounds for affine two-base loci

The ordinary estimate

`|Bad₂(A)| ≤ |Nonregular(A)|²`

first takes a union of fixed spaces and then squares the resulting bound.
That repeats all cross terms between different group elements.  For the
affine two-base problem the sharper order is to take, for each active
element, the square of its own fixed space and only then form the union.
This gives the direct rectangle envelope

`|Bad₂(A)| ≤ 1 + (# active elements) * (c² - 1)`

when every active element fixes at most `c` vectors.

The second part records arithmetic estimates for the odd extraspecial rows
in characteristic two.  It deliberately makes no assertion about a
noncommuting normal `2`-core.
-/

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI

/-! ## The direct rectangle envelope -/

/-- The nonzero pairs fixed diagonally by one linear automorphism. -/
def nonzeroFixedPairSet
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    (g : LinearMap.GeneralLinearGroup R V) : Set (V × V) :=
  (fixedVectorSet g ×ˢ fixedVectorSet g) \ {(0, 0)}

/-- Every untranslated bad pair is either zero or is fixed by one
nonidentity element in both coordinates. -/
theorem affineTwoBaseBadSet_zero_subset_fixedPairSpectrum
    {r : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    affineTwoBaseBadSet A 0 0 ⊆
      {(0, 0)} ∪
        ⋃ g : {g : A // g ≠ 1}, nonzeroFixedPairSet g.1.1 := by
  intro z hz
  by_cases hz0 : z = (0, 0)
  · subst z
    simp
  · obtain ⟨g, hg⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hz
    have hgA : (g.1 : A) ≠ 1 := by
      intro hgone
      apply hg
      exact Subtype.ext hgone
    apply Set.mem_union_right
    apply Set.mem_iUnion.mpr
    refine ⟨⟨g.1, hgA⟩, ?_⟩
    rw [nonzeroFixedPairSet]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_fixedVectorSet]
      simpa using MulAction.mem_stabilizer_iff.mp g.2.1
    · rw [mem_fixedVectorSet]
      simpa using MulAction.mem_stabilizer_iff.mp g.2.2
    · exact hz0

/-- Union bound for the direct pair-spectrum envelope, with the zero pair
counted only once. -/
theorem ncard_affineTwoBaseBadSet_zero_le_one_add_sum_fixedPair
    {r : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Fintype A] :
    (affineTwoBaseBadSet A 0 0).ncard ≤
      1 + ∑ g ∈ nonidentityElements A,
        (nonzeroFixedPairSet g.1).ncard := by
  classical
  letI : Fintype {g : A // g ≠ 1} := Fintype.ofFinite _
  calc
    (affineTwoBaseBadSet A 0 0).ncard ≤
        ({(0, 0)} ∪
          ⋃ g : {g : A // g ≠ 1},
            nonzeroFixedPairSet g.1.1).ncard :=
      Set.ncard_le_ncard
        (affineTwoBaseBadSet_zero_subset_fixedPairSpectrum A)
        (Set.toFinite _)
    _ ≤ ({(0, 0)} : Set (V × V)).ncard +
        (⋃ g : {g : A // g ≠ 1},
          nonzeroFixedPairSet g.1.1).ncard := by
      exact Set.ncard_union_le _ _
    _ ≤ 1 + ∑ g : {g : A // g ≠ 1},
          (nonzeroFixedPairSet g.1.1).ncard := by
      simp only [Set.ncard_singleton]
      exact Nat.add_le_add_left (Set.ncard_iUnion_le_of_fintype _) 1
    _ = 1 + ∑ g ∈ nonidentityElements A,
          (nonzeroFixedPairSet g.1).ncard := by
      congr 1
      rw [nonidentityElements, ← Finset.filter_ne',
        ← Finset.sum_subtype_eq_sum_filter]
      simp

/-- A nonzero diagonal fixed rectangle has `|Fix(g)|² - 1` points. -/
theorem ncard_nonzeroFixedPairSet
    {R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
    [Finite V]
    (g : LinearMap.GeneralLinearGroup R V) :
    (nonzeroFixedPairSet g).ncard =
      (fixedVectorSet g).ncard * (fixedVectorSet g).ncard - 1 := by
  rw [nonzeroFixedPairSet,
    Set.ncard_diff_singleton_of_mem]
  · rw [Set.ncard_prod]
  · simp [fixedVectorSet]

/-- Direct rectangle-envelope estimate.  This is the abstract counting
lemma behind the odd extraspecial pair-spectrum term

`1 + (q^(2n+1)-1) * (r^(2(d/q))-1)`.
-/
theorem ncard_affineTwoBaseBadSet_zero_le_one_add_active_mul_fixed_sq
    {r : ℕ} {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Fintype A] (a c : ℕ)
    (hactive : (nonzeroFixingElements A).card ≤ a)
    (hfixed : ∀ g ∈ nonzeroFixingElements A,
      (fixedVectorSet g.1).ncard ≤ c) :
    (affineTwoBaseBadSet A 0 0).ncard ≤
      1 + a * (c * c - 1) := by
  classical
  have hsum :
      (∑ g ∈ nonidentityElements A,
          (nonzeroFixedPairSet g.1).ncard) =
        ∑ g ∈ nonzeroFixingElements A,
          (nonzeroFixedPairSet g.1).ncard := by
    rw [nonzeroFixingElements]
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro g hg hfiltered
    have hnot :
        ¬(nonzeroFixedVectorSet g.1).Nonempty := by
      intro hne
      exact hfiltered (Finset.mem_filter.mpr ⟨hg, hne⟩)
    have hfix : fixedVectorSet g.1 = {0} := by
      ext v
      constructor
      · intro hv
        by_contra hv0
        exact hnot
          ⟨v, (mem_nonzeroFixedVectorSet g.1 v).2 ⟨hv, hv0⟩⟩
      · intro hv
        have hv0 : v = 0 := by simpa using hv
        subst v
        simp [fixedVectorSet]
    simp [nonzeroFixedPairSet, hfix]
  calc
    (affineTwoBaseBadSet A 0 0).ncard ≤
        1 + ∑ g ∈ nonidentityElements A,
          (nonzeroFixedPairSet g.1).ncard :=
      ncard_affineTwoBaseBadSet_zero_le_one_add_sum_fixedPair A
    _ = 1 + ∑ g ∈ nonzeroFixingElements A,
          (nonzeroFixedPairSet g.1).ncard := by rw [hsum]
    _ ≤ 1 + (nonzeroFixingElements A).card * (c * c - 1) := by
      apply Nat.add_le_add_left
      calc
        (∑ g ∈ nonzeroFixingElements A,
            (nonzeroFixedPairSet g.1).ncard) ≤
            ∑ _g ∈ nonzeroFixingElements A, (c * c - 1) := by
          apply Finset.sum_le_sum
          intro g hg
          rw [ncard_nonzeroFixedPairSet]
          exact Nat.sub_le_sub_right
            (Nat.mul_le_mul (hfixed g hg) (hfixed g hg)) 1
        _ = (nonzeroFixingElements A).card * (c * c - 1) := by
          rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ ≤ 1 + a * (c * c - 1) :=
      Nat.add_le_add_left
        (Nat.mul_le_mul_right (c * c - 1) hactive) 1

/-- Exact direct pair-spectrum row for an odd cyclic-center class-two
group whose center acts fixed-point-freely.  In contrast with squaring the
ordinary spectrum bound, the active-element factor occurs only once. -/
theorem ncard_affineTwoBaseBadSet_zero_le_cyclicCenter_pairSpectrum
    {r d q : ℕ} [Fact r.Prime] [NeZero r]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (C : CenterFixedPointFreeAction r d P) :
    (affineTwoBaseBadSet P 0 0).ncard ≤
      1 + (q ^ (2 * hP.cyclicCenterStructuralRank + 1) - 1) *
        (r ^ (2 * (d / q)) - 1) := by
  letI : Fintype P := Fintype.ofFinite P
  have hfixed :
      ∀ g ∈ nonzeroFixingElements P,
        (fixedVectorSet g.1).ncard ≤ r ^ (d / q) := by
    intro g hg
    have hnz := C.active_fixed_le_of_cyclicCenterClassTwo hP g hg
    rw [ncard_nonzeroFixedVectorSet] at hnz
    have hcardPos : 0 < (fixedVectorSet g.1).ncard := by
      rw [Set.ncard_pos]
      exact ⟨0, by simp [fixedVectorSet]⟩
    have hpowPos : 0 < r ^ (d / q) :=
      pow_pos (Fact.out : Nat.Prime r).pos _
    omega
  have hraw :=
    ncard_affineTwoBaseBadSet_zero_le_one_add_active_mul_fixed_sq
      P
      (q ^ (2 * hP.cyclicCenterStructuralRank + 1) - 1)
      (r ^ (d / q))
      (C.card_nonzeroFixingElements_le_cyclicCenterStructuralRank_bound hP)
      hfixed
  have hsquare :
      r ^ (d / q) * r ^ (d / q) = r ^ (2 * (d / q)) := by
    rw [← pow_add]
    congr 1
    omega
  simpa only [hsquare] using hraw

/-! ## One odd extraspecial row in characteristic two -/

/-- If an odd prime divides `2^a - 1`, then squaring the field-size block
gives the lower bound used by the usual extraspecial arithmetic. -/
theorem two_mul_prime_add_one_le_four_pow_of_dvd_two_pow_sub_one
    {p a : ℕ}
    (hp : Nat.Prime p) (hpTwo : p ≠ 2)
    (ha : 0 < a) (hdiv : p ∣ 2 ^ a - 1) :
    2 * p + 1 ≤ 4 ^ a := by
  have htwoPow : 1 < 2 ^ a := one_lt_pow₀ (by norm_num) ha.ne'
  obtain ⟨c, hc⟩ := hdiv
  have hcPos : 0 < c := by
    by_contra hc0
    have hcZero : c = 0 := by omega
    rw [hcZero, mul_zero] at hc
    omega
  have hpAddOne : p + 1 ≤ 2 ^ a := by
    have hpLe : p ≤ 2 ^ a - 1 := by
      rw [hc]
      exact Nat.le_mul_of_pos_right p hcPos
    omega
  have hpThree : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hpTwo
    have := hp.two_le
    omega
  calc
    2 * p + 1 ≤ (p + 1) * (p + 1) := by nlinarith
    _ ≤ (2 ^ a) * (2 ^ a) :=
      Nat.mul_le_mul hpAddOne hpAddOne
    _ = 4 ^ a := by
      rw [← mul_pow]
      norm_num

/-- Twice the direct pair-spectrum budget of one admissible odd
extraspecial row in characteristic two is smaller than the doubled
module.  Writing the doubled field block as `4^(d/p)` makes this the same
one-row arithmetic shape as the odd-characteristic estimate. -/
theorem two_mul_odd_extraspecial_pairSpectrum_budget_lt_four
    {p n a b d : ℕ}
    (hp : Nat.Prime p) (hpTwo : p ≠ 2)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hdiv : p ∣ 2 ^ a - 1)
    (hd : d = a * p ^ n * b) :
    2 * (1 + (p ^ (2 * n + 1) - 1) *
      (4 ^ (d / p) - 1)) < 4 ^ d := by
  subst d
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let e := a * p ^ k * b
  let x := 4 ^ e
  let q := p ^ (2 * (k + 1) + 1)
  have hdExp : a * p ^ (k + 1) * b = e * p := by
    dsimp [e]
    rw [pow_succ]
    ring
  have hquot : (a * p ^ (k + 1) * b) / p = e := by
    rw [hdExp]
    exact Nat.mul_div_cancel e hp.pos
  have htop : 4 ^ (a * p ^ (k + 1) * b) = x ^ p := by
    rw [hdExp, pow_mul]
  have hbase : 2 * p + 1 ≤ 4 ^ a :=
    two_mul_prime_add_one_le_four_pow_of_dvd_two_pow_sub_one
      hp hpTwo ha hdiv
  have hxEq : x = (4 ^ a) ^ (p ^ k * b) := by
    dsimp [x, e]
    rw [show a * p ^ k * b = a * (p ^ k * b) by ring, pow_mul]
  have hmultPos : 0 < p ^ k * b :=
    Nat.mul_pos (pow_pos hp.pos _) hb
  have hxLower : (2 * p + 1) ^ (p ^ k * b) ≤ x := by
    rw [hxEq]
    exact Nat.pow_le_pow_left hbase _
  have hpThree : 3 ≤ p := by
    obtain ⟨j, hj⟩ := hp.odd_of_ne_two hpTwo
    have := hp.two_le
    omega
  have hxSeven : 7 ≤ x := by
    have hbaseSeven : 7 ≤ 2 * p + 1 := by omega
    have hfirst : 2 * p + 1 ≤ (2 * p + 1) ^ (p ^ k * b) := by
      calc
        2 * p + 1 = (2 * p + 1) ^ 1 := by simp
        _ ≤ (2 * p + 1) ^ (p ^ k * b) :=
          Nat.pow_le_pow_right (by omega) hmultPos
    exact hbaseSeven.trans (hfirst.trans hxLower)
  rw [hquot, htop]
  change 2 * (1 + (q - 1) * (x - 1)) < x ^ p
  by_cases hsmall : p = 3 ∧ k = 0
  · rcases hsmall with ⟨rfl, rfl⟩
    norm_num only [q, pow_one]
    by_cases hxEqSeven : x = 7
    · rw [hxEqSeven]
      norm_num
    · have hxEight : 8 ≤ x := by omega
      have hsq : 52 ≤ x * x := by nlinarith
      calc
        2 * (1 + 26 * (x - 1)) < 52 * x := by omega
        _ ≤ (x * x) * x := Nat.mul_le_mul_right x hsq
        _ = x ^ 3 := by ring
  · have horder : q < x ^ (p - 2) := by
      by_cases hpThreeEq : p = 3
      · subst p
        have hkOne : 1 ≤ k := by omega
        have hmin :
            3 ^ (2 * (k + 1) + 1) <
              7 ^ (3 ^ k * b) :=
          three_extraspecial_order_lt_minimalBlock (by omega) hb
        have hscale : 7 ^ (3 ^ k * b) ≤ x := by
          simpa using hxLower
        simpa [q] using hmin.trans_le hscale
      · have hpFive : 5 ≤ p := by
          obtain ⟨j, hj⟩ := hp.odd_of_ne_two hpTwo
          have := hp.two_le
          omega
        have hmin :
            p ^ (2 * (k + 1) + 1) <
              ((2 * p + 1) ^ (p ^ k * b)) ^ (p - 2) :=
          extraspecial_order_lt_minimalBlock_pow_sub_two
            hpFive (by omega) hb
        exact hmin.trans_le (Nat.pow_le_pow_left hxLower _)
    have hxOne : 1 ≤ x := by omega
    have hqOne : 1 < q := by
      dsimp [q]
      exact one_lt_pow₀ hp.one_lt (by omega)
    have hbad : 1 + (q - 1) * (x - 1) ≤ q * x := by
      have hqSub : 1 ≤ q - 1 := by omega
      calc
        1 + (q - 1) * (x - 1) =
            (q - 1) * (x - 1) + 1 := by omega
        _ ≤ (q - 1) * (x - 1) + (q - 1) :=
          Nat.add_le_add_left hqSub _
        _ = (q - 1) * ((x - 1) + 1) := by
          rw [mul_add, mul_one]
        _ = (q - 1) * x := by rw [Nat.sub_add_cancel hxOne]
        _ ≤ q * x := Nat.mul_le_mul_right x (Nat.sub_le q 1)
    have hxPos : 0 < x := by omega
    calc
      2 * (1 + (q - 1) * (x - 1)) ≤ 2 * (q * x) :=
        Nat.mul_le_mul_left 2 hbad
      _ < 2 * (x ^ (p - 2) * x) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right horder hxPos) (by norm_num)
      _ ≤ x * (x ^ (p - 2) * x) :=
        Nat.mul_le_mul_right _ (by omega)
      _ = x ^ p := by
        rw [show x * (x ^ (p - 2) * x) = x ^ (p - 2) * x ^ 2 by ring,
          ← pow_add]
        congr 1
        omega

/-- Characteristic-two form of the one-row pair-spectrum estimate. -/
theorem two_mul_odd_extraspecial_pairSpectrum_budget_lt
    {p n a b d : ℕ}
    (hp : Nat.Prime p) (hpTwo : p ≠ 2)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hdiv : p ∣ 2 ^ a - 1)
    (hd : d = a * p ^ n * b) :
    2 * (1 + (p ^ (2 * n + 1) - 1) *
      (2 ^ (2 * (d / p)) - 1)) < 2 ^ (2 * d) := by
  have h :=
    two_mul_odd_extraspecial_pairSpectrum_budget_lt_four
      hp hpTwo hn ha hb hdiv hd
  simpa [pow_mul] using h

/-! ## A finite odd-prime family in characteristic two -/

/-- The order of an odd extraspecial row is bounded by a power of the
squared binary field block. -/
theorem odd_extraspecial_order_le_four_pow_primePower
    {p n : ℕ}
    (hp : Nat.Prime p) (hpTwo : p ≠ 2) (hn : 0 < n) :
    p ^ (2 * n + 1) ≤ 4 ^ (p ^ n) := by
  exact
    (extraspecial_order_le_field_pow_primePower
      (by norm_num : Nat.Prime 3) hp (by norm_num) hpTwo hn).trans
      (Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) _)

/-- The complete direct pair-spectrum budget of a distinctly
prime-labelled odd extraspecial family in characteristic two occupies
strictly less than half of the doubled module.

This is the characteristic-two counterpart of
`two_mul_extraspecial_family_activeSpectrum_budget_lt`, with the
fixed-space scale squared before the row budgets are summed. -/
theorem two_mul_odd_extraspecial_family_pairSpectrum_lt_four
    {I : Type uI} [Fintype I]
    {d : ℕ} (p n a b : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hinj : Function.Injective p)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i)
    (hdiv : ∀ i, p i ∣ 2 ^ a i - 1)
    (hd : ∀ i, d = a i * p i ^ n i * b i) :
    2 * (∑ i : I, (1 + (p i ^ (2 * n i + 1) - 1) *
        (4 ^ (d / p i) - 1))) < 4 ^ d := by
  classical
  let B : I → ℕ := fun i ↦
    1 + (p i ^ (2 * n i + 1) - 1) * (4 ^ (d / p i) - 1)
  cases isEmpty_or_nonempty I with
  | inl hI =>
      letI : IsEmpty I := hI
      simp
  | inr hI =>
      letI : Nonempty I := hI
      by_cases hcardOne : Fintype.card I = 1
      · let i₀ : I := Classical.choice hI
        have hsub : Subsingleton I :=
          Fintype.card_le_one_iff_subsingleton.mp hcardOne.le
        have hsum : ∑ i : I, B i = B i₀ := by
          apply Finset.sum_eq_single i₀
          · intro i _hi hne
            exact False.elim (hne (Subsingleton.elim i i₀))
          · simp
        change 2 * (∑ i : I, B i) < 4 ^ d
        rw [hsum]
        exact two_mul_odd_extraspecial_pairSpectrum_budget_lt_four
          (hp i₀) (hpTwo i₀) (hn i₀) (ha i₀) (hb i₀)
          (hdiv i₀) (hd i₀)
      · have hcardTwo : 2 ≤ Fintype.card I := by
          have hcardPos : 0 < Fintype.card I := Fintype.card_pos
          omega
        have hthreePow : ∀ i, 3 * p i ^ n i ≤ d :=
          three_mul_extraspecial_primePower_le_dimension
            p n a b hp hpTwo hinj hn ha hb hd hcardTwo
        let m := d / 3
        have hpThree : ∀ i, 3 ≤ p i := by
          intro i
          obtain ⟨k, hk⟩ := (hp i).odd_of_ne_two (hpTwo i)
          have := (hp i).two_le
          omega
        have hprimePower : ∀ i, p i ^ n i ≤ m := by
          intro i
          apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2
          simpa [m, mul_comm] using hthreePow i
        have hfixedExp : ∀ i, d / p i ≤ m := by
          intro i
          exact Nat.div_le_div_left (hpThree i) (by norm_num)
        have hq : ∀ i, p i ^ (2 * n i + 1) ≤ 4 ^ m := by
          intro i
          exact
            (odd_extraspecial_order_le_four_pow_primePower
              (hp i) (hpTwo i) (hn i)).trans
              (Nat.pow_le_pow_right (by norm_num : 0 < 4)
                (hprimePower i))
        have hx : ∀ i, 4 ^ (d / p i) ≤ 4 ^ m := by
          intro i
          exact Nat.pow_le_pow_right (by norm_num : 0 < 4) (hfixedExp i)
        have hB : ∀ i, B i ≤ 4 ^ (2 * m) := by
          intro i
          let q := p i ^ (2 * n i + 1)
          let x := 4 ^ (d / p i)
          have hqOne : 1 < q := by
            dsimp [q]
            exact one_lt_pow₀ (hp i).one_lt (by omega)
          have hxOne : 1 ≤ x := by
            dsimp [x]
            exact Nat.one_le_pow _ _ (by norm_num)
          have hcompressed : 1 + (q - 1) * (x - 1) ≤ q * x := by
            have hqSub : 1 ≤ q - 1 := by omega
            calc
              1 + (q - 1) * (x - 1) =
                  (q - 1) * (x - 1) + 1 := by omega
              _ ≤ (q - 1) * (x - 1) + (q - 1) :=
                Nat.add_le_add_left hqSub _
              _ = (q - 1) * ((x - 1) + 1) := by
                rw [mul_add, mul_one]
              _ = (q - 1) * x := by rw [Nat.sub_add_cancel hxOne]
              _ ≤ q * x := Nat.mul_le_mul_right x (Nat.sub_le q 1)
          change 1 + (q - 1) * (x - 1) ≤ 4 ^ (2 * m)
          calc
            _ ≤ q * x := hcompressed
            _ ≤ 4 ^ m * 4 ^ m := Nat.mul_le_mul (hq i) (hx i)
            _ = 4 ^ (2 * m) := by
              rw [← pow_add]
              congr 1
              omega
        have hsum : ∑ i : I, B i ≤ d * 4 ^ (2 * m) := by
          have hpiLePow : ∀ i, p i ≤ p i ^ n i := by
            intro i
            calc
              p i = p i ^ 1 := by simp
              _ ≤ p i ^ n i :=
                Nat.pow_le_pow_right (hp i).pos (hn i)
          have hpLtD : ∀ i, p i < d := by
            intro i
            have hp3 := hpThree i
            have hpow := hpiLePow i
            have hdim := hthreePow i
            omega
          let f : I → Fin d := fun i ↦ ⟨p i, hpLtD i⟩
          have hf : Function.Injective f := by
            intro i j hij
            apply hinj
            exact congrArg Fin.val hij
          have hcardD : Fintype.card I ≤ d := by
            simpa [f] using Fintype.card_le_of_injective f hf
          calc
            ∑ i : I, B i ≤ ∑ _i : I, 4 ^ (2 * m) := by
              apply Finset.sum_le_sum
              intro i _hi
              exact hB i
            _ = Fintype.card I * 4 ^ (2 * m) := by simp
            _ ≤ d * 4 ^ (2 * m) := Nat.mul_le_mul_right _ hcardD
        let i₀ : I := Classical.choice hI
        have hdNine : 9 ≤ d := by
          have hp3 := hpThree i₀
          have hpow :
              p i₀ ≤ p i₀ ^ n i₀ := by
            calc
              p i₀ = p i₀ ^ 1 := by simp
              _ ≤ p i₀ ^ n i₀ :=
                Nat.pow_le_pow_right (hp i₀).pos (hn i₀)
          have hdim := hthreePow i₀
          omega
        have hmThree : 3 ≤ m := by
          dsimp [m]
          exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by omega)
        have hmMul : 3 * m ≤ d := by
          simpa [m, mul_comm] using Nat.div_mul_le_self d 3
        have htwoD : 2 * d < 4 ^ m := by
          calc
            2 * d ≤ 6 * m + 4 := by
              have := Nat.lt_mul_div_succ d (by norm_num : 0 < 3)
              omega
            _ < 3 ^ m :=
              six_mul_add_four_lt_three_pow_of_three_le m hmThree
            _ ≤ 4 ^ m :=
              Nat.pow_le_pow_left (by norm_num : 3 ≤ 4) _
        have hFourPos : 0 < 4 ^ (2 * m) := pow_pos (by norm_num) _
        change 2 * (∑ i : I, B i) < 4 ^ d
        calc
          2 * (∑ i : I, B i) ≤ 2 * (d * 4 ^ (2 * m)) :=
            Nat.mul_le_mul_left 2 hsum
          _ = (2 * d) * 4 ^ (2 * m) := by ring
          _ < 4 ^ m * 4 ^ (2 * m) :=
            Nat.mul_lt_mul_of_pos_right htwoD hFourPos
          _ = 4 ^ (3 * m) := by
            rw [← pow_add]
            congr 1
            omega
          _ ≤ 4 ^ d :=
            Nat.pow_le_pow_right (by norm_num : 0 < 4) hmMul

/-- Binary-power presentation of the characteristic-two odd-family
pair-spectrum theorem. -/
theorem two_mul_odd_extraspecial_family_pairSpectrum_lt
    {I : Type uI} [Fintype I]
    {d : ℕ} (p n a b : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hinj : Function.Injective p)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i)
    (hdiv : ∀ i, p i ∣ 2 ^ a i - 1)
    (hd : ∀ i, d = a i * p i ^ n i * b i) :
    2 * (∑ i : I, (1 + (p i ^ (2 * n i + 1) - 1) *
        (2 ^ (2 * (d / p i)) - 1))) < 2 ^ (2 * d) := by
  have h :=
    two_mul_odd_extraspecial_family_pairSpectrum_lt_four
      p n a b hp hpTwo hinj hn ha hb hdiv hd
  simpa [pow_mul] using h

end LisiSabatini
