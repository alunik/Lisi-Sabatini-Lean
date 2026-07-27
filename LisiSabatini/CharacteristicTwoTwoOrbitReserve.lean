import LisiSabatini.AffineTwoBaseOrbitAvoidance
import LisiSabatini.AffineTwoBaseTwoOrbitReserveArithmetic
import LisiSabatini.QuasiprimitiveAffineParityCATB

/-!
# The strong characteristic-two quasiprimitive affine leaf

For a distinctly prime-labelled family of cross-characteristic normal
prime subgroups in a positive-dimensional quasiprimitive binary linear
group, the diagonal action on two copies of the module has a common
regular translate outside two prescribed orbits of any distinguished
component.

The numerical input is a fourfold reserve for the direct pair-spectrum of
all noncommuting odd prime cores.  A noncommuting distinguished core pays
for both of its orbits inside its own pair-spectrum row.  A commuting core
acts fixed-point-freely off zero, so its order is at most the number of
module points.  Dimension one is handled separately: every
cross-characteristic prime core is then trivial.
-/

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI

/-! ## Fourfold characteristic-two pair-spectrum reserve -/

/-- For `m ≥ 3`, the binary square base absorbs twice a ternary power. -/
private theorem two_mul_three_pow_le_four_pow_of_three_le
    (m : ℕ) (hm : 3 ≤ m) :
    2 * 3 ^ m ≤ 4 ^ m := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  clear hm
  induction k with
  | zero =>
      norm_num
  | succ k ih =>
      rw [show 3 + (k + 1) = (3 + k) + 1 by omega,
        pow_succ, pow_succ]
      calc
        2 * (3 ^ (3 + k) * 3) =
            3 * (2 * 3 ^ (3 + k)) := by ring
        _ ≤ 3 * 4 ^ (3 + k) := Nat.mul_le_mul_left 3 ih
        _ ≤ 4 * 4 ^ (3 + k) :=
          Nat.mul_le_mul_right _ (by norm_num)
        _ = 4 ^ (3 + k) * 4 := by ring

/-- One odd extraspecial row in characteristic two occupies less than one
quarter of the doubled module. -/
private theorem four_mul_odd_extraspecial_pairSpectrum_budget_lt_four
    {p n a b d : ℕ}
    (hp : Nat.Prime p) (hpTwo : p ≠ 2)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hdiv : p ∣ 2 ^ a - 1)
    (hd : d = a * p ^ n * b) :
    4 * (1 + (p ^ (2 * n + 1) - 1) *
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
  have hePos : 0 < e := by
    dsimp [e]
    exact Nat.mul_pos (Nat.mul_pos ha (pow_pos hp.pos _)) hb
  have hxFour : 4 ≤ x := by
    calc
      4 = 4 ^ 1 := by simp
      _ ≤ 4 ^ e := Nat.pow_le_pow_right (by norm_num) hePos
      _ = x := rfl
  rw [hquot, htop]
  change 4 * (1 + (q - 1) * (x - 1)) < x ^ p
  by_cases hsmall : p = 3 ∧ k = 0
  · rcases hsmall with ⟨rfl, rfl⟩
    norm_num only [q, pow_one]
    have haTwo : 2 ≤ a := by
      by_contra hnot
      have haOne : a = 1 := by omega
      subst a
      norm_num at hdiv
    have heTwo : 2 ≤ e := by
      dsimp [e]
      norm_num
      exact haTwo.trans
        (Nat.le_mul_of_pos_right a hb)
    have hxSixteen : 16 ≤ x := by
      calc
        16 = 4 ^ 2 := by norm_num
        _ ≤ 4 ^ e := Nat.pow_le_pow_right (by norm_num) heTwo
        _ = x := rfl
    have hsq : 104 ≤ x * x := by nlinarith
    calc
      4 * (1 + 26 * (x - 1)) < 104 * x := by omega
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
      4 * (1 + (q - 1) * (x - 1)) ≤ 4 * (q * x) :=
        Nat.mul_le_mul_left 4 hbad
      _ < 4 * (x ^ (p - 2) * x) :=
        Nat.mul_lt_mul_of_pos_left
          (Nat.mul_lt_mul_of_pos_right horder hxPos) (by norm_num)
      _ ≤ x * (x ^ (p - 2) * x) :=
        Nat.mul_le_mul_right _ hxFour
      _ = x ^ p := by
        rw [show x * (x ^ (p - 2) * x) =
          x ^ (p - 2) * x ^ 2 by ring, ← pow_add]
        congr 1
        omega

/-- A distinctly prime-labelled family of odd extraspecial rows in
characteristic two occupies less than one quarter of the doubled module. -/
theorem four_mul_odd_extraspecial_family_pairSpectrum_lt_four
    {I : Type uI} [Fintype I]
    {d : ℕ} (p n a b : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hinj : Function.Injective p)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i)
    (hdiv : ∀ i, p i ∣ 2 ^ a i - 1)
    (hd : ∀ i, d = a i * p i ^ n i * b i) :
    4 * (∑ i : I, (1 + (p i ^ (2 * n i + 1) - 1) *
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
        change 4 * (∑ i : I, B i) < 4 ^ d
        rw [hsum]
        exact four_mul_odd_extraspecial_pairSpectrum_budget_lt_four
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
        have hfourD : 4 * d < 4 ^ m := by
          have hdUpper := Nat.lt_mul_div_succ d (by norm_num : 0 < 3)
          have hlinear : 4 * d ≤ 2 * (6 * m + 4) := by
            have hdUpper' : d < (m + 1) * 3 := by
              simpa [m, mul_comm] using hdUpper
            omega
          have hexp : 2 * (6 * m + 4) < 2 * 3 ^ m :=
            Nat.mul_lt_mul_of_pos_left
              (six_mul_add_four_lt_three_pow_of_three_le m hmThree)
              (by norm_num)
          exact hlinear.trans_lt
            (hexp.trans_le
              (two_mul_three_pow_le_four_pow_of_three_le m hmThree))
        have hFourPos : 0 < 4 ^ (2 * m) := pow_pos (by norm_num) _
        change 4 * (∑ i : I, B i) < 4 ^ d
        calc
          4 * (∑ i : I, B i) ≤ 4 * (d * 4 ^ (2 * m)) :=
            Nat.mul_le_mul_left 4 hsum
          _ = (4 * d) * 4 ^ (2 * m) := by ring
          _ < 4 ^ m * 4 ^ (2 * m) :=
            Nat.mul_lt_mul_of_pos_right hfourD hFourPos
          _ = 4 ^ (3 * m) := by
            rw [← pow_add]
            congr 1
            omega
          _ ≤ 4 ^ d :=
            Nat.pow_le_pow_right (by norm_num : 0 < 4) hmMul

/-- Binary-power presentation of the fourfold characteristic-two family
reserve. -/
theorem four_mul_odd_extraspecial_family_pairSpectrum_lt
    {I : Type uI} [Fintype I]
    {d : ℕ} (p n a b : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hinj : Function.Injective p)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i)
    (hdiv : ∀ i, p i ∣ 2 ^ a i - 1)
    (hd : ∀ i, d = a i * p i ^ n i * b i) :
    4 * (∑ i : I, (1 + (p i ^ (2 * n i + 1) - 1) *
        (2 ^ (2 * (d / p i)) - 1))) < 2 ^ (2 * d) := by
  have h :=
    four_mul_odd_extraspecial_family_pairSpectrum_lt_four
      p n a b hp hpTwo hinj hn ha hb hdiv hd
  simpa [pow_mul] using h

/-! ## Prime-core reserve -/

namespace CharacteristicTwoTwoOrbitReserve

variable {d : ℕ}
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod 2) (Fin d → ZMod 2))}
variable {I : Type uI} [Fintype I] {p : I → ℕ}

local instance finiteConcreteLinearSubgroup
    (s e : ℕ) [NeZero s]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod s) (Fin e → ZMod s))) :
    Finite P :=
  finite_linearSubgroup_of_finite P

/-- Fourfold reserve for the noncommuting rows of a structural binary
prime-core family. -/
theorem four_mul_noncommuting_pairSpectrumSum_lt_of_charTwo
    (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p)
    (hcross : ∀ i, p i ≠ 2)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows 2 d K p) :
    4 * (∑ i : {i : I //
        (pCore (p i) K).map K.subtype ≠ ⊥ ∧
          ¬ IsCommutingPrimeCore (p i) K},
      (1 + (p (i : I) ^ (2 * R.rank (i : I) + 1) - 1) *
        (2 ^ (2 * (d / p (i : I))) - 1))) <
      2 ^ (2 * d) := by
  let A := {i : I //
    (pCore (p i) K).map K.subtype ≠ ⊥ ∧
      ¬ IsCommutingPrimeCore (p i) K}
  let pA : A → ℕ := fun i ↦ p i.1
  let nA : A → ℕ := fun i ↦ R.rank i.1
  let aA : A → ℕ := fun i ↦ R.schurDegree i.1
  let bA : A → ℕ := fun i ↦ R.multiplicity i.1
  have hraw :=
    four_mul_odd_extraspecial_family_pairSpectrum_lt
      pA nA aA bA
      (fun i ↦ hp i.1)
      (fun i ↦ hcross i.1)
      (fun i j hij ↦ Subtype.ext (hinj hij))
      (fun i ↦ by
        dsimp only [nA]
        rw [← R.structuralRank_eq i.1 i.2.1 i.2.2]
        exact
          (R.cyclicCenter i.1 i.2.1 i.2.2)
            |>.cyclicCenterStructuralRank_pos)
      (fun i ↦ R.schurDegree_pos i.1 i.2.1 i.2.2)
      (fun i ↦ R.multiplicity_pos i.1 i.2.1 i.2.2)
      (fun i ↦ by
        let hP := R.cyclicCenter i.1 i.2.1 i.2.2
        exact
          (show p i.1 ∣ Nat.card (Subgroup.center
              ((pCore (p i.1) K).map K.subtype)) from by
            calc
              p i.1 = Nat.card (centerPrimeKernel (p i.1)
                  ((pCore (p i.1) K).map K.subtype)) :=
                hP.card_centerPrimeKernel.symm
              _ ∣ Nat.card (Subgroup.center
                  ((pCore (p i.1) K).map K.subtype)) :=
                Subgroup.card_dvd_of_le
                  (centerPrimeKernel_le_center (p i.1)
                    ((pCore (p i.1) K).map K.subtype)))
            |>.trans
              (R.center_card_dvd_field_pow_sub_one
                i.1 i.2.1 i.2.2))
      (fun i ↦ R.dimension_eq i.1 i.2.1 i.2.2)
  simpa [A, pA, nA, aA, bA] using hraw

/-- In dimension one over `F₂`, every cross-characteristic prime core in
a structural quasiprimitive family is trivial. -/
private theorem mapped_pCore_eq_bot_of_dimension_one
    (hdOne : d = 1)
    (hp : ∀ i, Nat.Prime (p i))
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows 2 d K p)
    (i : I) :
    (pCore (p i) K).map K.subtype = ⊥ := by
  let P := (pCore (p i) K).map K.subtype
  by_contra hne
  by_cases hcomm : IsCommutingPrimeCore (p i) K
  · have hdiv :
        p i ∣ Nat.card (Fin d → ZMod 2) - 1 :=
      prime_dvd_natCard_sub_one_of_nontrivial_pGroup_fixedPointFreeOffZero
        (hp i) P hne ((pCore_isPGroup (p i) K).map K.subtype)
        (R.commutative_fixedPointFree i hne hcomm)
    rw [hdOne, Nat.card_fun, Nat.card_fin, Nat.card_zmod] at hdiv
    have hpOne : p i = 1 := Nat.dvd_one.mp (by simpa using hdiv)
    exact (hp i).ne_one hpOne
  · have hn : 0 < R.rank i := by
      rw [← R.structuralRank_eq i hne hcomm]
      exact
        (R.cyclicCenter i hne hcomm).cyclicCenterStructuralRank_pos
    have hpDvdPow : p i ∣ p i ^ R.rank i :=
      dvd_pow_self _ hn.ne'
    have hpDvdD : p i ∣ d := by
      rw [R.dimension_eq i hne hcomm]
      exact (hpDvdPow.mul_left _).mul_right _
    rw [hdOne] at hpDvdD
    have hpOne : p i = 1 := Nat.dvd_one.mp hpDvdD
    exact (hp i).ne_one hpOne

/-- The exact characteristic-two counting inequality required for
two-orbit avoidance: all affine two-base bad loci plus two complete
orbits of any distinguished mapped prime core fit strictly inside the
doubled module. -/
theorem
    sum_affineTwoBaseBadSet_add_two_mul_natCard_mapped_pCore_lt_of_quasiprimitive_of_charTwo
    (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p)
    (hcross : ∀ i, p i ≠ 2)
    (hqp : IsQuasiprimitiveLinearAction 2 d K)
    (j₀ : I) :
    (∑ i,
        (affineTwoBaseBadSet
          ((pCore (p i) K).map K.subtype) 0 0).ncard) +
      2 * Nat.card ((pCore (p j₀) K).map K.subtype) <
        2 ^ (2 * d) := by
  classical
  let R :
      PrimeCoreMixedCyclicCenterFullSchurFamilyRows 2 d K p :=
    PrimeCoreMixedCyclicCenterFullSchurFamilyRows.ofQuasiprimitive
      hp hcross hqp
      (fun i hne hnoncomm ↦ by
        let hA : IsAdmissibleNoncommutingPrimeCore 2 d (p i) K :=
          ⟨hp i, hcross i, hcross i, hne, hnoncomm⟩
        exact
          mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
            (by norm_num) hqp hA
            (mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
              (by norm_num) hqp hA))
  let A := {i : I //
    (pCore (p i) K).map K.subtype ≠ ⊥ ∧
      ¬ IsCommutingPrimeCore (p i) K}
  let C := {i : I //
    (pCore (p i) K).map K.subtype ≠ ⊥ ∧
      IsCommutingPrimeCore (p i) K}
  let B : I → ℕ := fun i ↦
    1 + (p i ^ (2 * R.rank i + 1) - 1) *
      (2 ^ (2 * (d / p i)) - 1)
  let S := ∑ i : A, B i.1
  let c := Fintype.card C
  let N := 2 ^ d
  let T := 2 ^ (2 * d)
  let P₀ := (pCore (p j₀) K).map K.subtype
  have hbad :
      (∑ i,
        (affineTwoBaseBadSet
          ((pCore (p i) K).map K.subtype) 0 0).ncard) ≤
        S + c := by
    calc
      _ ≤ ∑ i,
          QuasiprimitiveAffineParityCATB.pairSpectrumWeight R i := by
        apply Finset.sum_le_sum
        intro i _hi
        exact
          QuasiprimitiveAffineParityCATB.ncard_affineTwoBaseBadSet_zero_le_pairSpectrumWeight
            R i
      _ = S + c := by
        simpa [A, C, B, S, c] using
          QuasiprimitiveAffineParityCATB.sum_pairSpectrumWeight_eq_split R
  by_cases hdOne : d = 1
  · have hcoreBot : ∀ i,
        (pCore (p i) K).map K.subtype = ⊥ :=
      mapped_pCore_eq_bot_of_dimension_one hdOne hp R
    have hweightZero :
        (∑ i,
          QuasiprimitiveAffineParityCATB.pairSpectrumWeight R i) = 0 := by
      apply Finset.sum_eq_zero
      intro i _hi
      simp [QuasiprimitiveAffineParityCATB.pairSpectrumWeight,
        hcoreBot i]
    have hbadZero :
        (∑ i,
          (affineTwoBaseBadSet
            ((pCore (p i) K).map K.subtype) 0 0).ncard) = 0 := by
      have hle :
          (∑ i,
            (affineTwoBaseBadSet
              ((pCore (p i) K).map K.subtype) 0 0).ncard) ≤ 0 := by
        calc
          _ ≤ ∑ i,
              QuasiprimitiveAffineParityCATB.pairSpectrumWeight R i := by
            apply Finset.sum_le_sum
            intro i _hi
            exact
              QuasiprimitiveAffineParityCATB.ncard_affineTwoBaseBadSet_zero_le_pairSpectrumWeight
                R i
          _ = 0 := hweightZero
      omega
    have hcardOne : Nat.card P₀ = 1 := by
      dsimp only [P₀]
      rw [hcoreBot j₀, Subgroup.card_bot]
    rw [hbadZero, hcardOne, hdOne]
    norm_num
  · have hdTwo : 2 ≤ d := by omega
    have hfourS : 4 * S < T := by
      simpa [A, B, S, T] using
        four_mul_noncommuting_pairSpectrumSum_lt_of_charTwo
          hp hinj hcross R
    have hcN : c ≤ N := by
      simpa [C, c, N] using
        QuasiprimitiveAffineParityCATB.card_commutingIndex_le_of_charTwo
          hd hp hinj R
    have hNfour : 4 ≤ N := by
      calc
        4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hdTwo
        _ = N := rfl
    have hT : T = N * N := by
      dsimp only [T, N]
      rw [← pow_add]
      congr 1
      omega
    have hfourN : 4 * N ≤ T := by
      rw [hT]
      exact Nat.mul_le_mul_right N hNfour
    have hTpos : 0 < T := by
      dsimp only [T]
      positivity
    by_cases hbot : P₀ = ⊥
    · have hcard : Nat.card P₀ ≤ N := by
        rw [hbot, Subgroup.card_bot]
        omega
      exact (Nat.add_le_add_right hbad (2 * Nat.card P₀)).trans_lt
        (by omega)
    · by_cases hcomm : IsCommutingPrimeCore (p j₀) K
      · have hcardDvd : Nat.card P₀ ∣ N - 1 := by
          have hfp := R.commutative_fixedPointFree j₀ hbot hcomm
          simpa [P₀, N, Nat.card_fun, Nat.card_fin, Nat.card_zmod] using
            natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero P₀ hfp
        have hcard : Nat.card P₀ ≤ N := by
          exact
            (Nat.le_of_dvd (by omega : 0 < N - 1) hcardDvd).trans
              (Nat.sub_le N 1)
        exact (Nat.add_le_add_right hbad (2 * Nat.card P₀)).trans_lt
          (by omega)
      · let jA : A := ⟨j₀, hbot, hcomm⟩
        have hcardRow : 2 * Nat.card P₀ ≤ B j₀ := by
          let hP := R.cyclicCenter j₀ hbot hcomm
          have hdim := R.dimension_eq j₀ hbot hcomm
          rw [← R.structuralRank_eq j₀ hbot hcomm] at hdim
          have hraw :=
            two_mul_natCard_le_odd_cyclicCenter_pairSpectrum_of_fullCenterRow
              hP
              (R.schurDegree_pos j₀ hbot hcomm)
              (R.multiplicity_pos j₀ hbot hcomm)
              (R.center_card_dvd_field_pow_sub_one j₀ hbot hcomm)
              hdim
          rw [R.structuralRank_eq j₀ hbot hcomm] at hraw
          simpa [P₀, B] using hraw
        have hrowS : B j₀ ≤ S := by
          change B jA.1 ≤ ∑ i : A, B i.1
          exact Finset.single_le_sum
            (fun i _ ↦ Nat.zero_le (B i.1))
            (Finset.mem_univ jA)
        exact (Nat.add_le_add_right hbad (2 * Nat.card P₀)).trans_lt
          (by omega)

/-- The mapped prime cores themselves have the strong diagonal
two-orbit-avoidance property in characteristic two. -/
theorem
    twoOrbitAvoidingCommonRegularTranslates_diagonal_pCores_of_quasiprimitive_of_charTwo
    {J : Type uI} [Finite J] {q : J → ℕ}
    (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (q i))
    (hinj : Function.Injective q)
    (hcross : ∀ i, q i ≠ 2)
    (hqp : IsQuasiprimitiveLinearAction 2 d K) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun i ↦
        (((pCore (q i) K).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod 2) (Fin d → ZMod 2)))) := by
  letI := Fintype.ofFinite J
  apply
    twoOrbitAvoidingCommonRegularTranslates_of_sum_ncard_add_two_mul_natCard_lt
  intro j₀
  have hbudget :=
    sum_affineTwoBaseBadSet_add_two_mul_natCard_mapped_pCore_lt_of_quasiprimitive_of_charTwo
      hd hp hinj hcross hqp j₀
  have hnonregular (i : J) :
      nonregularVectors
          (((pCore (q i) K).map K.subtype).map
            (diagonalGeneralLinearHom (ZMod 2) (Fin d → ZMod 2))) =
        affineTwoBaseBadSet
          ((pCore (q i) K).map K.subtype) 0 0 := by
    ext z
    simpa using
      (mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
        ((pCore (q i) K).map K.subtype) 0 0 z).symm
  have hmapCard :
      Nat.card
          (((pCore (q j₀) K).map K.subtype).map
            (diagonalGeneralLinearHom (ZMod 2) (Fin d → ZMod 2))) =
        Nat.card ((pCore (q j₀) K).map K.subtype) := by
    exact
      Subgroup.card_map_of_injective
        (diagonalGeneralLinearHom_injective
          (ZMod 2) (Fin d → ZMod 2))
  rw [show
    (∑ i,
      (nonregularVectors
        (((pCore (q i) K).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod 2)
            (Fin d → ZMod 2)))).ncard) =
      ∑ i,
        (affineTwoBaseBadSet
          ((pCore (q i) K).map K.subtype) 0 0).ncard by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hnonregular i]]
  rw [hmapCard, Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  rw [← pow_add]
  simpa only [show d + d = 2 * d by omega] using hbudget

/-- Every positive-dimensional quasiprimitive binary linear action
satisfies the recursively stable diagonal two-orbit invariant for
arbitrary distinctly prime-labelled normal cross-characteristic
subgroups. -/
theorem
    commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_quasiprimitive_of_charTwo
    (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction 2 d K) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
      2 (Fin d → ZMod 2) K := by
  intro I _ p hp hinj hcross H hHnormal hHp
  apply
    TwoOrbitAvoidingCommonRegularTranslates.mono
      (B := fun i ↦
        (((pCore (p i) K).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod 2) (Fin d → ZMod 2))))
  · intro i
    exact Subgroup.map_mono
      (map_normalPSubgroup_le_map_pCore (hHp i) (hHnormal i))
  · exact
      twoOrbitAvoidingCommonRegularTranslates_diagonal_pCores_of_quasiprimitive_of_charTwo
        hd hp hinj hcross hqp

end CharacteristicTwoTwoOrbitReserve

end LisiSabatini
