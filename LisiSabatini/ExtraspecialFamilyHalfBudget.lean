module

public import LisiSabatini.ExtraspecialFamilyArithmeticCore

/-!
# Half-space budget for an extraspecial family

The complete active fixed-space budget of a finite, distinctly
prime-labelled extraspecial family occupies strictly less than half of its
ambient odd prime-field vector space.  This is the complementary estimate
needed to mix extraspecial rows with an arbitrary fixed-point-free prime
family: the latter has at most half as many active rows as ambient points.
-/

@[expose] public section

namespace LisiSabatini

universe uI

/-! ## One row -/

/-- Twice the active fixed-space budget of one admissible odd extraspecial
row is strictly smaller than the ambient space. -/
theorem two_mul_extraspecial_activeSpectrum_budget_lt
    {r p n a b d : ℕ}
    (hr : Nat.Prime r) (hp : Nat.Prime p)
    (hrTwo : r ≠ 2) (hpTwo : p ≠ 2) (hrp : r ≠ p)
    (hn : 0 < n) (ha : 0 < a) (hb : 0 < b)
    (hdiv : p ∣ r ^ a - 1)
    (hd : d = a * p ^ n * b) :
    2 * (1 + (p ^ (2 * n + 1) - 1) *
      (r ^ (d / p) - 1)) < r ^ d := by
  subst d
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let e := a * p ^ k * b
  let x := r ^ e
  let q := p ^ (2 * (k + 1) + 1)
  have hePos : 0 < e := by
    dsimp [e]
    exact Nat.mul_pos (Nat.mul_pos ha (pow_pos hp.pos _)) hb
  have hdExp : a * p ^ (k + 1) * b = e * p := by
    dsimp [e]
    rw [pow_succ]
    ring
  have hquot : (a * p ^ (k + 1) * b) / p = e := by
    rw [hdExp]
    exact Nat.mul_div_cancel e hp.pos
  have htop : r ^ (a * p ^ (k + 1) * b) = x ^ p := by
    rw [hdExp, pow_mul]
  have hbase : 2 * p + 1 ≤ r ^ a :=
    two_mul_prime_add_one_le_pow_of_dvd_sub_one
      hr hp hrTwo hpTwo ha hdiv
  have hxEq : x = (r ^ a) ^ (p ^ k * b) := by
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
  · have hthree : p = 3 → k + 1 = 1 →
        27 < r ^ ((a * p ^ (k + 1) * b) / 3) := by
      intro hpEq hkOne
      exfalso
      exact hsmall ⟨hpEq, by omega⟩
    have horderRaw := extraspecial_order_lt_fixedScale_pow_sub_two
      hr hp hrTwo hpTwo hrp (by omega : 0 < k + 1)
      ha hb hdiv rfl hthree
    have horder : q < x ^ (p - 2) := by
      simpa [q, hquot, x] using horderRaw
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

/-! ## Finite families -/

/-- The complete active fixed-space budget of an admissible finite
extraspecial family is strictly below half of the ambient space. -/
theorem two_mul_extraspecial_family_activeSpectrum_budget_lt
    {I : Type uI} [Fintype I]
    {r d : ℕ} (p n a b : I → ℕ)
    (hr : Nat.Prime r) (hrTwo : r ≠ 2)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hn : ∀ i, 0 < n i) (ha : ∀ i, 0 < a i)
    (hb : ∀ i, 0 < b i)
    (hdiv : ∀ i, p i ∣ r ^ a i - 1)
    (hd : ∀ i, d = a i * p i ^ n i * b i) :
    2 * (∑ i : I, (1 + (p i ^ (2 * n i + 1) - 1) *
        (r ^ (d / p i) - 1))) < r ^ d := by
  classical
  let B : I → ℕ := fun i ↦
    1 + (p i ^ (2 * n i + 1) - 1) * (r ^ (d / p i) - 1)
  cases isEmpty_or_nonempty I with
  | inl hI =>
      let : IsEmpty I := hI
      simpa using pow_pos hr.pos d
  | inr hI =>
      let : Nonempty I := hI
      by_cases hcardOne : Fintype.card I = 1
      · let i₀ : I := Classical.choice hI
        have hsub : Subsingleton I :=
          Fintype.card_le_one_iff_subsingleton.mp hcardOne.le
        have hsum : ∑ i : I, B i = B i₀ := by
          apply Finset.sum_eq_single i₀
          · intro i _hi hne
            exact False.elim (hne (Subsingleton.elim i i₀))
          · simp
        change 2 * (∑ i : I, B i) < r ^ d
        rw [hsum]
        exact two_mul_extraspecial_activeSpectrum_budget_lt
          hr (hp i₀) hrTwo (hpTwo i₀) (hcross i₀).symm
          (hn i₀) (ha i₀) (hb i₀) (hdiv i₀) (hd i₀)
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
        have hq : ∀ i, p i ^ (2 * n i + 1) ≤ r ^ m := by
          intro i
          exact
            (extraspecial_order_le_field_pow_primePower
              hr (hp i) hrTwo (hpTwo i) (hn i)).trans
              (Nat.pow_le_pow_right hr.pos (hprimePower i))
        have hx : ∀ i, r ^ (d / p i) ≤ r ^ m := by
          intro i
          exact Nat.pow_le_pow_right hr.pos (hfixedExp i)
        have hB : ∀ i, B i ≤ r ^ (2 * m) := by
          intro i
          let q := p i ^ (2 * n i + 1)
          let x := r ^ (d / p i)
          have hqOne : 1 < q := by
            dsimp [q]
            exact one_lt_pow₀ (hp i).one_lt (by omega)
          have hxOne : 1 ≤ x := by
            dsimp [x]
            exact Nat.one_le_pow _ _ hr.pos
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
          change 1 + (q - 1) * (x - 1) ≤ r ^ (2 * m)
          calc
            _ ≤ q * x := hcompressed
            _ ≤ r ^ m * r ^ m := Nat.mul_le_mul (hq i) (hx i)
            _ = r ^ (2 * m) := by
              rw [← pow_add]
              congr 1
              omega
        have hsum : ∑ i : I, B i ≤ d * r ^ (2 * m) := by
          have hpiLePow : ∀ i, p i ≤ p i ^ n i := by
            intro i
            calc
              p i = p i ^ 1 := by simp
              _ ≤ p i ^ n i := Nat.pow_le_pow_right (hp i).pos (hn i)
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
            ∑ i : I, B i ≤ ∑ _i : I, r ^ (2 * m) := by
              apply Finset.sum_le_sum
              intro i _hi
              exact hB i
            _ = Fintype.card I * r ^ (2 * m) := by simp
            _ ≤ d * r ^ (2 * m) := Nat.mul_le_mul_right _ hcardD
        let i₀ : I := Classical.choice hI
        have hpiLePow : p i₀ ≤ p i₀ ^ n i₀ := by
          calc
            p i₀ = p i₀ ^ 1 := by simp
            _ ≤ p i₀ ^ n i₀ :=
              Nat.pow_le_pow_right (hp i₀).pos (hn i₀)
        have hdNine : 9 ≤ d := by
          have hp3 := hpThree i₀
          have hdim := hthreePow i₀
          omega
        have hmThree : 3 ≤ m := by
          dsimp [m]
          exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).2 (by omega)
        have hmMul : 3 * m ≤ d := by
          simpa [m, mul_comm] using Nat.div_mul_le_self d 3
        have hrThree : 3 ≤ r := by
          obtain ⟨k, hk⟩ := hr.odd_of_ne_two hrTwo
          have := hr.two_le
          omega
        have htwoD : 2 * d < r ^ m := by
          calc
            2 * d ≤ 6 * m + 4 := by
              have := Nat.lt_mul_div_succ d (by norm_num : 0 < 3)
              omega
            _ < 3 ^ m :=
              six_mul_add_four_lt_three_pow_of_three_le m hmThree
            _ ≤ r ^ m := Nat.pow_le_pow_left hrThree _
        have hRPos : 0 < r ^ (2 * m) := pow_pos hr.pos _
        change 2 * (∑ i : I, B i) < r ^ d
        calc
          2 * (∑ i : I, B i) ≤ 2 * (d * r ^ (2 * m)) :=
            Nat.mul_le_mul_left 2 hsum
          _ = (2 * d) * r ^ (2 * m) := by ring
          _ < r ^ m * r ^ (2 * m) :=
            Nat.mul_lt_mul_of_pos_right htwoD hRPos
          _ = r ^ (3 * m) := by
            rw [← pow_add]
            congr 1
            omega
          _ ≤ r ^ d := Nat.pow_le_pow_right hr.pos hmMul

end LisiSabatini
