module

public import LisiSabatini.AlternatingSylowBasePBlocks
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# A negative-binomial majorant for Sylow cycle profiles

For a prime `p`, put

`B p m j = (p - 1)^j * multichoose m j`.

Thus, when `m > 0`,

`B p m j = (p - 1)^j * choose (m + j - 1) j`.

This file develops the coefficientwise convolution calculus for this
sequence.  It is the natural majorant for the order-`p` cycle profile
of a Sylow subgroup of a symmetric group.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

/-- The coefficient of the negative-binomial comparison series. -/
def sylowCycleNegativeBinomialMajorant
    (p m j : ℕ) : ℕ :=
  (p - 1) ^ j * Nat.multichoose m j

@[simp]
theorem sylowCycleNegativeBinomialMajorant_zero_right
    (p m : ℕ) :
    sylowCycleNegativeBinomialMajorant p m 0 = 1 := by
  simp [sylowCycleNegativeBinomialMajorant]

@[simp]
theorem sylowCycleNegativeBinomialMajorant_zero_left_succ
    (p j : ℕ) :
    sylowCycleNegativeBinomialMajorant p 0 (j + 1) = 0 := by
  simp [sylowCycleNegativeBinomialMajorant]

theorem sylowCycleNegativeBinomialMajorant_eq_choose
    {p m j : ℕ} :
    sylowCycleNegativeBinomialMajorant p m j =
      (p - 1) ^ j * (m + j - 1).choose j := by
  rw [sylowCycleNegativeBinomialMajorant,
    Nat.multichoose_eq]

/-- Vandermonde convolution for multichoose. -/
theorem sum_antidiagonal_multichoose_mul
    (m n k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        Nat.multichoose m ij.1 *
          Nat.multichoose n ij.2) =
      Nat.multichoose (m + n) k := by
  by_cases hm : m = 0
  · subst m
    classical
    rw [Finset.sum_eq_single ((0, k) : ℕ × ℕ)]
    · simp
    · intro x hx hne
      have hsum := Finset.mem_antidiagonal.mp hx
      have hxPos : 0 < x.1 := by
        by_contra hx0
        have hxFirst : x.1 = 0 :=
          Nat.eq_zero_of_not_pos hx0
        apply hne
        apply Prod.ext
        · exact hxFirst
        · omega
      obtain ⟨r, hr⟩ :=
        Nat.exists_eq_succ_of_ne_zero hxPos.ne'
      rcases x with ⟨x₁, x₂⟩
      simp only at hr
      subst x₁
      simp
    · intro hnot
      exact (hnot (Finset.mem_antidiagonal.mpr (by simp))).elim
  by_cases hn : n = 0
  · subst n
    classical
    rw [Finset.sum_eq_single ((k, 0) : ℕ × ℕ)]
    · simp
    · intro x hx hne
      have hsum := Finset.mem_antidiagonal.mp hx
      have hxPos : 0 < x.2 := by
        by_contra hx0
        have hxSecond : x.2 = 0 :=
          Nat.eq_zero_of_not_pos hx0
        apply hne
        apply Prod.ext
        · omega
        · exact hxSecond
      obtain ⟨r, hr⟩ :=
        Nat.exists_eq_succ_of_ne_zero hxPos.ne'
      rcases x with ⟨x₁, x₂⟩
      simp only at hr
      subst x₂
      simp
    · intro hnot
      exact (hnot (Finset.mem_antidiagonal.mpr (by simp))).elim
  have hmPos : 0 < m := Nat.pos_of_ne_zero hm
  have hnPos : 0 < n := Nat.pos_of_ne_zero hn
  have hseries :=
    congrArg
      (fun u : (PowerSeries ℤ)ˣ =>
        PowerSeries.coeff k u.1)
      (PowerSeries.invOneSubPow_add
        (S := ℤ) m n)
  simp only [Units.val_mul, PowerSeries.coeff_mul] at hseries
  rw [
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos
      (S := ℤ) (d := m) hmPos,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos
      (S := ℤ) (d := n) hnPos,
    PowerSeries.invOneSubPow_val_eq_mk_sub_one_add_choose_of_pos
      (S := ℤ) (d := m + n) (Nat.add_pos_left hmPos n)] at hseries
  simp only [PowerSeries.coeff_mk] at hseries
  norm_cast at hseries
  have hchooseMultichoose
      (d r : ℕ) (hd : 0 < d) :
      (d - 1 + r).choose (d - 1) =
        Nat.multichoose d r := by
    rw [Nat.multichoose_eq]
    have htop : d + r - 1 = d - 1 + r := by
      omega
    rw [htop]
    exact Nat.choose_symm_add
  have hseries' :
      Nat.multichoose (m + n) k =
        ∑ x ∈ Finset.antidiagonal k,
          (m - 1 + x.1).choose (m - 1) *
            (n - 1 + x.2).choose (n - 1) := by
    rw [← hchooseMultichoose (m + n) k
      (Nat.add_pos_left hmPos n)]
    exact hseries
  calc
    (∑ x ∈ Finset.antidiagonal k,
        Nat.multichoose m x.1 *
          Nat.multichoose n x.2) =
        ∑ x ∈ Finset.antidiagonal k,
          (m - 1 + x.1).choose (m - 1) *
            (n - 1 + x.2).choose (n - 1) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [← hchooseMultichoose m x.1 hmPos,
        ← hchooseMultichoose n x.2 hnPos]
    _ = Nat.multichoose (m + n) k :=
      hseries'.symm

/-- The negative-binomial coefficients multiply by adding the
capacity parameters. -/
theorem sum_antidiagonal_sylowCycleNegativeBinomialMajorant_mul
    (p m n k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
        sylowCycleNegativeBinomialMajorant p m ij.1 *
          sylowCycleNegativeBinomialMajorant p n ij.2) =
      sylowCycleNegativeBinomialMajorant p (m + n) k := by
  simp only [sylowCycleNegativeBinomialMajorant]
  calc
    (∑ ij ∈ Finset.antidiagonal k,
        ((p - 1) ^ ij.1 * Nat.multichoose m ij.1) *
          ((p - 1) ^ ij.2 * Nat.multichoose n ij.2)) =
        (p - 1) ^ k *
          ∑ ij ∈ Finset.antidiagonal k,
            Nat.multichoose m ij.1 *
              Nat.multichoose n ij.2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ij hij
      have hs := Finset.mem_antidiagonal.mp hij
      calc
        ((p - 1) ^ ij.1 * Nat.multichoose m ij.1) *
              ((p - 1) ^ ij.2 * Nat.multichoose n ij.2) =
            ((p - 1) ^ ij.1 * (p - 1) ^ ij.2) *
              (Nat.multichoose m ij.1 *
                Nat.multichoose n ij.2) := by ring
        _ =
            (p - 1) ^ (ij.1 + ij.2) *
              (Nat.multichoose m ij.1 *
                Nat.multichoose n ij.2) := by
          rw [pow_add]
        _ =
            (p - 1) ^ k *
              (Nat.multichoose m ij.1 *
                Nat.multichoose n ij.2) := by rw [hs]
    _ = (p - 1) ^ k * Nat.multichoose (m + n) k := by
      rw [sum_antidiagonal_multichoose_mul]

/-! ## Coefficientwise convolution -/

/-- A polynomial is bounded coefficientwise by the negative-binomial
series with parameter `m`. -/
def IsSylowCycleNegativeBinomialMajorized
    (p m : ℕ) (f : Polynomial ℕ) : Prop :=
  ∀ j : ℕ,
    f.coeff j ≤
      sylowCycleNegativeBinomialMajorant p m j

theorem isSylowCycleNegativeBinomialMajorized_one
    (p : ℕ) :
    IsSylowCycleNegativeBinomialMajorized p 0 1 := by
  intro j
  cases j with
  | zero => simp
  | succ j => simp [Polynomial.coeff_one]

theorem IsSylowCycleNegativeBinomialMajorized.mul
    {p m n : ℕ} {f g : Polynomial ℕ}
    (hf : IsSylowCycleNegativeBinomialMajorized p m f)
    (hg : IsSylowCycleNegativeBinomialMajorized p n g) :
    IsSylowCycleNegativeBinomialMajorized p (m + n)
      (f * g) := by
  intro k
  rw [Polynomial.coeff_mul]
  calc
    (∑ ij ∈ Finset.antidiagonal k,
        f.coeff ij.1 * g.coeff ij.2) ≤
        ∑ ij ∈ Finset.antidiagonal k,
          sylowCycleNegativeBinomialMajorant p m ij.1 *
            sylowCycleNegativeBinomialMajorant p n ij.2 := by
      apply Finset.sum_le_sum
      intro ij _hij
      exact Nat.mul_le_mul (hf ij.1) (hg ij.2)
    _ = sylowCycleNegativeBinomialMajorant p (m + n) k :=
      sum_antidiagonal_sylowCycleNegativeBinomialMajorant_mul
        p m n k

theorem IsSylowCycleNegativeBinomialMajorized.pow
    {p m : ℕ} {f : Polynomial ℕ}
    (hf : IsSylowCycleNegativeBinomialMajorized p m f)
    (r : ℕ) :
    IsSylowCycleNegativeBinomialMajorized p (r * m)
      (f ^ r) := by
  induction r with
  | zero =>
      simpa using
        isSylowCycleNegativeBinomialMajorized_one p
  | succ r ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hf

theorem isSylowCycleNegativeBinomialMajorized_prod
    {ι : Type*}
    (p : ℕ) (s : Finset ι)
    (f : ι → Polynomial ℕ) (m : ι → ℕ)
    (h : ∀ i ∈ s,
      IsSylowCycleNegativeBinomialMajorized p (m i) (f i)) :
    IsSylowCycleNegativeBinomialMajorized p
      (∑ i ∈ s, m i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using
        isSylowCycleNegativeBinomialMajorized_one p
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact
        (h a (Finset.mem_insert_self a s)).mul
          (ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi))

/-! ## Tower support and order -/

/-- Maximum possible number of `p`-cycles in the action on `p^k`
letters.  The value at `k = 0` is zero. -/
def sylowTowerCycleCapacity (p : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => p ^ k

@[simp]
theorem sylowTowerCycleCapacity_zero (p : ℕ) :
    sylowTowerCycleCapacity p 0 = 0 :=
  rfl

@[simp]
theorem sylowTowerCycleCapacity_succ (p k : ℕ) :
    sylowTowerCycleCapacity p (k + 1) = p ^ k :=
  rfl

theorem mul_sylowTowerCycleCapacity_le_pow
    {p k : ℕ} :
    p * sylowTowerCycleCapacity p k ≤ p ^ k := by
  cases k with
  | zero => simp
  | succ k =>
      simp only [sylowTowerCycleCapacity_succ]
      rw [pow_succ']

theorem natDegree_sylowTowerCycleProfile_le
    {p k : ℕ} :
    (sylowTowerCycleProfile p k).natDegree ≤
      sylowTowerCycleCapacity p k := by
  induction k with
  | zero =>
      simp [sylowTowerCycleProfile,
        sylowTowerCycleCapacity]
  | succ k ih =>
      rw [sylowTowerCycleProfile_succ]
      have hleft :
          (sylowTowerCycleProfile p k ^ p).natDegree ≤
            sylowTowerCycleCapacity p (k + 1) :=
        (Polynomial.natDegree_pow_le_of_le p ih).trans
          mul_sylowTowerCycleCapacity_le_pow
      have hright :
          (Polynomial.C
              ((p - 1) *
                sylowTowerOrder p k ^ (p - 1)) *
              Polynomial.X ^ p ^ k).natDegree ≤
            sylowTowerCycleCapacity p (k + 1) := by
        simpa only [sylowTowerCycleCapacity_succ] using
          Polynomial.natDegree_C_mul_X_pow_le
            ((p - 1) * sylowTowerOrder p k ^ (p - 1))
            (p ^ k)
      simpa using
        (Polynomial.natDegree_add_le_of_le hleft hright)

/-- Closed order formula for the iterated Sylow tower. -/
theorem sylowTowerOrder_eq_pow_geomSum
    (p k : ℕ) :
    sylowTowerOrder p k =
      p ^ (∑ r ∈ Finset.range k, p ^ r) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sylowTowerOrder_succ, ih, ← pow_mul,
        show
          (∑ r ∈ Finset.range k, p ^ r) * p =
            p * ∑ r ∈ Finset.range k, p ^ r by
              exact Nat.mul_comm _ _]
      calc
        p *
            p ^ (p * ∑ r ∈ Finset.range k, p ^ r) =
            p ^ (p * ∑ r ∈ Finset.range k, p ^ r + 1) := by
          rw [pow_succ]
          exact Nat.mul_comm _ _
        _ =
            p ^ (∑ r ∈ Finset.range (k + 1), p ^ r) := by
          rw [geom_sum_succ]

theorem sylowTowerOrder_pow_pred
    {p k : ℕ} (hp : 2 ≤ p) :
    sylowTowerOrder p k ^ (p - 1) =
      p ^ (p ^ k - 1) := by
  rw [sylowTowerOrder_eq_pow_geomSum, ← pow_mul,
    Nat.mul_comm,
    pred_mul_geom_sum hp]

/-! ## The top-coefficient reserve -/

theorem choose_mul_choose_le_choose_add
    (a b i j : ℕ) :
    a.choose i * b.choose j ≤
      (a + b).choose (i + j) := by
  rw [Nat.add_choose_eq]
  have h :=
    Finset.single_le_sum
      (s := Finset.antidiagonal (i + j))
      (f := fun ij : ℕ × ℕ ↦
        a.choose ij.1 * b.choose ij.2)
      (fun x _hx ↦ Nat.zero_le _)
      (a := (i, j))
      (Finset.mem_antidiagonal.mpr rfl)
  simpa using h

theorem choose_mul_choose_pow_le
    (a b i j r : ℕ) :
    a.choose i * (b.choose j) ^ r ≤
      (a + r * b).choose (i + r * j) := by
  induction r with
  | zero => simp
  | succ r ih =>
      calc
        a.choose i * b.choose j ^ (r + 1) =
            (a.choose i * b.choose j ^ r) *
              b.choose j := by
          rw [pow_succ]
          ring
        _ ≤
            (a + r * b).choose (i + r * j) *
              b.choose j :=
          Nat.mul_le_mul_right _ ih
        _ ≤
            ((a + r * b) + b).choose
              ((i + r * j) + j) :=
          choose_mul_choose_le_choose_add _ _ _ _
        _ =
            (a + (r + 1) * b).choose
              (i + (r + 1) * j) := by
          simp only [Nat.succ_mul]
          rw [Nat.add_assoc, Nat.add_assoc]

theorem two_mul_choose_pow_le_middle
    {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) :
    2 * ((2 * m - 1).choose m) ^ p ≤
      (2 * (p * m) - 1).choose (p * m) := by
  have hblock :=
    choose_mul_choose_pow_le
      (2 * m - 1) (2 * m) m m (p - 1)
  have hcentral :
      (2 * m).choose m =
        2 * (2 * m - 1).choose m := by
    obtain ⟨r, rfl⟩ :=
      Nat.exists_eq_add_of_le hm
    rw [show 2 * (1 + r) - 1 = 2 * r + 1 by omega,
      show 2 * (1 + r) = (2 * r + 1) + 1 by omega,
      show 1 + r = r + 1 by omega,
      Nat.choose_succ_succ',
      Nat.choose_symm_half]
    ring
  rw [hcentral] at hblock
  have hpow :
      2 * ((2 * m - 1).choose m) ^ p ≤
        (2 * m - 1).choose m *
          (2 * (2 * m - 1).choose m) ^ (p - 1) := by
    rw [mul_pow]
    have htwo : 2 ≤ 2 ^ (p - 1) := by
      exact
        (Nat.pow_le_pow_right (by omega : 1 ≤ 2)
          (by omega : 1 ≤ p - 1))
    calc
      2 * ((2 * m - 1).choose m) ^ p ≤
          2 ^ (p - 1) *
            ((2 * m - 1).choose m) ^ p :=
        Nat.mul_le_mul_right _ htwo
      _ =
          (2 * m - 1).choose m *
            (2 ^ (p - 1) *
              ((2 * m - 1).choose m) ^ (p - 1)) := by
        have hpowA :
            ((2 * m - 1).choose m) ^ p =
              ((2 * m - 1).choose m) ^ (p - 1) *
                (2 * m - 1).choose m := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ p)]
        rw [hpowA]
        ring
  have hblock' :
      (2 * m - 1).choose m *
          (2 * (2 * m - 1).choose m) ^ (p - 1) ≤
        (2 * (p * m) - 1).choose (p * m) := by
    have hpEq : p - 1 + 1 = p :=
      Nat.sub_add_cancel (by omega)
    have hmSub : 2 * m - 1 + 1 = 2 * m :=
      Nat.sub_add_cancel (by nlinarith)
    have htop :
        2 * m - 1 + (p - 1) * (2 * m) =
          2 * (p * m) - 1 := by
      apply Nat.add_right_cancel (m := 1)
      rw [Nat.sub_add_cancel (by nlinarith : 1 ≤ 2 * (p * m))]
      nlinarith [hpEq, hmSub]
    have hindex :
        m + (p - 1) * m = p * m := by
      nlinarith [hpEq]
    simpa only [htop, hindex] using hblock
  exact hpow.trans hblock'

theorem three_mul_two_pow_sub_two_le_choose_middle_pred
    {M : ℕ} (hM : 2 ≤ M) :
    3 * 2 ^ (M - 2) ≤
      (2 * M - 1).choose M := by
  have h :=
    choose_mul_choose_pow_le 3 2 2 1 (M - 2)
  norm_num [Nat.choose] at h
  have hsub : M - 2 + 2 = M :=
    Nat.sub_add_cancel hM
  have htop :
      3 + (M - 2) * 2 = 2 * M - 1 := by
    apply Nat.add_right_cancel (m := 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * M)]
    nlinarith [hsub]
  have hindex : 2 + (M - 2) = M := by omega
  simpa only [htop, hindex] using h

theorem ten_mul_two_pow_sub_three_le_choose_middle_pred
    {M : ℕ} (hM : 3 ≤ M) :
    10 * 2 ^ (M - 3) ≤
      (2 * M - 1).choose M := by
  have h :=
    choose_mul_choose_pow_le 5 2 3 1 (M - 3)
  norm_num [Nat.choose] at h
  have hsub : M - 3 + 3 = M :=
    Nat.sub_add_cancel hM
  have htop :
      5 + (M - 3) * 2 = 2 * M - 1 := by
    apply Nat.add_right_cancel (m := 1)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ 2 * M)]
    nlinarith [hsub]
  have hindex : 3 + (M - 3) = M := by omega
  simpa only [htop, hindex] using h

theorem two_mul_topWreathTerm_le_majorantTop
    {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m)
    (hnotSmall : ¬(p = 2 ∧ m = 1)) :
    2 * ((p - 1) * p ^ (p * m - 1)) ≤
      sylowCycleNegativeBinomialMajorant
        p (p * m) (p * m) := by
  rw [sylowCycleNegativeBinomialMajorant,
    Nat.multichoose_eq]
  have hM : 2 ≤ p * m :=
    (Nat.mul_le_mul hp hm)
  by_cases hp2 : p = 2
  · subst p
    have hm2 : 2 ≤ m := by
      omega
    have hM4 : 4 ≤ 2 * m := by omega
    have hchoose :
        2 ^ (2 * m) ≤
          (2 * (2 * m) - 1).choose (2 * m) := by
      have hten :=
        ten_mul_two_pow_sub_three_le_choose_middle_pred
          (M := 2 * m) (by omega)
      calc
        2 ^ (2 * m) =
            8 * 2 ^ (2 * m - 3) := by
          rw [show 2 * m = 3 + (2 * m - 3) by omega,
            pow_add]
          norm_num
        _ ≤ 10 * 2 ^ (2 * m - 3) :=
          Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ (2 * (2 * m) - 1).choose (2 * m) :=
          hten
    simp only [Nat.reduceSub, one_mul, one_pow]
    calc
      2 * 2 ^ (2 * m - 1) = 2 ^ (2 * m) := by
        rw [← pow_succ']
        congr 1
        omega
      _ ≤ (2 * m + 2 * m - 1).choose (2 * m) := by
        have hbase : 2 * (2 * m) = 2 * m + 2 * m := by
          ring
        rw [hbase] at hchoose
        exact hchoose
  · have hp3 : 3 ≤ p := by omega
    have hM3 : 3 ≤ p * m :=
      hp3.trans (Nat.le_mul_of_pos_right p (by omega))
    obtain ⟨t, ht⟩ :=
      Nat.exists_eq_add_of_le hM3
    have hp_le : p ≤ 2 * (p - 1) := by omega
    have hpSq :
        2 * (p - 1) * p ^ 2 ≤
          6 * (p - 1) ^ 3 := by
      have hpSubOne : p - 1 + 1 = p :=
        Nat.sub_add_cancel (by omega)
      have hpSubThree : p - 3 + 3 = p :=
        Nat.sub_add_cancel hp3
      have hsq : p ^ 2 ≤ 3 * (p - 1) ^ 2 := by
        nlinarith [hpSubOne, hpSubThree,
          Nat.zero_le (2 * p * (p - 3))]
      calc
        2 * (p - 1) * p ^ 2 ≤
            2 * (p - 1) * (3 * (p - 1) ^ 2) :=
          Nat.mul_le_mul_left _ hsq
        _ = 6 * (p - 1) ^ 3 := by ring
    have hpow :
        p ^ t ≤ (2 * (p - 1)) ^ t :=
      Nat.pow_le_pow_left hp_le t
    have harith :
        2 * ((p - 1) * p ^ (p * m - 1)) ≤
          (p - 1) ^ (p * m) *
            (3 * 2 ^ (p * m - 2)) := by
      calc
        2 * ((p - 1) * p ^ (p * m - 1)) =
            (2 * (p - 1) * p ^ 2) * p ^ t := by
          rw [ht, show 3 + t - 1 = 2 + t by omega,
            pow_add]
          ring
        _ ≤
            (6 * (p - 1) ^ 3) *
              (2 * (p - 1)) ^ t :=
          Nat.mul_le_mul hpSq hpow
        _ =
            (p - 1) ^ (p * m) *
              (3 * 2 ^ (p * m - 2)) := by
          rw [ht, show 3 + t - 2 = 1 + t by omega,
            pow_add, pow_add, mul_pow]
          ring
    have hchoose :=
      three_mul_two_pow_sub_two_le_choose_middle_pred hM
    have hbase :
        2 * (p * m) = p * m + p * m := by ring
    rw [hbase] at hchoose
    exact harith.trans
      (Nat.mul_le_mul_left _ hchoose)

theorem majorantTop_pow_add_topWreathTerm_le
    {p m : ℕ} (hp : 2 ≤ p) (hm : 1 ≤ m) :
    sylowCycleNegativeBinomialMajorant p m m ^ p +
        (p - 1) * p ^ (p * m - 1) ≤
      sylowCycleNegativeBinomialMajorant
        p (p * m) (p * m) := by
  by_cases hsmall : p = 2 ∧ m = 1
  · rcases hsmall with ⟨rfl, rfl⟩
    norm_num [sylowCycleNegativeBinomialMajorant,
      Nat.multichoose]
  have hchoose :=
    two_mul_choose_pow_le_middle (p := p) (m := m) hp hm
  have hchoose' :
      2 * ((2 * m - 1).choose m) ^ p ≤
        (p * m + p * m - 1).choose (p * m) := by
    have hbase : 2 * (p * m) = p * m + p * m := by
      ring
    rw [hbase] at hchoose
    exact hchoose
  have hchoose'' :
      2 * ((m + m - 1).choose m) ^ p ≤
        (p * m + p * m - 1).choose (p * m) := by
    simpa only [two_mul] using hchoose'
  have hfirst :
      2 *
          sylowCycleNegativeBinomialMajorant p m m ^ p ≤
        sylowCycleNegativeBinomialMajorant
          p (p * m) (p * m) := by
    rw [sylowCycleNegativeBinomialMajorant,
      sylowCycleNegativeBinomialMajorant,
      Nat.multichoose_eq, Nat.multichoose_eq,
      mul_pow]
    calc
      2 *
          (((p - 1) ^ m) ^ p *
            ((m + m - 1).choose m) ^ p) =
          (p - 1) ^ (p * m) *
            (2 * ((m + m - 1).choose m) ^ p) := by
        rw [← pow_mul]
        ring
      _ ≤
          (p - 1) ^ (p * m) *
            (p * m + p * m - 1).choose (p * m) :=
        Nat.mul_le_mul_left _ hchoose''
  have hsecond :=
    two_mul_topWreathTerm_le_majorantTop
      hp hm hsmall
  omega

/-! ## The tower majorant -/

theorem sylowTowerCycleProfile_negativeBinomialMajorized
    {p k : ℕ} (hp : 2 ≤ p) :
    IsSylowCycleNegativeBinomialMajorized p
      (sylowTowerCycleCapacity p k)
      (sylowTowerCycleProfile p k) := by
  induction k with
  | zero =>
      simpa [sylowTowerCycleProfile,
        sylowTowerCycleCapacity] using
        isSylowCycleNegativeBinomialMajorized_one p
  | succ k ih =>
      cases k with
      | zero =>
          intro j
          cases j with
          | zero =>
              simp [sylowTowerCycleProfile,
                sylowTowerCycleCapacity,
                sylowCycleNegativeBinomialMajorant]
          | succ j =>
              cases j with
              | zero =>
                  simp [sylowTowerCycleProfile,
                    sylowTowerCycleCapacity,
                    sylowCycleNegativeBinomialMajorant,
                    sylowTowerOrder,
                    Polynomial.coeff_one]
              | succ j =>
                  simp [sylowTowerCycleProfile,
                    sylowTowerCycleCapacity,
                    sylowCycleNegativeBinomialMajorant,
                    sylowTowerOrder,
                    Polynomial.coeff_one]
      | succ k =>
          let m := p ^ k
          have hm : 1 ≤ m := by
            exact Nat.one_le_pow _ _ (by omega)
          have hdegree :
              (sylowTowerCycleProfile p (k + 1)).natDegree ≤ m := by
            simpa only [sylowTowerCycleCapacity_succ] using
              natDegree_sylowTowerCycleProfile_le
                (p := p) (k := k + 1)
          have hpow :=
            ih.pow p
          have hM : p * m = p ^ (k + 1) := by
            simp only [m, pow_succ']
          intro j
          rw [sylowTowerCycleProfile_succ,
            Polynomial.coeff_add,
            Polynomial.coeff_C_mul,
            Polynomial.coeff_X_pow]
          by_cases hj : j = p * m
          · subst j
            rw [if_pos hM,
              Nat.mul_one,
              Polynomial.coeff_pow_of_natDegree_le hdegree,
              sylowTowerOrder_pow_pred hp, ← hM]
            have hcoeff :
                (sylowTowerCycleProfile p (k + 1)).coeff m ^ p ≤
                  sylowCycleNegativeBinomialMajorant p m m ^ p :=
              Nat.pow_le_pow_left (ih m) p
            calc
              (sylowTowerCycleProfile p (k + 1)).coeff m ^ p +
                    (p - 1) * p ^ (p * m - 1) ≤
                  sylowCycleNegativeBinomialMajorant p m m ^ p +
                    (p - 1) * p ^ (p * m - 1) :=
                Nat.add_le_add_right hcoeff _
              _ ≤
                  sylowCycleNegativeBinomialMajorant
                    p (p * m) (p * m) :=
                majorantTop_pow_add_topWreathTerm_le hp hm
              _ =
                  sylowCycleNegativeBinomialMajorant
                    p (sylowTowerCycleCapacity p (k + 2))
                      (p * m) := by
                simp only [sylowTowerCycleCapacity_succ, m,
                  pow_succ']
          · have hj' : j ≠ p ^ (k + 1) := by
              simpa only [← hM] using hj
            rw [if_neg hj', Nat.mul_zero, Nat.add_zero]
            simpa only [sylowTowerCycleCapacity_succ, m,
              pow_succ'] using hpow j

/-! ## Assembly over the base-`p` blocks -/

theorem sum_basePDigit_mul_sylowTowerCycleCapacity
    (n p : ℕ) (hp : 2 ≤ p) :
    (∑ k ∈ Finset.range (n + 1),
        basePDigit n p k *
          sylowTowerCycleCapacity p k) =
      n / p := by
  let S :=
    ∑ k ∈ Finset.range n,
      basePDigit n p (k + 1) * p ^ k
  have htotal :=
    sum_basePDigit_mul_pow n p hp
  have htotal' :
      n % p + S * p = n := by
    rw [Finset.sum_range_succ'] at htotal
    simp only [basePDigit, pow_zero, Nat.div_one,
      Nat.mul_one] at htotal
    have htail :
        (∑ x ∈ Finset.range n,
            n / p ^ (x + 1) % p * p ^ (x + 1)) =
          S * p := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _hk
      simp only [basePDigit]
      rw [pow_succ']
      ring
    rw [htail] at htotal
    simpa only [Nat.add_comm] using htotal
  have hdivision :
      n % p + (n / p) * p = n := by
    simpa [Nat.add_comm, Nat.mul_comm] using
      (Nat.div_add_mod n p)
  have hmul : S * p = (n / p) * p := by
    omega
  have hS : S = n / p :=
    Nat.eq_of_mul_eq_mul_right (by omega) hmul
  rw [Finset.sum_range_succ']
  simp only [sylowTowerCycleCapacity_zero, Nat.mul_zero,
    sylowTowerCycleCapacity_succ]
  exact hS

/-- The claimed global coefficient majorant.  It is valid in every
degree and has no finite-range restriction. -/
theorem sylowCycleProfile_coeff_le_negativeBinomialMajorant
    {n p j : ℕ} (hp : p.Prime) :
    (sylowCycleProfile n p).coeff j ≤
      sylowCycleNegativeBinomialMajorant p (n / p) j := by
  rw [sylowCycleProfile]
  have hprod :=
    isSylowCycleNegativeBinomialMajorized_prod
      p (Finset.range (n + 1))
      (fun k ↦
        if basePDigit n p k = 0 then 1
        else
          sylowTowerCycleProfile p k ^
            basePDigit n p k)
      (fun k ↦
        basePDigit n p k *
          sylowTowerCycleCapacity p k)
      (by
        intro k _hk
        by_cases hdigit : basePDigit n p k = 0
        · simp only [hdigit, if_pos, zero_mul]
          exact
            isSylowCycleNegativeBinomialMajorized_one p
        · simp only [hdigit]
          exact
            (sylowTowerCycleProfile_negativeBinomialMajorized
              (p := p) (k := k) hp.two_le).pow
                (basePDigit n p k))
  rw [sum_basePDigit_mul_sylowTowerCycleCapacity
    n p hp.two_le] at hprod
  exact hprod j

/-- Choose notation for the majorant, under the natural nonempty-row
hypothesis. -/
theorem sylowCycleProfile_coeff_le_choose_majorant
    {n p j : ℕ} (hp : p.Prime) (_hpn : p ≤ n) :
    (sylowCycleProfile n p).coeff j ≤
      (p - 1) ^ j *
        (n / p + j - 1).choose j := by
  exact
    (sylowCycleProfile_coeff_le_negativeBinomialMajorant
      (n := n) (p := p) (j := j) hp).trans_eq
        sylowCycleNegativeBinomialMajorant_eq_choose

end LisiSabatini
