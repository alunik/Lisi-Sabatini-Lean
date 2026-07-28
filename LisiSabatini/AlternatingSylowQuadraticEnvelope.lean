module

public import LisiSabatini.AlternatingSylowNegativeBinomial
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Logic.Equiv.Fintype

/-!
# A global quadratic envelope for alternating Sylow rows

This file turns the exact Sylow cycle-profile recurrence into an
explicit quadratic class-sum estimate.  The negative-binomial
majorant is monotone at successive odd-prime blocks.  At the binary
row, where only an even number of transpositions lies in `A_n`, a
two-block monotonicity argument avoids the spurious odd top term.

The final arithmetic endpoint is deliberately coarse and modular:
for every `n ≥ 40`, the sum of the majorants is strictly below `1/4`.
This leaves enough room for the factor-four index-two transfer from
`S_n` to `A_n`.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

/-! ## Growth inside a prime block -/

/-- Extend a permutation of `Fin n` by fixing the final point. -/
def quadraticPermFinSucc (n : ℕ) :
    Equiv.Perm (Fin n) → Equiv.Perm (Fin (n + 1)) :=
  fun g ↦ g.viaFintypeEmbedding Fin.castSuccEmb

theorem quadraticPermFinSucc_injective
    (n : ℕ) :
    Function.Injective (quadraticPermFinSucc n) := by
  intro g h hgh
  apply
    Equiv.Perm.extendDomainHom_injective
      Fin.castSuccEmb.toEquivRange
  simpa only [quadraticPermFinSucc,
    Equiv.Perm.viaFintypeEmbedding] using hgh

theorem cycleType_quadraticPermFinSucc
    (n : ℕ) (g : Equiv.Perm (Fin n)) :
    (quadraticPermFinSucc n g).cycleType = g.cycleType := by
  simpa only [quadraticPermFinSucc,
    Equiv.Perm.viaFintypeEmbedding] using
      (Equiv.Perm.cycleType_extendDomain
        Fin.castSuccEmb.toEquivRange (g := g))

theorem card_primeCycleTypeFinset_le_succ
    (n p j : ℕ) :
    (primeCycleTypeFinset n p j).card ≤
      (primeCycleTypeFinset (n + 1) p j).card := by
  classical
  apply
    Finset.card_le_card_of_injOn (quadraticPermFinSucc n)
  · intro g hg
    simp only [Finset.mem_coe, primeCycleTypeFinset,
      Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rw [cycleType_quadraticPermFinSucc]
    exact hg
  · exact (quadraticPermFinSucc_injective n).injOn

theorem primeCycleClassCard_le_succ
    {n p j : ℕ} (hp : 2 ≤ p) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    primeCycleClassCard n p j ≤
      primeCycleClassCard (n + 1) p j := by
  rw [← card_primeCycleTypeFinset hp hj hpj,
    ← card_primeCycleTypeFinset hp hj
      (hpj.trans (Nat.le_succ n))]
  exact card_primeCycleTypeFinset_le_succ n p j

theorem primeCycleClassCard_pos
    {n p j : ℕ} (hp : 2 ≤ p) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    0 < primeCycleClassCard n p j := by
  rw [← card_primeCycleTypeFinset hp hj hpj,
    Finset.card_pos]
  have hvalid :
      (Multiset.replicate j p).sum ≤ Fintype.card (Fin n) ∧
        ∀ a ∈ Multiset.replicate j p, 2 ≤ a := by
    constructor
    · simpa [Nat.mul_comm] using hpj
    · intro a ha
      simpa [Multiset.eq_of_mem_replicate ha] using hp
  obtain ⟨g, hg⟩ :=
    (Equiv.Perm.exists_with_cycleType_iff
      (α := Fin n)
      (m := Multiset.replicate j p)).mpr hvalid
  exact
    ⟨g, by
      simp only [primeCycleTypeFinset, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hg⟩
theorem primeCycleClassCard_mul_centralizer
    {n p j : ℕ} (hp : 2 ≤ p) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    primeCycleClassCard n p j *
        (p ^ j * j.factorial * (n - p * j).factorial) =
      n.factorial := by
  classical
  have hvalid :
      (Multiset.replicate j p).sum ≤ Fintype.card (Fin n) ∧
        ∀ a ∈ Multiset.replicate j p, 2 ≤ a := by
    constructor
    · simpa [Nat.mul_comm] using hpj
    · intro a ha
      simpa [Multiset.eq_of_mem_replicate ha] using hp
  have hmul :=
    Equiv.Perm.card_of_cycleType_mul_eq
      (Fin n) (Multiset.replicate j p)
  rw [if_pos hvalid] at hmul
  have hcard :=
    card_primeCycleTypeFinset hp hj hpj
  have hfiltered :
      ({g : Equiv.Perm (Fin n) |
          g.cycleType = Multiset.replicate j p} : Finset _).card =
        primeCycleClassCard n p j := by
    simpa [primeCycleTypeFinset] using hcard
  rw [hfiltered] at hmul
  simpa [hj.ne',
    Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

theorem primeCycleClassCard_mul_cycleCentralizer
    {n p j : ℕ} (hp : 2 ≤ p) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    primeCycleClassCard n p j * (p ^ j * j.factorial) =
      n.descFactorial (p * j) := by
  have hclass :=
    primeCycleClassCard_mul_centralizer hp hj hpj
  have hfactorial :=
    Nat.factorial_mul_descFactorial hpj
  let r := (n - p * j).factorial
  have hcancel :
      r *
          (primeCycleClassCard n p j *
            (p ^ j * j.factorial)) =
        r * n.descFactorial (p * j) := by
    calc
      r *
          (primeCycleClassCard n p j *
            (p ^ j * j.factorial)) =
          primeCycleClassCard n p j *
            (p ^ j * j.factorial * r) := by
              simp only [r]
              ring
      _ = n.factorial := by
        simpa only [Nat.mul_assoc] using hclass
      _ = r * n.descFactorial (p * j) := by
        simpa only [r] using hfactorial.symm
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hcancel

/-! ## Quadratic negative-binomial costs -/

/-- The quadratic cost obtained by replacing every exact cycle-profile
coefficient by its negative-binomial majorant. -/
def sylowCycleNegativeBinomialQuadraticCost
    (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n / p),
    sylowCycleNegativeBinomialMajorant p (n / p) j ^ 2 /
      (primeCycleClassCard n p j : ℝ)

/-- The binary majorant after discarding the odd-transposition rows,
which do not lie in the alternating group. -/
def sylowCycleNegativeBinomialEvenQuadraticCost
    (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n / 2),
    if Even j then
      sylowCycleNegativeBinomialMajorant 2 (n / 2) j ^ 2 /
        (primeCycleClassCard n 2 j : ℝ)
    else 0

theorem symmetricSylowProfileQuadraticCost_le_negativeBinomial
    {n p : ℕ} (hp : p.Prime) :
    symmetricSylowProfileQuadraticCost n p ≤
      sylowCycleNegativeBinomialQuadraticCost n p := by
  rw [symmetricSylowProfileQuadraticCost,
    sylowCycleNegativeBinomialQuadraticCost]
  apply Finset.sum_le_sum
  intro j _hj
  have hcoeff :=
    sylowCycleProfile_coeff_le_negativeBinomialMajorant
      (n := n) (p := p) (j := j) hp
  have hcoeffReal :
      ((sylowCycleProfile n p).coeff j : ℝ) ≤
        sylowCycleNegativeBinomialMajorant
          p (n / p) j := by
    exact_mod_cast hcoeff
  gcongr

theorem alternatingSylowProfileQuadraticCost_two_le_negativeBinomialEven
    (n : ℕ) :
    alternatingSylowProfileQuadraticCost n 2 ≤
      sylowCycleNegativeBinomialEvenQuadraticCost n := by
  rw [alternatingSylowProfileQuadraticCost, if_pos rfl,
    sylowCycleNegativeBinomialEvenQuadraticCost]
  apply Finset.sum_le_sum
  intro j _hj
  split_ifs with hj
  · have hcoeff :=
      sylowCycleProfile_coeff_le_negativeBinomialMajorant
        (n := n) (p := 2) (j := j) Nat.prime_two
    have hcoeffReal :
        ((sylowCycleProfile n 2).coeff j : ℝ) ≤
          sylowCycleNegativeBinomialMajorant
            2 (n / 2) j := by
      exact_mod_cast hcoeff
    gcongr
  · exact le_rfl

theorem sylowCycleNegativeBinomialQuadraticCost_succ_le_of_not_dvd
    {n p : ℕ} (hp : 2 ≤ p) (hpn : ¬p ∣ n + 1) :
    sylowCycleNegativeBinomialQuadraticCost (n + 1) p ≤
      sylowCycleNegativeBinomialQuadraticCost n p := by
  rw [sylowCycleNegativeBinomialQuadraticCost,
    sylowCycleNegativeBinomialQuadraticCost,
    Nat.succ_div_of_not_dvd hpn]
  apply Finset.sum_le_sum
  intro j hj
  have hjpos : 0 < j :=
    (Finset.mem_Icc.mp hj).1
  have hpj : p * j ≤ n := by
    simpa only [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le (by omega : 0 < p)).mp
        (Finset.mem_Icc.mp hj).2
  have hcard :=
    primeCycleClassCard_le_succ hp hjpos hpj
  have hcardPos :
      (0 : ℝ) <
        (primeCycleClassCard n p j : ℕ) := by
    exact_mod_cast primeCycleClassCard_pos hp hjpos hpj
  gcongr

theorem sylowCycleNegativeBinomialEvenQuadraticCost_succ_le_of_odd
    {n : ℕ} (hodd : Odd (n + 1)) :
    sylowCycleNegativeBinomialEvenQuadraticCost (n + 1) ≤
      sylowCycleNegativeBinomialEvenQuadraticCost n := by
  have hnotdvd : ¬2 ∣ n + 1 := by
    exact hodd.not_two_dvd_nat
  rw [sylowCycleNegativeBinomialEvenQuadraticCost,
    sylowCycleNegativeBinomialEvenQuadraticCost,
    Nat.succ_div_of_not_dvd hnotdvd]
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with heven
  · have hjpos : 0 < j :=
      (Finset.mem_Icc.mp hj).1
    have h2j : 2 * j ≤ n := by
      simpa only [Nat.mul_comm] using
        (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mp
          (Finset.mem_Icc.mp hj).2
    have hcard :=
      primeCycleClassCard_le_succ (p := 2)
        (by omega) hjpos h2j
    have hcardPos :
        (0 : ℝ) <
          (primeCycleClassCard n 2 j : ℕ) := by
      exact_mod_cast
        primeCycleClassCard_pos (p := 2)
          (by omega) hjpos h2j
    gcongr
  · exact le_rfl

theorem sylowCycleNegativeBinomialQuadraticCost_mul_add_le
    {p m r : ℕ} (hp : 2 ≤ p) (hr : r < p) :
    sylowCycleNegativeBinomialQuadraticCost (p * m + r) p ≤
      sylowCycleNegativeBinomialQuadraticCost (p * m) p := by
  induction r with
  | zero =>
      simp
  | succ r ih =>
      have hrp : r < p := by omega
      have hnotdvd : ¬p ∣ p * m + r + 1 := by
        intro hdiv
        have hsmall : p ∣ r + 1 := by
          exact
            (Nat.dvd_add_iff_right
              (dvd_mul_right p m)).mpr
              (by simpa [Nat.add_assoc] using hdiv)
        have hle : p ≤ r + 1 :=
          Nat.le_of_dvd (by omega) hsmall
        omega
      exact
        (sylowCycleNegativeBinomialQuadraticCost_succ_le_of_not_dvd
          hp hnotdvd).trans (ih hrp)

theorem sylowCycleNegativeBinomialQuadraticCost_le_blockStart
    {n p : ℕ} (hp : 2 ≤ p) :
    sylowCycleNegativeBinomialQuadraticCost n p ≤
      sylowCycleNegativeBinomialQuadraticCost
        (p * (n / p)) p := by
  have hr : n % p < p :=
    Nat.mod_lt n (by omega)
  have h :=
    sylowCycleNegativeBinomialQuadraticCost_mul_add_le
      (p := p) (m := n / p) hp hr
  rwa [Nat.div_add_mod] at h

theorem sylowCycleNegativeBinomialEvenQuadraticCost_mul_add_le
    {m r : ℕ} (hr : r < 2) :
    sylowCycleNegativeBinomialEvenQuadraticCost (2 * m + r) ≤
      sylowCycleNegativeBinomialEvenQuadraticCost (2 * m) := by
  interval_cases r
  · simp
  · exact
      sylowCycleNegativeBinomialEvenQuadraticCost_succ_le_of_odd
        (n := 2 * m) (by
          refine ⟨m, ?_⟩
          omega)

theorem sylowCycleNegativeBinomialEvenQuadraticCost_le_blockStart
    (n : ℕ) :
    sylowCycleNegativeBinomialEvenQuadraticCost n ≤
      sylowCycleNegativeBinomialEvenQuadraticCost
        (2 * (n / 2)) := by
  have hr : n % 2 < 2 :=
    Nat.mod_lt n (by omega)
  have h :=
    sylowCycleNegativeBinomialEvenQuadraticCost_mul_add_le
      (m := n / 2) hr
  rwa [Nat.div_add_mod] at h

theorem primeCycleClassCard_succBlock_ratio
    {p m j : ℕ} (hp : 2 ≤ p) (hj : 0 < j) (hjm : j ≤ m) :
    primeCycleClassCard (p * (m + 1)) p j *
        (p * (m - j) + 1).ascFactorial p =
      primeCycleClassCard (p * m) p j *
        (p * m + 1).ascFactorial p := by
  let d := p ^ j * j.factorial
  let r := (p * (m - j)).factorial
  let lower := (p * (m - j) + 1).ascFactorial p
  let upper := (p * m + 1).ascFactorial p
  have hjOld : p * j ≤ p * m :=
    Nat.mul_le_mul_left p hjm
  have hjNew : p * j ≤ p * (m + 1) :=
    hjOld.trans (Nat.mul_le_mul_left p (Nat.le_succ m))
  have hold :=
    primeCycleClassCard_mul_centralizer
      (n := p * m) (p := p) (j := j) hp hj hjOld
  have hnew :=
    primeCycleClassCard_mul_centralizer
      (n := p * (m + 1)) (p := p) (j := j) hp hj hjNew
  have hrestOld :
      p * m - p * j = p * (m - j) := by
    exact (Nat.mul_sub_left_distrib p m j).symm
  have hrestNew :
      p * (m + 1) - p * j = p * (m - j) + p := by
    rw [← Nat.mul_sub_left_distrib]
    calc
      p * (m + 1 - j) = p * ((m - j) + 1) := by
        congr 1
        omega
      _ = p * (m - j) + p := by ring
  have hlower :
      r * lower = (p * (m - j) + p).factorial := by
    simpa only [r, lower] using
      Nat.factorial_mul_ascFactorial (p * (m - j)) p
  have hupper :
      (p * m).factorial * upper =
        (p * (m + 1)).factorial := by
    simpa only [upper, Nat.mul_add, Nat.mul_one] using
      Nat.factorial_mul_ascFactorial (p * m) p
  rw [hrestOld] at hold
  rw [hrestNew, ← hlower, ← hupper] at hnew
  have hcancel :
      d * r *
          (primeCycleClassCard (p * (m + 1)) p j * lower) =
        d * r *
          (primeCycleClassCard (p * m) p j * upper) := by
    calc
      d * r *
          (primeCycleClassCard (p * (m + 1)) p j * lower) =
          primeCycleClassCard (p * (m + 1)) p j *
            (d * (r * lower)) := by
              simp only [d]
              ring
      _ = (p * m).factorial * upper := by
        simpa only [d, Nat.mul_assoc] using hnew
      _ =
          primeCycleClassCard (p * m) p j *
            (d * r) * upper := by
        rw [← hold]
      _ =
          d * r *
            (primeCycleClassCard (p * m) p j * upper) := by
        ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hcancel

theorem ascFactorial_mono_base
    {a b k : ℕ} (hab : a ≤ b) :
    a.ascFactorial k ≤ b.ascFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.ascFactorial_succ, Nat.ascFactorial_succ]
      exact Nat.mul_le_mul (Nat.add_le_add_right hab k) ih

theorem ascFactorial_add_two
    (a k : ℕ) :
    a.ascFactorial (k + 2) =
      a * (a + 1) * (a + 2).ascFactorial k := by
  induction k with
  | zero =>
      simp [Nat.ascFactorial_succ]
      ring
  | succ k ih =>
      rw [show k + 1 + 2 = (k + 2) + 1 by omega,
        Nat.ascFactorial_succ, ih,
        Nat.ascFactorial_succ]
      ring

/-- Two factors of the class-cardinality growth already dominate the
three-halves power needed by the cubic cost. -/
theorem ascFactorial_succBlock_cross_square
    {p m j : ℕ} (hp : 2 ≤ p) (hj : 0 < j) (hjm : j ≤ m) :
    (p * (m - j) + 1).ascFactorial p * (m + j) ^ 2 ≤
      (p * m + 1).ascFactorial p * m ^ 2 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hp
  have hadd : 2 + k = k + 2 := by omega
  rw [hadd] at *
  have hpjTwo : 2 ≤ (k + 2) * j :=
    by
      simpa using Nat.mul_le_mul (by omega : 2 ≤ k + 2) hj
  have hpdecomp :
      (k + 2) * (m - j) + (k + 2) * j =
        (k + 2) * m := by
    rw [← Nat.mul_add, Nat.sub_add_cancel hjm]
  have hfirst :
      ((k + 2) * (m - j) + 1) * (m + j) ≤
        ((k + 2) * m + 1) * m := by
    have hmul :
        j * 1 ≤ j * ((k + 2) * j) :=
      Nat.mul_le_mul_left j (by omega)
    nlinarith [hpdecomp]
  have hsecond :
      ((k + 2) * (m - j) + 2) * (m + j) ≤
        ((k + 2) * m + 2) * m := by
    have hmul :
        j * 2 ≤ j * ((k + 2) * j) :=
      Nat.mul_le_mul_left j hpjTwo
    nlinarith [hpdecomp]
  have hbase :
      (k + 2) * (m - j) + 3 ≤ (k + 2) * m + 3 := by
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_left (k + 2) (Nat.sub_le m j)) 3
  have htail :
      ((k + 2) * (m - j) + 3).ascFactorial k ≤
        ((k + 2) * m + 3).ascFactorial k :=
    ascFactorial_mono_base hbase
  rw [ascFactorial_add_two, ascFactorial_add_two]
  calc
    (((k + 2) * (m - j) + 1) *
          ((k + 2) * (m - j) + 1 + 1) *
          ((k + 2) * (m - j) + 1 + 2).ascFactorial k) *
        (m + j) ^ 2 =
      (((k + 2) * (m - j) + 1) * (m + j)) *
        (((k + 2) * (m - j) + 2) * (m + j)) *
        ((k + 2) * (m - j) + 3).ascFactorial k := by
          ring
    _ ≤
      (((k + 2) * m + 1) * m) *
        (((k + 2) * m + 2) * m) *
        ((k + 2) * m + 3).ascFactorial k :=
      Nat.mul_le_mul (Nat.mul_le_mul hfirst hsecond) htail
    _ =
      ((k + 2) * m + 1) *
          ((k + 2) * m + 1 + 1) *
          ((k + 2) * m + 1 + 2).ascFactorial k *
        m ^ 2 := by ring

theorem sylowCycleNegativeBinomialMajorant_succBlock_ratio
    {p m j : ℕ} (hm : 0 < m) :
    sylowCycleNegativeBinomialMajorant p (m + 1) j * m =
      sylowCycleNegativeBinomialMajorant p m j * (m + j) := by
  rw [sylowCycleNegativeBinomialMajorant_eq_choose,
    sylowCycleNegativeBinomialMajorant_eq_choose]
  have hchoose :=
    Nat.choose_mul_succ_eq (m + j - 1) j
  have htop : m + j - 1 + 1 = m + j := by omega
  have hdiff : m + j - j = m := by omega
  rw [htop, hdiff] at hchoose
  have harg : m + 1 + j - 1 = m + j := by omega
  calc
    ((p - 1) ^ j * (m + 1 + j - 1).choose j) * m =
        (p - 1) ^ j * ((m + j).choose j * m) := by
          rw [harg]
          ring
    _ =
        (p - 1) ^ j *
          ((m + j - 1).choose j * (m + j)) := by
      rw [← hchoose]
    _ =
        ((p - 1) ^ j * (m + j - 1).choose j) *
          (m + j) := by ring

theorem sylowCycleNegativeBinomialMajorant_sameTop_succ
    {p m : ℕ} (hm : 0 < m) :
    sylowCycleNegativeBinomialMajorant p (m + 1) m =
      2 * sylowCycleNegativeBinomialMajorant p m m := by
  have h :=
    sylowCycleNegativeBinomialMajorant_succBlock_ratio
      (p := p) (m := m) (j := m) hm
  have hcancel :
      sylowCycleNegativeBinomialMajorant p (m + 1) m * m =
        (2 * sylowCycleNegativeBinomialMajorant p m m) * m := by
    calc
      sylowCycleNegativeBinomialMajorant p (m + 1) m * m =
          sylowCycleNegativeBinomialMajorant p m m *
            (m + m) := h
      _ =
          (2 * sylowCycleNegativeBinomialMajorant p m m) * m := by
        ring
  exact Nat.eq_of_mul_eq_mul_right hm hcancel

theorem sylowCycleNegativeBinomialMajorant_newTop_ratio
    {p m : ℕ} (hm : 0 < m) :
    sylowCycleNegativeBinomialMajorant p (m + 1) (m + 1) *
        (m + 1) =
      sylowCycleNegativeBinomialMajorant p m m *
        (2 * (p - 1) * (2 * m + 1)) := by
  rw [sylowCycleNegativeBinomialMajorant_eq_choose,
    sylowCycleNegativeBinomialMajorant_eq_choose]
  have hcentral :=
    Nat.choose_mul_succ_eq (2 * m - 1) m
  have htop : 2 * m - 1 + 1 = 2 * m := by omega
  have hdiff : 2 * m - m = m := by omega
  rw [htop, hdiff] at hcentral
  have hcentral' :
      (2 * m).choose m =
        2 * (2 * m - 1).choose m := by
    apply Nat.eq_of_mul_eq_mul_right hm
    calc
      (2 * m).choose m * m =
          (2 * m - 1).choose m * (2 * m) :=
        hcentral.symm
      _ = (2 * (2 * m - 1).choose m) * m := by ring
  have hnext :=
    Nat.add_one_mul_choose_eq (2 * m) m
  have hargNew :
      m + 1 + (m + 1) - 1 = 2 * m + 1 := by omega
  have hargOld : m + m - 1 = 2 * m - 1 := by omega
  rw [hcentral'] at hnext
  rw [hargNew, hargOld, pow_succ]
  calc
    ((p - 1) ^ m * (p - 1) *
          (2 * m + 1).choose (m + 1)) *
        (m + 1) =
      (p - 1) ^ m * (p - 1) *
        ((2 * m + 1).choose (m + 1) * (m + 1)) := by
          ring
    _ =
      (p - 1) ^ m * (p - 1) *
        ((2 * m + 1) *
          (2 * (2 * m - 1).choose m)) := by
      rw [← hnext]
    _ =
      ((p - 1) ^ m * (2 * m - 1).choose m) *
        (2 * (p - 1) * (2 * m + 1)) := by ring

theorem primeCycleClassCard_newTop_ratio
    {p m : ℕ} (hp : 2 ≤ p) (hm : 0 < m) :
    primeCycleClassCard (p * (m + 1)) p (m + 1) =
      primeCycleClassCard (p * m) p m *
        (p * m + 1).ascFactorial (p - 1) := by
  let cn := primeCycleClassCard (p * (m + 1)) p (m + 1)
  let co := primeCycleClassCard (p * m) p m
  let d := p ^ m * m.factorial
  let v := (p * m + 1).ascFactorial (p - 1)
  have hnew :=
    primeCycleClassCard_mul_cycleCentralizer
      (n := p * (m + 1)) (p := p) (j := m + 1)
      hp (by omega) (by exact le_rfl)
  have hold :=
    primeCycleClassCard_mul_cycleCentralizer
      (n := p * m) (p := p) (j := m)
      hp hm (by rfl)
  have hnewDesc :
      (p * (m + 1)).descFactorial (p * (m + 1)) =
        (p * (m + 1)).factorial :=
    Nat.descFactorial_self _
  have holdDesc :
      (p * m).descFactorial (p * m) =
        (p * m).factorial :=
    Nat.descFactorial_self _
  rw [hnewDesc] at hnew
  rw [holdDesc] at hold
  have hdnew :
      p ^ (m + 1) * (m + 1).factorial =
        d * (p * (m + 1)) := by
    simp only [d, pow_succ, Nat.factorial_succ]
    ring
  have hv :
      v * (p * (m + 1)) =
        (p * m + 1).ascFactorial p := by
    have hlast :
        p * m + 1 + (p - 1) = p * (m + 1) := by
      calc
        p * m + 1 + (p - 1) = p * m + p := by omega
        _ = p * (m + 1) := by ring
    have hrec :=
      Nat.ascFactorial_succ
        (n := p * m + 1) (k := p - 1)
    have hsucc : (p - 1).succ = p := by omega
    rw [hsucc] at hrec
    calc
      v * (p * (m + 1)) =
          (p * m + 1 + (p - 1)) *
            (p * m + 1).ascFactorial (p - 1) := by
        rw [hlast]
        simp only [v]
        ring
      _ = (p * m + 1).ascFactorial p :=
        hrec.symm
  have hfact :
      (p * m).factorial *
          (p * m + 1).ascFactorial p =
        (p * (m + 1)).factorial := by
    simpa only [Nat.mul_add, Nat.mul_one] using
      Nat.factorial_mul_ascFactorial (p * m) p
  rw [hdnew] at hnew
  have hcancel :
      d * (p * (m + 1)) * cn =
        d * (p * (m + 1)) * (co * v) := by
    calc
      d * (p * (m + 1)) * cn =
          cn * (d * (p * (m + 1))) := by ring
      _ = (p * (m + 1)).factorial := by
        simpa only [cn, Nat.mul_assoc] using hnew
      _ =
          (p * m).factorial *
            (p * m + 1).ascFactorial p := hfact.symm
      _ =
          (co * d) * (v * (p * (m + 1))) := by
        rw [← hold, ← hv]
      _ = d * (p * (m + 1)) * (co * v) := by ring
  exact Nat.eq_of_mul_eq_mul_left (by positivity) hcancel

/-! ## Termwise decrease at successive prime blocks -/

def sylowCycleNegativeBinomialQuadraticTerm
    (p m j : ℕ) : ℝ :=
  (sylowCycleNegativeBinomialMajorant p m j : ℝ) ^ 2 /
    (primeCycleClassCard (p * m) p j : ℝ)

theorem sylowCycleNegativeBinomialQuadraticTerm_succBlock_le
    {p m j : ℕ} (hp : 2 ≤ p) (hm : 0 < m)
    (hj : 0 < j) (hjm : j ≤ m) :
    sylowCycleNegativeBinomialQuadraticTerm p (m + 1) j ≤
      sylowCycleNegativeBinomialQuadraticTerm p m j := by
  let bn :=
    sylowCycleNegativeBinomialMajorant p (m + 1) j
  let bo :=
    sylowCycleNegativeBinomialMajorant p m j
  let cn := primeCycleClassCard (p * (m + 1)) p j
  let co := primeCycleClassCard (p * m) p j
  let lower := (p * (m - j) + 1).ascFactorial p
  let upper := (p * m + 1).ascFactorial p
  let large := m + j
  have hjOld : p * j ≤ p * m :=
    Nat.mul_le_mul_left p hjm
  have hjNew : p * j ≤ p * (m + 1) :=
    hjOld.trans (Nat.mul_le_mul_left p (Nat.le_succ m))
  have hbo :
      bn * m = bo * large := by
    simpa only [bn, bo, large] using
      sylowCycleNegativeBinomialMajorant_succBlock_ratio
        (p := p) (m := m) (j := j) hm
  have hclass :
      cn * lower = co * upper := by
    simpa only [cn, co, lower, upper] using
      primeCycleClassCard_succBlock_ratio hp hj hjm
  have hratio :
      lower * large ^ 2 ≤ upper * m ^ 2 := by
    simpa only [lower, upper, large] using
      ascFactorial_succBlock_cross_square hp hj hjm
  have hscaled :
      (m ^ 2 * lower) * (bn ^ 2 * co) ≤
        (m ^ 2 * lower) * (bo ^ 2 * cn) := by
    calc
      (m ^ 2 * lower) * (bn ^ 2 * co) =
          bo ^ 2 * co * (lower * large ^ 2) := by
        calc
          (m ^ 2 * lower) * (bn ^ 2 * co) =
              (bn * m) ^ 2 * co * lower := by ring
          _ = (bo * large) ^ 2 * co * lower := by
            rw [hbo]
          _ = bo ^ 2 * co * (lower * large ^ 2) := by
            ring
      _ ≤ bo ^ 2 * co * (upper * m ^ 2) :=
        Nat.mul_le_mul_left _ hratio
      _ = (m ^ 2 * lower) * (bo ^ 2 * cn) := by
        calc
          bo ^ 2 * co * (upper * m ^ 2) =
              bo ^ 2 * m ^ 2 * (co * upper) := by ring
          _ = bo ^ 2 * m ^ 2 * (cn * lower) := by
            rw [hclass]
          _ = (m ^ 2 * lower) * (bo ^ 2 * cn) := by
            ring
  have hnat :
      bn ^ 2 * co ≤ bo ^ 2 * cn :=
    Nat.le_of_mul_le_mul_left hscaled (by
      dsimp only [lower]
      positivity)
  have hcnPos : (0 : ℝ) < cn := by
    exact_mod_cast
      primeCycleClassCard_pos hp hj hjNew
  have hcoPos : (0 : ℝ) < co := by
    exact_mod_cast
      primeCycleClassCard_pos hp hj hjOld
  change (bn : ℝ) ^ 2 / (cn : ℝ) ≤
    (bo : ℝ) ^ 2 / (co : ℝ)
  rw [div_le_div_iff₀ hcnPos hcoPos]
  exact_mod_cast hnat

/-! ## Packing the two top terms at odd primes -/

theorem sixteen_mul_factorial_le_succ_pow
    {p : ℕ} (hp : 5 ≤ p) :
    16 * p.factorial ≤ (p + 1) ^ p := by
  induction p, hp using Nat.le_induction with
  | base =>
      norm_num [Nat.factorial]
  | succ p hp ih =>
      rw [Nat.factorial_succ]
      calc
        16 * ((p + 1) * p.factorial) =
            (p + 1) * (16 * p.factorial) := by ring
        _ ≤ (p + 1) * (p + 1) ^ p :=
          Nat.mul_le_mul_left _ ih
        _ = (p + 1) ^ (p + 1) := by
          rw [pow_succ']
        _ ≤ (p + 1 + 1) ^ (p + 1) :=
          Nat.pow_le_pow_left (by omega) _

theorem sixteen_mul_factorial_le_succBlockAscFactorial
    {p m : ℕ} (hp : 5 ≤ p) (hm : 0 < m) :
    16 * p.factorial ≤
      (p * m + 1).ascFactorial p := by
  have hbase : p + 1 ≤ p * m + 1 := by
    have hpm : p ≤ p * m :=
      Nat.le_mul_of_pos_right p hm
    omega
  calc
    16 * p.factorial ≤ (p + 1) ^ p :=
      sixteen_mul_factorial_le_succ_pow hp
    _ ≤ (p * m + 1) ^ p :=
      Nat.pow_le_pow_left hbase p
    _ ≤ (p * m + 1).ascFactorial p :=
      Nat.pow_succ_le_ascFactorial _ _

theorem sixteen_mul_oldTopClassCard_le_succSameTop
    {p m : ℕ} (hp : 5 ≤ p) (hm : 0 < m) :
    16 * primeCycleClassCard (p * m) p m ≤
      primeCycleClassCard (p * (m + 1)) p m := by
  let cn := primeCycleClassCard (p * (m + 1)) p m
  let co := primeCycleClassCard (p * m) p m
  let upper := (p * m + 1).ascFactorial p
  have hclass :=
    primeCycleClassCard_succBlock_ratio
      (p := p) (m := m) (j := m) (by omega) hm (le_rfl)
  have hsixteen :
      16 * p.factorial ≤ upper := by
    simpa only [upper] using
      sixteen_mul_factorial_le_succBlockAscFactorial hp hm
  have hlower :
      (p * (m - m) + 1).ascFactorial p =
        p.factorial := by simp
  rw [hlower] at hclass
  have hscaled :
      p.factorial * (16 * co) ≤
        p.factorial * cn := by
    calc
      p.factorial * (16 * co) =
          co * (16 * p.factorial) := by ring
      _ ≤ co * upper :=
        Nat.mul_le_mul_left co hsixteen
      _ = cn * p.factorial := by
        simpa only [cn, co, upper] using hclass.symm
      _ = p.factorial * cn := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by positivity)

theorem four_mul_negativeBinomialQuadraticSameTopTerm_le_oldTop_of_five_le
    {p m : ℕ} (hp : 5 ≤ p) (hm : 0 < m) :
    4 * sylowCycleNegativeBinomialQuadraticTerm p (m + 1) m ≤
      sylowCycleNegativeBinomialQuadraticTerm p m m := by
  let bn := sylowCycleNegativeBinomialMajorant p (m + 1) m
  let bo := sylowCycleNegativeBinomialMajorant p m m
  let cn := primeCycleClassCard (p * (m + 1)) p m
  let co := primeCycleClassCard (p * m) p m
  have hbn : bn = 2 * bo := by
    simpa only [bn, bo] using
      sylowCycleNegativeBinomialMajorant_sameTop_succ
        (p := p) hm
  have hcn : 16 * co ≤ cn := by
    simpa only [cn, co] using
      sixteen_mul_oldTopClassCard_le_succSameTop hp hm
  have hcross :
      4 * bn ^ 2 * co ≤ bo ^ 2 * cn := by
    rw [hbn]
    calc
      4 * (2 * bo) ^ 2 * co =
          bo ^ 2 * (16 * co) := by ring
      _ ≤ bo ^ 2 * cn :=
        Nat.mul_le_mul_left _ hcn
  have hcnPos : (0 : ℝ) < cn := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      hm (Nat.mul_le_mul_left p (Nat.le_succ m))
  have hcoPos : (0 : ℝ) < co := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      hm (le_rfl)
  change
    4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) ≤
      (bo : ℝ) ^ 2 / (co : ℝ)
  rw [show
      4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) =
        (4 * (bn : ℝ) ^ 2) / (cn : ℝ) by ring,
    div_le_div_iff₀ hcnPos hcoPos]
  exact_mod_cast hcross

theorem sixtyFour_mul_pred_sq_le_three_mul_succBlockAscFactorial
    {p m : ℕ} (hp : 5 ≤ p) (hm : 0 < m) :
    64 * (p - 1) ^ 2 ≤
      3 * (p * m + 1).ascFactorial (p - 1) := by
  let a := p * m + 1
  let v := a.ascFactorial (p - 1)
  have ha : p + 1 ≤ a := by
    dsimp only [a]
    have hpm : p ≤ p * m :=
      Nat.le_mul_of_pos_right p hm
    omega
  have haOne : 1 ≤ a := by omega
  have hexp : 4 ≤ p - 1 := by omega
  have hpowFour :
      (p + 1) ^ 4 ≤ a ^ 4 :=
    Nat.pow_le_pow_left ha 4
  have hpowExp :
      a ^ 4 ≤ a ^ (p - 1) :=
    Nat.pow_le_pow_right haOne hexp
  have hv :
      a ^ (p - 1) ≤ v := by
    exact Nat.pow_succ_le_ascFactorial a (p - 1)
  have hpred :
      (p - 1) ^ 2 ≤ (p + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have h36 : 36 ≤ (p + 1) ^ 2 := by
    calc
      36 = (6 : ℕ) ^ 2 := by norm_num
      _ ≤ (p + 1) ^ 2 :=
        Nat.pow_le_pow_left (by omega) 2
  have h64 : 64 ≤ 3 * (p + 1) ^ 2 := by omega
  calc
    64 * (p - 1) ^ 2 ≤
        64 * (p + 1) ^ 2 :=
      Nat.mul_le_mul_left 64 hpred
    _ ≤ 3 * (p + 1) ^ 2 * (p + 1) ^ 2 := by
      exact Nat.mul_le_mul_right ((p + 1) ^ 2) h64
    _ = 3 * ((p + 1) ^ 4) := by ring
    _ ≤ 3 * (a ^ 4) :=
      Nat.mul_le_mul_left 3 hpowFour
    _ ≤ 3 * (a ^ (p - 1)) :=
      Nat.mul_le_mul_left 3 hpowExp
    _ ≤ 3 * v :=
      Nat.mul_le_mul_left 3 hv

theorem four_mul_negativeBinomialQuadraticNewTopTerm_le_three_oldTop_of_five_le
    {p m : ℕ} (hp : 5 ≤ p) (hm : 0 < m) :
    4 * sylowCycleNegativeBinomialQuadraticTerm
        p (m + 1) (m + 1) ≤
      3 * sylowCycleNegativeBinomialQuadraticTerm p m m := by
  let bn :=
    sylowCycleNegativeBinomialMajorant p (m + 1) (m + 1)
  let bo := sylowCycleNegativeBinomialMajorant p m m
  let cn := primeCycleClassCard (p * (m + 1)) p (m + 1)
  let co := primeCycleClassCard (p * m) p m
  let k := 2 * (p - 1) * (2 * m + 1)
  let v := (p * m + 1).ascFactorial (p - 1)
  have hbn :
      bn * (m + 1) = bo * k := by
    simpa only [bn, bo, k] using
      sylowCycleNegativeBinomialMajorant_newTop_ratio
        (p := p) hm
  have hcn :
      cn = co * v := by
    simpa only [cn, co, v] using
      primeCycleClassCard_newTop_ratio
        (p := p) (m := m) (by omega) hm
  have hk :
      k ≤ (m + 1) * (4 * (p - 1)) := by
    dsimp only [k]
    have hlinear : 2 * (2 * m + 1) ≤ 4 * (m + 1) := by
      omega
    calc
      2 * (p - 1) * (2 * m + 1) =
          (p - 1) * (2 * (2 * m + 1)) := by ring
      _ ≤ (p - 1) * (4 * (m + 1)) :=
        Nat.mul_le_mul_left _ hlinear
      _ = (m + 1) * (4 * (p - 1)) := by ring
  have hv :=
    sixtyFour_mul_pred_sq_le_three_mul_succBlockAscFactorial
      hp hm
  have hratio :
      4 * k ^ 2 ≤ 3 * (m + 1) ^ 2 * v := by
    calc
      4 * k ^ 2 ≤
          4 * ((m + 1) * (4 * (p - 1))) ^ 2 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hk 2)
      _ =
          (m + 1) ^ 2 * (64 * (p - 1) ^ 2) := by ring
      _ ≤ (m + 1) ^ 2 * (3 * v) :=
        Nat.mul_le_mul_left _ hv
      _ = 3 * (m + 1) ^ 2 * v := by ring
  have hscaled :
      (m + 1) ^ 2 * (4 * bn ^ 2 * co) ≤
        (m + 1) ^ 2 * (3 * bo ^ 2 * cn) := by
    calc
      (m + 1) ^ 2 * (4 * bn ^ 2 * co) =
          bo ^ 2 * co * (4 * k ^ 2) := by
        calc
          (m + 1) ^ 2 * (4 * bn ^ 2 * co) =
              4 * (bn * (m + 1)) ^ 2 * co := by ring
          _ = 4 * (bo * k) ^ 2 * co := by
            rw [hbn]
          _ = bo ^ 2 * co * (4 * k ^ 2) := by ring
      _ ≤ bo ^ 2 * co * (3 * (m + 1) ^ 2 * v) :=
        Nat.mul_le_mul_left _ hratio
      _ = (m + 1) ^ 2 * (3 * bo ^ 2 * cn) := by
        rw [hcn]
        ring
  have hcross :
      4 * bn ^ 2 * co ≤ 3 * bo ^ 2 * cn :=
    Nat.le_of_mul_le_mul_left hscaled (by positivity)
  have hcnPos : (0 : ℝ) < cn := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m + 1) (le_rfl)
  have hcoPos : (0 : ℝ) < co := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      hm (le_rfl)
  change
    4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) ≤
      3 * ((bo : ℝ) ^ 2 / (co : ℝ))
  rw [show
      4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) =
        (4 * (bn : ℝ) ^ 2) / (cn : ℝ) by ring,
    show
      3 * ((bo : ℝ) ^ 2 / (co : ℝ)) =
        (3 * (bo : ℝ) ^ 2) / (co : ℝ) by ring,
    div_le_div_iff₀ hcnPos hcoPos]
  exact_mod_cast hcross

theorem sixteen_mul_oldTopClassCard_le_succSameTop_three
    {m : ℕ} (hm : 3 ≤ m) :
    16 * primeCycleClassCard (3 * m) 3 m ≤
      primeCycleClassCard (3 * (m + 1)) 3 m := by
  let cn := primeCycleClassCard (3 * (m + 1)) 3 m
  let co := primeCycleClassCard (3 * m) 3 m
  let upper := (3 * m + 1).ascFactorial 3
  have hclass :=
    primeCycleClassCard_succBlock_ratio
      (p := 3) (m := m) (j := m)
        (by omega) (by omega) (le_rfl)
  have hupper : 96 ≤ upper := by
    calc
      96 ≤ 4 * 5 * 6 := by norm_num
      _ ≤ (3 * m + 1) * (3 * m + 2) * (3 * m + 3) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (by omega) (by omega)) (by omega)
      _ = upper := by
        simp only [upper, Nat.ascFactorial_succ,
          Nat.ascFactorial_zero, Nat.mul_one]
        ring
  have hlower :
      (3 * (m - m) + 1).ascFactorial 3 = 6 := by
    norm_num [Nat.ascFactorial_succ]
  rw [hlower] at hclass
  have hscaled :
      6 * (16 * co) ≤ 6 * cn := by
    calc
      6 * (16 * co) = co * 96 := by ring
      _ ≤ co * upper :=
        Nat.mul_le_mul_left co hupper
      _ = cn * 6 := by
        simpa only [cn, co, upper] using hclass.symm
      _ = 6 * cn := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)

theorem four_mul_negativeBinomialQuadraticSameTopTerm_le_oldTop_three
    {m : ℕ} (hm : 3 ≤ m) :
    4 * sylowCycleNegativeBinomialQuadraticTerm 3 (m + 1) m ≤
      sylowCycleNegativeBinomialQuadraticTerm 3 m m := by
  let bn := sylowCycleNegativeBinomialMajorant 3 (m + 1) m
  let bo := sylowCycleNegativeBinomialMajorant 3 m m
  let cn := primeCycleClassCard (3 * (m + 1)) 3 m
  let co := primeCycleClassCard (3 * m) 3 m
  have hbn : bn = 2 * bo := by
    simpa only [bn, bo] using
      sylowCycleNegativeBinomialMajorant_sameTop_succ
        (p := 3) (by omega : 0 < m)
  have hcn : 16 * co ≤ cn := by
    simpa only [cn, co] using
      sixteen_mul_oldTopClassCard_le_succSameTop_three hm
  have hcross :
      4 * bn ^ 2 * co ≤ bo ^ 2 * cn := by
    rw [hbn]
    calc
      4 * (2 * bo) ^ 2 * co =
          bo ^ 2 * (16 * co) := by ring
      _ ≤ bo ^ 2 * cn :=
        Nat.mul_le_mul_left _ hcn
  have hcnPos : (0 : ℝ) < cn := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m)
      (Nat.mul_le_mul_left 3 (Nat.le_succ m))
  have hcoPos : (0 : ℝ) < co := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m) (le_rfl)
  change
    4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) ≤
      (bo : ℝ) ^ 2 / (co : ℝ)
  rw [show
      4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) =
        (4 * (bn : ℝ) ^ 2) / (cn : ℝ) by ring,
    div_le_div_iff₀ hcnPos hcoPos]
  exact_mod_cast hcross

theorem four_mul_negativeBinomialQuadraticNewTopTerm_le_three_oldTop_three
    {m : ℕ} (hm : 3 ≤ m) :
    4 * sylowCycleNegativeBinomialQuadraticTerm
        3 (m + 1) (m + 1) ≤
      3 * sylowCycleNegativeBinomialQuadraticTerm 3 m m := by
  let bn :=
    sylowCycleNegativeBinomialMajorant 3 (m + 1) (m + 1)
  let bo := sylowCycleNegativeBinomialMajorant 3 m m
  let cn := primeCycleClassCard (3 * (m + 1)) 3 (m + 1)
  let co := primeCycleClassCard (3 * m) 3 m
  let k := 4 * (2 * m + 1)
  let v := (3 * m + 1).ascFactorial 2
  have hbn :
      bn * (m + 1) = bo * k := by
    simpa only [bn, bo, k] using
      sylowCycleNegativeBinomialMajorant_newTop_ratio
        (p := 3) (by omega : 0 < m)
  have hcn :
      cn = co * v := by
    simpa only [cn, co, v] using
      primeCycleClassCard_newTop_ratio
        (p := 3) (m := m) (by norm_num) (by omega)
  have hk :
      k ≤ (m + 1) * 8 := by
    dsimp only [k]
    omega
  have hv : 256 ≤ 3 * v := by
    have hbase :
        10 * 11 ≤ (3 * m + 1) * (3 * m + 2) :=
      Nat.mul_le_mul (by omega) (by omega)
    calc
      256 ≤ 3 * (10 * 11) := by norm_num
      _ ≤ 3 * ((3 * m + 1) * (3 * m + 2)) :=
        Nat.mul_le_mul_left 3 hbase
      _ = 3 * v := by
        simp only [v, Nat.ascFactorial_succ,
          Nat.ascFactorial_zero, Nat.mul_one]
        ring
  have hratio :
      4 * k ^ 2 ≤ 3 * (m + 1) ^ 2 * v := by
    calc
      4 * k ^ 2 ≤ 4 * ((m + 1) * 8) ^ 2 :=
        Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hk 2)
      _ = (m + 1) ^ 2 * 256 := by ring
      _ ≤ (m + 1) ^ 2 * (3 * v) :=
        Nat.mul_le_mul_left _ hv
      _ = 3 * (m + 1) ^ 2 * v := by ring
  have hscaled :
      (m + 1) ^ 2 * (4 * bn ^ 2 * co) ≤
        (m + 1) ^ 2 * (3 * bo ^ 2 * cn) := by
    calc
      (m + 1) ^ 2 * (4 * bn ^ 2 * co) =
          bo ^ 2 * co * (4 * k ^ 2) := by
        calc
          (m + 1) ^ 2 * (4 * bn ^ 2 * co) =
              4 * (bn * (m + 1)) ^ 2 * co := by ring
          _ = 4 * (bo * k) ^ 2 * co := by rw [hbn]
          _ = bo ^ 2 * co * (4 * k ^ 2) := by ring
      _ ≤ bo ^ 2 * co * (3 * (m + 1) ^ 2 * v) :=
        Nat.mul_le_mul_left _ hratio
      _ = (m + 1) ^ 2 * (3 * bo ^ 2 * cn) := by
        rw [hcn]
        ring
  have hcross :
      4 * bn ^ 2 * co ≤ 3 * bo ^ 2 * cn :=
    Nat.le_of_mul_le_mul_left hscaled (by positivity)
  have hcnPos : (0 : ℝ) < cn := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m + 1) (le_rfl)
  have hcoPos : (0 : ℝ) < co := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m) (le_rfl)
  change
    4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) ≤
      3 * ((bo : ℝ) ^ 2 / (co : ℝ))
  rw [show
      4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) =
        (4 * (bn : ℝ) ^ 2) / (cn : ℝ) by ring,
    show
      3 * ((bo : ℝ) ^ 2 / (co : ℝ)) =
        (3 * (bo : ℝ) ^ 2) / (co : ℝ) by ring,
    div_le_div_iff₀ hcnPos hcoPos]
  exact_mod_cast hcross

theorem sylowCycleNegativeBinomialQuadraticCost_succBlock_le_of_top_pack
    {p m : ℕ} (hp : 2 ≤ p) (hm : 0 < m)
    (hsame :
      4 * sylowCycleNegativeBinomialQuadraticTerm p (m + 1) m ≤
        sylowCycleNegativeBinomialQuadraticTerm p m m)
    (hnew :
      4 * sylowCycleNegativeBinomialQuadraticTerm
          p (m + 1) (m + 1) ≤
        3 * sylowCycleNegativeBinomialQuadraticTerm p m m) :
    sylowCycleNegativeBinomialQuadraticCost (p * (m + 1)) p ≤
      sylowCycleNegativeBinomialQuadraticCost (p * m) p := by
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero hm.ne'
  let fNew : ℕ → ℝ := fun j ↦
    sylowCycleNegativeBinomialQuadraticTerm p (r + 2) j
  let fOld : ℕ → ℝ := fun j ↦
    sylowCycleNegativeBinomialQuadraticTerm p (r + 1) j
  have hcore :
      (∑ j ∈ Finset.Icc 1 r, fNew j) ≤
        ∑ j ∈ Finset.Icc 1 r, fOld j := by
    apply Finset.sum_le_sum
    intro j hjMem
    have hj : 0 < j := (Finset.mem_Icc.mp hjMem).1
    have hjm : j ≤ r + 1 := by
      exact (Finset.mem_Icc.mp hjMem).2.trans
        (Nat.le_succ r)
    simpa only [fNew, fOld] using
      sylowCycleNegativeBinomialQuadraticTerm_succBlock_le
        hp (by omega : 0 < r + 1) hj hjm
  have hpair :
      fNew (r + 1) + fNew (r + 2) ≤
        fOld (r + 1) := by
    have hsame' :
        4 * fNew (r + 1) ≤ fOld (r + 1) := by
      simpa only [fNew, fOld] using hsame
    have hnew' :
        4 * fNew (r + 2) ≤ 3 * fOld (r + 1) := by
      simpa only [fNew, fOld] using hnew
    linarith
  have hsplitNewTop :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := r + 1)
      (by omega : 1 ≤ r + 1 + 1) fNew
  have hsplitNewSame :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := r)
      (by omega : 1 ≤ r + 1) fNew
  have hsplitOld :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := r)
      (by omega : 1 ≤ r + 1) fOld
  rw [sylowCycleNegativeBinomialQuadraticCost,
    sylowCycleNegativeBinomialQuadraticCost]
  rw [Nat.mul_div_cancel_left (r.succ + 1) (by omega : 0 < p),
    Nat.mul_div_cancel_left r.succ (by omega : 0 < p)]
  change (∑ j ∈ Finset.Icc 1 (r + 2), fNew j) ≤
    ∑ j ∈ Finset.Icc 1 (r + 1), fOld j
  rw [hsplitNewTop, hsplitNewSame, hsplitOld]
  linarith

theorem sylowCycleNegativeBinomialQuadraticCost_succBlock_le_of_five_le
    {p m : ℕ} (hp : 5 ≤ p) (hm : 0 < m) :
    sylowCycleNegativeBinomialQuadraticCost (p * (m + 1)) p ≤
      sylowCycleNegativeBinomialQuadraticCost (p * m) p :=
  sylowCycleNegativeBinomialQuadraticCost_succBlock_le_of_top_pack
    (by omega) hm
    (four_mul_negativeBinomialQuadraticSameTopTerm_le_oldTop_of_five_le
      hp hm)
    (four_mul_negativeBinomialQuadraticNewTopTerm_le_three_oldTop_of_five_le
      hp hm)

theorem sylowCycleNegativeBinomialQuadraticCost_succBlock_le_three
    {m : ℕ} (hm : 3 ≤ m) :
    sylowCycleNegativeBinomialQuadraticCost (3 * (m + 1)) 3 ≤
      sylowCycleNegativeBinomialQuadraticCost (3 * m) 3 :=
  sylowCycleNegativeBinomialQuadraticCost_succBlock_le_of_top_pack
    (by norm_num) (by omega)
    (four_mul_negativeBinomialQuadraticSameTopTerm_le_oldTop_three hm)
    (four_mul_negativeBinomialQuadraticNewTopTerm_le_three_oldTop_three hm)

theorem sylowCycleNegativeBinomialQuadraticCost_mul_le_of_five_le
    {p a m : ℕ} (hp : 5 ≤ p) (ha : 0 < a) (hm : a ≤ m) :
    sylowCycleNegativeBinomialQuadraticCost (p * m) p ≤
      sylowCycleNegativeBinomialQuadraticCost (p * a) p := by
  induction m, hm using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ m hm ih =>
      exact
        (sylowCycleNegativeBinomialQuadraticCost_succBlock_le_of_five_le
          hp (ha.trans_le hm)).trans ih

theorem sylowCycleNegativeBinomialQuadraticCost_mul_le_three
    {a m : ℕ} (ha : 3 ≤ a) (hm : a ≤ m) :
    sylowCycleNegativeBinomialQuadraticCost (3 * m) 3 ≤
      sylowCycleNegativeBinomialQuadraticCost (3 * a) 3 := by
  induction m, hm using Nat.le_induction with
  | base =>
      exact le_rfl
  | succ m hm ih =>
      exact
        (sylowCycleNegativeBinomialQuadraticCost_succBlock_le_three
          (ha.trans hm)).trans ih

/-! ## The binary even-row two-block step -/

theorem sixteen_mul_oldTopClassCard_le_succSameTop_two
    {m : ℕ} (hm : 8 ≤ m) :
    16 * primeCycleClassCard (2 * m) 2 m ≤
      primeCycleClassCard (2 * (m + 1)) 2 m := by
  let cn := primeCycleClassCard (2 * (m + 1)) 2 m
  let co := primeCycleClassCard (2 * m) 2 m
  let upper := (2 * m + 1).ascFactorial 2
  have hclass :=
    primeCycleClassCard_succBlock_ratio
      (p := 2) (m := m) (j := m)
        (by omega) (by omega) (le_rfl)
  have hupper : 32 ≤ upper := by
    calc
      32 ≤ 17 * 18 := by norm_num
      _ ≤ (2 * m + 1) * (2 * m + 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      _ = upper := by
        simp only [upper, Nat.ascFactorial_succ,
          Nat.ascFactorial_zero, Nat.mul_one]
        ring
  have hlower :
      (2 * (m - m) + 1).ascFactorial 2 = 2 := by
    norm_num [Nat.ascFactorial_succ]
  rw [hlower] at hclass
  have hscaled :
      2 * (16 * co) ≤ 2 * cn := by
    calc
      2 * (16 * co) = co * 32 := by ring
      _ ≤ co * upper :=
        Nat.mul_le_mul_left co hupper
      _ = cn * 2 := by
        simpa only [cn, co, upper] using hclass.symm
      _ = 2 * cn := by ring
  exact Nat.le_of_mul_le_mul_left hscaled (by norm_num)

theorem four_mul_negativeBinomialQuadraticSameTopTerm_le_oldTop_two
    {m : ℕ} (hm : 8 ≤ m) :
    4 * sylowCycleNegativeBinomialQuadraticTerm 2 (m + 1) m ≤
      sylowCycleNegativeBinomialQuadraticTerm 2 m m := by
  let bn := sylowCycleNegativeBinomialMajorant 2 (m + 1) m
  let bo := sylowCycleNegativeBinomialMajorant 2 m m
  let cn := primeCycleClassCard (2 * (m + 1)) 2 m
  let co := primeCycleClassCard (2 * m) 2 m
  have hbn : bn = 2 * bo := by
    simpa only [bn, bo] using
      sylowCycleNegativeBinomialMajorant_sameTop_succ
        (p := 2) (by omega : 0 < m)
  have hcn : 16 * co ≤ cn := by
    simpa only [cn, co] using
      sixteen_mul_oldTopClassCard_le_succSameTop_two hm
  have hcross :
      4 * bn ^ 2 * co ≤ bo ^ 2 * cn := by
    rw [hbn]
    calc
      4 * (2 * bo) ^ 2 * co =
          bo ^ 2 * (16 * co) := by ring
      _ ≤ bo ^ 2 * cn :=
        Nat.mul_le_mul_left _ hcn
  have hcnPos : (0 : ℝ) < cn := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m)
      (Nat.mul_le_mul_left 2 (Nat.le_succ m))
  have hcoPos : (0 : ℝ) < co := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m) (le_rfl)
  change
    4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) ≤
      (bo : ℝ) ^ 2 / (co : ℝ)
  rw [show
      4 * ((bn : ℝ) ^ 2 / (cn : ℝ)) =
        (4 * (bn : ℝ) ^ 2) / (cn : ℝ) by ring,
    div_le_div_iff₀ hcnPos hcoPos]
  exact_mod_cast hcross

theorem four_mul_negativeBinomialQuadraticTwoStepNewTopTerm_le_three_oldTop
    {m : ℕ} (hm : 8 ≤ m) :
    4 * sylowCycleNegativeBinomialQuadraticTerm
        2 (m + 2) (m + 2) ≤
      3 * sylowCycleNegativeBinomialQuadraticTerm 2 m m := by
  let b₀ := sylowCycleNegativeBinomialMajorant 2 m m
  let b₁ := sylowCycleNegativeBinomialMajorant 2 (m + 1) (m + 1)
  let b₂ := sylowCycleNegativeBinomialMajorant 2 (m + 2) (m + 2)
  let c₀ := primeCycleClassCard (2 * m) 2 m
  let c₁ := primeCycleClassCard (2 * (m + 1)) 2 (m + 1)
  let c₂ := primeCycleClassCard (2 * (m + 2)) 2 (m + 2)
  let d := (m + 1) * (m + 2)
  let v := (2 * m + 1) * (2 * m + 3)
  have hb₁ :
      b₁ * (m + 1) = b₀ * (2 * (2 * m + 1)) := by
    simpa only [b₁, b₀] using
      sylowCycleNegativeBinomialMajorant_newTop_ratio
        (p := 2) (by omega : 0 < m)
  have hb₂ :
      b₂ * (m + 2) = b₁ * (2 * (2 * m + 3)) := by
    simpa only [b₂, b₁, show 2 * (m + 1) + 1 = 2 * m + 3 by omega]
      using
        sylowCycleNegativeBinomialMajorant_newTop_ratio
          (p := 2) (m := m + 1) (by omega)
  have hb :
      b₂ * d = b₀ * (4 * v) := by
    calc
      b₂ * d = (b₂ * (m + 2)) * (m + 1) := by
        simp only [d]
        ring
      _ = (b₁ * (2 * (2 * m + 3))) * (m + 1) := by
        rw [hb₂]
      _ = (b₁ * (m + 1)) * (2 * (2 * m + 3)) := by
        ring
      _ = (b₀ * (2 * (2 * m + 1))) *
          (2 * (2 * m + 3)) := by rw [hb₁]
      _ = b₀ * (4 * v) := by
        simp only [v]
        ring
  have hc₁ :
      c₁ = c₀ * (2 * m + 1) := by
    simpa only [c₁, c₀, Nat.ascFactorial_succ,
      Nat.ascFactorial_zero, Nat.mul_one] using
      primeCycleClassCard_newTop_ratio
        (p := 2) (m := m) (by norm_num) (by omega)
  have hc₂ :
      c₂ = c₁ * (2 * m + 3) := by
    simpa only [c₂, c₁,
      show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
      Nat.ascFactorial_succ, Nat.ascFactorial_zero,
      Nat.mul_one] using
      primeCycleClassCard_newTop_ratio
        (p := 2) (m := m + 1) (by norm_num) (by omega)
  have hc :
      c₂ = c₀ * v := by
    rw [hc₂, hc₁]
    simp only [v]
    ring
  have hv :
      64 * v ≤ 3 * d ^ 2 := by
    have hfirst : 2 * m + 1 ≤ 2 * (m + 1) := by omega
    have hsecond : 2 * m + 3 ≤ 2 * (m + 2) := by omega
    have hprod :
        v ≤ 4 * d := by
      dsimp only [v, d]
      calc
        (2 * m + 1) * (2 * m + 3) ≤
            (2 * (m + 1)) * (2 * (m + 2)) :=
          Nat.mul_le_mul hfirst hsecond
        _ = 4 * ((m + 1) * (m + 2)) := by ring
    have hbase : 256 ≤ 3 * d := by
      dsimp only [d]
      have hmul :
          9 * 10 ≤ (m + 1) * (m + 2) :=
        Nat.mul_le_mul (by omega) (by omega)
      omega
    calc
      64 * v ≤ 64 * (4 * d) :=
        Nat.mul_le_mul_left 64 hprod
      _ = 256 * d := by ring
      _ ≤ (3 * d) * d :=
        Nat.mul_le_mul_right d hbase
      _ = 3 * d ^ 2 := by ring
  have hratio :
      4 * (4 * v) ^ 2 ≤ 3 * d ^ 2 * v := by
    calc
      4 * (4 * v) ^ 2 = (64 * v) * v := by ring
      _ ≤ (3 * d ^ 2) * v :=
        Nat.mul_le_mul_right v hv
      _ = 3 * d ^ 2 * v := by ring
  have hscaled :
      d ^ 2 * (4 * b₂ ^ 2 * c₀) ≤
        d ^ 2 * (3 * b₀ ^ 2 * c₂) := by
    calc
      d ^ 2 * (4 * b₂ ^ 2 * c₀) =
          b₀ ^ 2 * c₀ * (4 * (4 * v) ^ 2) := by
        calc
          d ^ 2 * (4 * b₂ ^ 2 * c₀) =
              4 * (b₂ * d) ^ 2 * c₀ := by ring
          _ = 4 * (b₀ * (4 * v)) ^ 2 * c₀ := by
            rw [hb]
          _ = b₀ ^ 2 * c₀ * (4 * (4 * v) ^ 2) := by ring
      _ ≤ b₀ ^ 2 * c₀ * (3 * d ^ 2 * v) :=
        Nat.mul_le_mul_left _ hratio
      _ = d ^ 2 * (3 * b₀ ^ 2 * c₂) := by
        rw [hc]
        ring
  have hcross :
      4 * b₂ ^ 2 * c₀ ≤ 3 * b₀ ^ 2 * c₂ :=
    Nat.le_of_mul_le_mul_left hscaled (by
      dsimp only [d]
      positivity)
  have hc₂Pos : (0 : ℝ) < c₂ := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m + 2) (le_rfl)
  have hc₀Pos : (0 : ℝ) < c₀ := by
    exact_mod_cast primeCycleClassCard_pos (by omega)
      (by omega : 0 < m) (le_rfl)
  change
    4 * ((b₂ : ℝ) ^ 2 / (c₂ : ℝ)) ≤
      3 * ((b₀ : ℝ) ^ 2 / (c₀ : ℝ))
  rw [show
      4 * ((b₂ : ℝ) ^ 2 / (c₂ : ℝ)) =
        (4 * (b₂ : ℝ) ^ 2) / (c₂ : ℝ) by ring,
    show
      3 * ((b₀ : ℝ) ^ 2 / (c₀ : ℝ)) =
        (3 * (b₀ : ℝ) ^ 2) / (c₀ : ℝ) by ring,
    div_le_div_iff₀ hc₂Pos hc₀Pos]
  exact_mod_cast hcross

theorem sylowCycleNegativeBinomialEvenQuadraticCost_twoStep_le
    {m : ℕ} (hm : 8 ≤ m) (heven : Even m) :
    sylowCycleNegativeBinomialEvenQuadraticCost (2 * (m + 2)) ≤
      sylowCycleNegativeBinomialEvenQuadraticCost (2 * m) := by
  obtain ⟨r, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  let fNew : ℕ → ℝ := fun j ↦
    if Even j then
      sylowCycleNegativeBinomialQuadraticTerm 2 (r + 3) j
    else 0
  let fOld : ℕ → ℝ := fun j ↦
    if Even j then
      sylowCycleNegativeBinomialQuadraticTerm 2 (r + 1) j
    else 0
  have hm8 : 8 ≤ r + 1 := by omega
  have hmPos : 0 < r + 1 := by omega
  have hevenM : Even (r + 1) := heven
  have hoddNext : ¬Even (r + 2) := by
    intro hevenNext
    rcases hevenM with ⟨a, ha⟩
    rcases hevenNext with ⟨b, hb⟩
    omega
  have hevenNextTwo : Even (r + 3) := by
    rcases hevenM with ⟨a, ha⟩
    refine ⟨a + 1, ?_⟩
    omega
  have hcore :
      (∑ j ∈ Finset.Icc 1 r, fNew j) ≤
        ∑ j ∈ Finset.Icc 1 r, fOld j := by
    apply Finset.sum_le_sum
    intro j hjMem
    by_cases hjEven : Even j
    · simp only [fNew, fOld, if_pos hjEven]
      have hj : 0 < j := (Finset.mem_Icc.mp hjMem).1
      have hjm : j ≤ r + 1 := by
        exact (Finset.mem_Icc.mp hjMem).2.trans
          (Nat.le_succ r)
      exact
        (sylowCycleNegativeBinomialQuadraticTerm_succBlock_le
          (p := 2) (m := r + 2) (j := j)
          (by omega) (by omega) hj (by omega)).trans
        (sylowCycleNegativeBinomialQuadraticTerm_succBlock_le
          (p := 2) (m := r + 1) (j := j)
          (by omega) hmPos hj hjm)
    · simp [fNew, fOld, hjEven]
  have hsame :
      4 * fNew (r + 1) ≤ fOld (r + 1) := by
    simp only [fNew, fOld, if_pos hevenM]
    have hdec :
        sylowCycleNegativeBinomialQuadraticTerm
            2 (r + 3) (r + 1) ≤
          sylowCycleNegativeBinomialQuadraticTerm
            2 (r + 2) (r + 1) :=
      sylowCycleNegativeBinomialQuadraticTerm_succBlock_le
        (p := 2) (m := r + 2) (j := r + 1)
        (by omega) (by omega) (by omega) (by omega)
    have hpack :=
      four_mul_negativeBinomialQuadraticSameTopTerm_le_oldTop_two
        (m := r + 1) hm8
    nlinarith
  have hmiddle :
      fNew (r + 2) = 0 := by
    simp [fNew, hoddNext]
  have htop :
      4 * fNew (r + 3) ≤ 3 * fOld (r + 1) := by
    simp only [fNew, fOld, if_pos hevenNextTwo, if_pos hevenM]
    exact
      four_mul_negativeBinomialQuadraticTwoStepNewTopTerm_le_three_oldTop
        (m := r + 1) hm8
  have hpair :
      fNew (r + 1) + fNew (r + 2) + fNew (r + 3) ≤
        fOld (r + 1) := by
    rw [hmiddle, add_zero]
    linarith
  have hsplitNewTop :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := r + 2)
      (by omega : 1 ≤ r + 2 + 1) fNew
  have hsplitNewMiddle :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := r + 1)
      (by omega : 1 ≤ r + 1 + 1) fNew
  have hsplitNewSame :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := r)
      (by omega : 1 ≤ r + 1) fNew
  have hsplitOld :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := r)
      (by omega : 1 ≤ r + 1) fOld
  rw [sylowCycleNegativeBinomialEvenQuadraticCost,
    sylowCycleNegativeBinomialEvenQuadraticCost]
  rw [Nat.mul_div_cancel_left (r + 1 + 2) (by norm_num : 0 < 2),
    Nat.mul_div_cancel_left (r + 1) (by norm_num : 0 < 2)]
  change (∑ j ∈ Finset.Icc 1 (r + 3), fNew j) ≤
    ∑ j ∈ Finset.Icc 1 (r + 1), fOld j
  rw [hsplitNewTop, hsplitNewMiddle,
    hsplitNewSame, hsplitOld]
  linarith

theorem sylowCycleNegativeBinomialEvenQuadraticCost_succBlock_le_of_not_even
    {m : ℕ} (hm : 0 < m) (hnewOdd : ¬Even (m + 1)) :
    sylowCycleNegativeBinomialEvenQuadraticCost (2 * (m + 1)) ≤
      sylowCycleNegativeBinomialEvenQuadraticCost (2 * m) := by
  let fNew : ℕ → ℝ := fun j ↦
    if Even j then
      sylowCycleNegativeBinomialQuadraticTerm 2 (m + 1) j
    else 0
  let fOld : ℕ → ℝ := fun j ↦
    if Even j then
      sylowCycleNegativeBinomialQuadraticTerm 2 m j
    else 0
  have hcore :
      (∑ j ∈ Finset.Icc 1 m, fNew j) ≤
        ∑ j ∈ Finset.Icc 1 m, fOld j := by
    apply Finset.sum_le_sum
    intro j hjMem
    by_cases hjEven : Even j
    · simp only [fNew, fOld, if_pos hjEven]
      exact
        sylowCycleNegativeBinomialQuadraticTerm_succBlock_le
          (p := 2) (m := m) (j := j)
          (by omega) hm
          (Finset.mem_Icc.mp hjMem).1
          (Finset.mem_Icc.mp hjMem).2
    · simp [fNew, fOld, hjEven]
  have htop : fNew (m + 1) = 0 := by
    simp [fNew, hnewOdd]
  have hsplit :=
    Finset.sum_Icc_succ_top
      (M := ℝ) (a := 1) (b := m)
      (by omega : 1 ≤ m + 1) fNew
  rw [sylowCycleNegativeBinomialEvenQuadraticCost,
    sylowCycleNegativeBinomialEvenQuadraticCost]
  rw [Nat.mul_div_cancel_left (m + 1) (by norm_num : 0 < 2),
    Nat.mul_div_cancel_left m (by norm_num : 0 < 2)]
  change (∑ j ∈ Finset.Icc 1 (m + 1), fNew j) ≤
    ∑ j ∈ Finset.Icc 1 m, fOld j
  rw [hsplit, htop, add_zero]
  exact hcore

theorem sylowCycleNegativeBinomialEvenQuadraticCost_mul_le_twenty
    {m : ℕ} (hm : 20 ≤ m) :
    sylowCycleNegativeBinomialEvenQuadraticCost (2 * m) ≤
      sylowCycleNegativeBinomialEvenQuadraticCost 40 := by
  by_cases heven : Even m
  · rcases heven with ⟨a, ha⟩
    have haTen : 10 ≤ a := by omega
    let k := a - 10
    have hk : m = 20 + 2 * k := by
      dsimp only [k]
      omega
    rw [hk]
    induction k with
    | zero =>
        norm_num
    | succ k ih =>
        have hstep :=
          sylowCycleNegativeBinomialEvenQuadraticCost_twoStep_le
            (m := 20 + 2 * k) (by omega)
            (by
              refine ⟨10 + k, ?_⟩
              omega)
        simpa only [Nat.mul_add, Nat.mul_one,
          Nat.succ_eq_add_one] using hstep.trans ih
  · have hodd : Odd m :=
      Nat.not_even_iff_odd.mp heven
    rcases hodd with ⟨a, ha⟩
    have haTen : 10 ≤ a := by omega
    have hmEq : m = (2 * a) + 1 := by omega
    rw [hmEq]
    have hfirst :=
      sylowCycleNegativeBinomialEvenQuadraticCost_succBlock_le_of_not_even
        (m := 2 * a) (by omega)
        (by
          intro h
          rcases h with ⟨b, hb⟩
          omega)
    have htail :=
      sylowCycleNegativeBinomialEvenQuadraticCost_mul_le_twenty
        (m := 2 * a) (by omega)
    exact hfirst.trans htail
termination_by m

/-! ## Exact rational anchors -/

theorem sylowCycleNegativeBinomialEvenQuadraticCost_forty_lt :
    sylowCycleNegativeBinomialEvenQuadraticCost 40 <
      (3 : ℝ) / 16 := by
  have hIcc : Finset.Icc 1 20 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10,
        11, 12, 13, 14, 15, 16, 17, 18, 19, 20} := by
    decide
  rw [sylowCycleNegativeBinomialEvenQuadraticCost, hIcc]
  norm_num [
    sylowCycleNegativeBinomialMajorant, Nat.multichoose,
    primeCycleClassCard, Nat.factorial, even_iff_two_dvd]

theorem sylowCycleNegativeBinomialQuadraticCost_three_thirtyNine_lt :
    sylowCycleNegativeBinomialQuadraticCost 39 3 <
      (1 : ℝ) / 25 := by
  have hIcc : Finset.Icc 1 13 =
      {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} := by
    decide
  rw [sylowCycleNegativeBinomialQuadraticCost, hIcc]
  norm_num [sylowCycleNegativeBinomialMajorant,
    Nat.multichoose, primeCycleClassCard, Nat.factorial]

theorem sylowCycleNegativeBinomialQuadraticCost_five_forty_lt :
    sylowCycleNegativeBinomialQuadraticCost 40 5 <
      (1 : ℝ) / 10000 := by
  have hIcc : Finset.Icc 1 8 =
      {1, 2, 3, 4, 5, 6, 7, 8} := by
    decide
  rw [sylowCycleNegativeBinomialQuadraticCost, hIcc]
  norm_num [sylowCycleNegativeBinomialMajorant,
    Nat.multichoose, primeCycleClassCard, Nat.factorial]

theorem sylowCycleNegativeBinomialQuadraticCost_seven_thirtyFive_lt :
    sylowCycleNegativeBinomialQuadraticCost 35 7 <
      (1 : ℝ) / 2400 := by
  have hIcc : Finset.Icc 1 5 =
      {1, 2, 3, 4, 5} := by
    decide
  rw [sylowCycleNegativeBinomialQuadraticCost, hIcc]
  norm_num [sylowCycleNegativeBinomialMajorant,
    Nat.multichoose, primeCycleClassCard, Nat.factorial]

/-! ## The uniform prime tail -/

theorem sylowCycleNegativeBinomialQuadraticCost_self
    {p : ℕ} (hp : 2 ≤ p) :
    sylowCycleNegativeBinomialQuadraticCost p p =
      ((p - 1 : ℕ) : ℝ) ^ 2 /
        ((p - 1).factorial : ℝ) := by
  rw [sylowCycleNegativeBinomialQuadraticCost,
    Nat.div_self (by omega : 0 < p)]
  simp [sylowCycleNegativeBinomialMajorant,
    primeCycleClassCard]
  obtain ⟨k, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : p ≠ 0)
  simp [Nat.factorial_succ]

theorem two_pow_mul_square_le_factorial
    {m : ℕ} (hm : 10 ≤ m) :
    2 ^ (m + 1) * m ^ 2 ≤ m.factorial := by
  induction m, hm using Nat.le_induction with
  | base =>
      norm_num [Nat.factorial]
  | succ m hm ih =>
      have hratio : 2 * (m + 1) ≤ m ^ 2 := by
        nlinarith
      have hratioSq :
          2 * (m + 1) ^ 2 ≤ (m + 1) * m ^ 2 := by
        calc
          2 * (m + 1) ^ 2 =
              (m + 1) * (2 * (m + 1)) := by ring
          _ ≤ (m + 1) * m ^ 2 :=
            Nat.mul_le_mul_left _ hratio
      rw [Nat.factorial_succ]
      calc
        2 ^ (m + 1 + 1) * (m + 1) ^ 2 =
            2 ^ (m + 1) * (2 * (m + 1) ^ 2) := by
          rw [pow_succ]
          ring
        _ ≤
            2 ^ (m + 1) * ((m + 1) * m ^ 2) :=
          Nat.mul_le_mul_left _ hratioSq
        _ =
            (m + 1) * (2 ^ (m + 1) * m ^ 2) := by ring
        _ ≤ (m + 1) * m.factorial :=
          Nat.mul_le_mul_left _ ih

theorem sylowCycleNegativeBinomialQuadraticCost_self_le_inverseTwoPow
    {p : ℕ} (hp : 11 ≤ p) :
    sylowCycleNegativeBinomialQuadraticCost p p ≤
      (2 : ℝ)⁻¹ ^ p := by
  rw [sylowCycleNegativeBinomialQuadraticCost_self
      (by omega),
    inv_pow, ← one_div]
  have hfac :
      (0 : ℝ) < ((p - 1).factorial : ℝ) := by
    positivity
  have htwo : (0 : ℝ) < (2 : ℝ) ^ p := by
    positivity
  rw [div_le_div_iff₀ hfac htwo]
  have hnat :=
    two_pow_mul_square_le_factorial
      (m := p - 1) (by omega)
  have hpSucc : p - 1 + 1 = p := by omega
  rw [hpSucc] at hnat
  exact_mod_cast (by simpa [mul_comm] using hnat)

/-! ## A pointwise prime envelope from degree forty onward -/

def alternatingQuadraticPrimeEnvelope (p : ℕ) : ℝ :=
  if p = 2 then 3 / 16
  else if p = 3 then 1 / 25
  else if p = 5 then 1 / 10000
  else if p = 7 then 1 / 2400
  else (2 : ℝ)⁻¹ ^ p

theorem alternatingQuadraticPrimeEnvelope_pos
    (p : ℕ) :
    0 < alternatingQuadraticPrimeEnvelope p := by
  simp only [alternatingQuadraticPrimeEnvelope]
  split_ifs <;> positivity

theorem alternatingSylowProfileQuadraticCost_le_primeEnvelope
    {n p : ℕ} (hn : 40 ≤ n) (hp : p.Prime) :
    alternatingSylowProfileQuadraticCost n p ≤
      alternatingQuadraticPrimeEnvelope p := by
  by_cases hpn : p ≤ n
  · by_cases hp2 : p = 2
    · subst p
      have hm20 : 20 ≤ n / 2 := by
        exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).mpr
          (by omega)
      calc
        alternatingSylowProfileQuadraticCost n 2 ≤
            sylowCycleNegativeBinomialEvenQuadraticCost n :=
          alternatingSylowProfileQuadraticCost_two_le_negativeBinomialEven n
        _ ≤
            sylowCycleNegativeBinomialEvenQuadraticCost
              (2 * (n / 2)) :=
          sylowCycleNegativeBinomialEvenQuadraticCost_le_blockStart n
        _ ≤ sylowCycleNegativeBinomialEvenQuadraticCost 40 :=
          sylowCycleNegativeBinomialEvenQuadraticCost_mul_le_twenty hm20
        _ ≤ (3 : ℝ) / 16 :=
          sylowCycleNegativeBinomialEvenQuadraticCost_forty_lt.le
        _ = alternatingQuadraticPrimeEnvelope 2 := by
          norm_num [alternatingQuadraticPrimeEnvelope]
    by_cases hp3 : p = 3
    · subst p
      have hm13 : 13 ≤ n / 3 := by
        exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 3)).mpr
          (by omega)
      calc
        alternatingSylowProfileQuadraticCost n 3 =
            symmetricSylowProfileQuadraticCost n 3 := by
          simp [alternatingSylowProfileQuadraticCost]
        _ ≤ sylowCycleNegativeBinomialQuadraticCost n 3 :=
          symmetricSylowProfileQuadraticCost_le_negativeBinomial
            Nat.prime_three
        _ ≤
            sylowCycleNegativeBinomialQuadraticCost
              (3 * (n / 3)) 3 :=
          sylowCycleNegativeBinomialQuadraticCost_le_blockStart
            (by norm_num)
        _ ≤ sylowCycleNegativeBinomialQuadraticCost 39 3 :=
          sylowCycleNegativeBinomialQuadraticCost_mul_le_three
            (a := 13) (m := n / 3) (by norm_num) hm13
        _ ≤ (1 : ℝ) / 25 :=
          sylowCycleNegativeBinomialQuadraticCost_three_thirtyNine_lt.le
        _ = alternatingQuadraticPrimeEnvelope 3 := by
          norm_num [alternatingQuadraticPrimeEnvelope]
    by_cases hp5 : p = 5
    · subst p
      have hm8 : 8 ≤ n / 5 := by
        exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 5)).mpr
          (by omega)
      calc
        alternatingSylowProfileQuadraticCost n 5 =
            symmetricSylowProfileQuadraticCost n 5 := by
          simp [alternatingSylowProfileQuadraticCost]
        _ ≤ sylowCycleNegativeBinomialQuadraticCost n 5 :=
          symmetricSylowProfileQuadraticCost_le_negativeBinomial
            Nat.prime_five
        _ ≤
            sylowCycleNegativeBinomialQuadraticCost
              (5 * (n / 5)) 5 :=
          sylowCycleNegativeBinomialQuadraticCost_le_blockStart
            (by norm_num)
        _ ≤ sylowCycleNegativeBinomialQuadraticCost 40 5 :=
          sylowCycleNegativeBinomialQuadraticCost_mul_le_of_five_le
            (p := 5) (a := 8) (m := n / 5)
            (by norm_num) (by norm_num) hm8
        _ ≤ (1 : ℝ) / 10000 :=
          sylowCycleNegativeBinomialQuadraticCost_five_forty_lt.le
        _ = alternatingQuadraticPrimeEnvelope 5 := by
          norm_num [alternatingQuadraticPrimeEnvelope]
    by_cases hp7 : p = 7
    · subst p
      have hm5 : 5 ≤ n / 7 := by
        exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 7)).mpr
          (by omega)
      calc
        alternatingSylowProfileQuadraticCost n 7 =
            symmetricSylowProfileQuadraticCost n 7 := by
          simp [alternatingSylowProfileQuadraticCost]
        _ ≤ sylowCycleNegativeBinomialQuadraticCost n 7 :=
          symmetricSylowProfileQuadraticCost_le_negativeBinomial
            Nat.prime_seven
        _ ≤
            sylowCycleNegativeBinomialQuadraticCost
              (7 * (n / 7)) 7 :=
          sylowCycleNegativeBinomialQuadraticCost_le_blockStart
            (by norm_num)
        _ ≤ sylowCycleNegativeBinomialQuadraticCost 35 7 :=
          sylowCycleNegativeBinomialQuadraticCost_mul_le_of_five_le
            (p := 7) (a := 5) (m := n / 7)
            (by norm_num) (by norm_num) hm5
        _ ≤ (1 : ℝ) / 2400 :=
          sylowCycleNegativeBinomialQuadraticCost_seven_thirtyFive_lt.le
        _ = alternatingQuadraticPrimeEnvelope 7 := by
          norm_num [alternatingQuadraticPrimeEnvelope]
    have hp11 : 11 ≤ p := by
      by_contra h
      have hpOdd :=
        hp.eq_two_or_odd.resolve_left hp2
      have hpMod : p % 2 = 1 := hpOdd
      have hpTwo : 2 ≤ p := hp.two_le
      have hpTen : p ≤ 10 := by omega
      have hp9 : p = 9 := by omega
      rw [hp9] at hp
      exact (by decide : ¬Nat.Prime 9) hp
    have hm1 : 1 ≤ n / p :=
      Nat.div_pos hpn hp.pos
    calc
      alternatingSylowProfileQuadraticCost n p =
          symmetricSylowProfileQuadraticCost n p := by
        simp [alternatingSylowProfileQuadraticCost, hp2]
      _ ≤ sylowCycleNegativeBinomialQuadraticCost n p :=
        symmetricSylowProfileQuadraticCost_le_negativeBinomial hp
      _ ≤
          sylowCycleNegativeBinomialQuadraticCost
            (p * (n / p)) p :=
        sylowCycleNegativeBinomialQuadraticCost_le_blockStart
          hp.two_le
      _ ≤ sylowCycleNegativeBinomialQuadraticCost p p := by
        simpa only [Nat.mul_one] using
          sylowCycleNegativeBinomialQuadraticCost_mul_le_of_five_le
            (p := p) (a := 1) (m := n / p)
            (by omega) (by norm_num) hm1
      _ ≤ (2 : ℝ)⁻¹ ^ p :=
        sylowCycleNegativeBinomialQuadraticCost_self_le_inverseTwoPow hp11
      _ = alternatingQuadraticPrimeEnvelope p := by
        simp [alternatingQuadraticPrimeEnvelope,
          hp2, hp3, hp5, hp7]
  · have hnp : n < p := by omega
    have hp2 : p ≠ 2 := by omega
    have hdiv : n / p = 0 :=
      Nat.div_eq_of_lt hnp
    have hzero :
        alternatingSylowProfileQuadraticCost n p = 0 := by
      simp [alternatingSylowProfileQuadraticCost,
        hp2, symmetricSylowProfileQuadraticCost, hdiv]
    rw [hzero]
    exact (alternatingQuadraticPrimeEnvelope_pos p).le

/-! ## Summing an arbitrary injective prime-labelled family -/

theorem sum_invTwo_pow_le_one_div_1024
    (s : Finset ℕ) (hs : ∀ p ∈ s, 11 ≤ p) :
    (∑ p ∈ s, (2 : ℝ)⁻¹ ^ p) ≤ 1 / 1024 := by
  let f : ℕ → ℝ :=
    fun i ↦ if 11 ≤ i then (2 : ℝ)⁻¹ ^ i else 0
  have hf : Summable f := by
    simpa only [f, ← Set.piecewise_eq_indicator, one_div] using
      summable_geometric_two.indicator {i : ℕ | 11 ≤ i}
  calc
    (∑ p ∈ s, (2 : ℝ)⁻¹ ^ p) =
        ∑ p ∈ s, f p := by
      apply Finset.sum_congr rfl
      intro p hp
      simp [f, hs p hp]
    _ ≤ ∑' i, f i :=
      hf.sum_le_tsum s (fun i _hi ↦ by positivity)
    _ = 2 * (2 : ℝ)⁻¹ ^ 11 := by
      simpa only [f] using tsum_geometric_inv_two_ge 11
    _ = 1 / 1024 := by norm_num

theorem eleven_le_of_prime_of_ne_small
    {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hp5 : p ≠ 5) (hp7 : p ≠ 7) :
    11 ≤ p := by
  by_contra h
  have hpOdd :=
    hp.eq_two_or_odd.resolve_left hp2
  have hpMod : p % 2 = 1 := hpOdd
  have hpTwo : 2 ≤ p := hp.two_le
  have hpTen : p ≤ 10 := by omega
  have hp9 : p = 9 := by omega
  rw [hp9] at hp
  exact (by decide : ¬Nat.Prime 9) hp

theorem sum_alternatingQuadraticPrimeEnvelope_lt_one_div_four
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    (∑ p ∈ s, alternatingQuadraticPrimeEnvelope p) <
      1 / 4 := by
  let tail := s.filter fun p ↦ 11 ≤ p
  have htail :
      (∑ p ∈ tail, (2 : ℝ)⁻¹ ^ p) ≤ 1 / 1024 :=
    sum_invTwo_pow_le_one_div_1024 tail
      (fun p hp ↦ (Finset.mem_filter.mp hp).2)
  have hpoint :
      ∀ p ∈ s,
        alternatingQuadraticPrimeEnvelope p ≤
          (if p = 2 then (3 : ℝ) / 16 else 0) +
          (if p = 3 then (1 : ℝ) / 25 else 0) +
          (if p = 5 then (1 : ℝ) / 10000 else 0) +
          (if p = 7 then (1 : ℝ) / 2400 else 0) +
          (if 11 ≤ p then (2 : ℝ)⁻¹ ^ p else 0) := by
    intro p hpMem
    have hpPrime := hs p hpMem
    by_cases hp2 : p = 2
    · subst p
      norm_num [alternatingQuadraticPrimeEnvelope]
    by_cases hp3 : p = 3
    · subst p
      norm_num [alternatingQuadraticPrimeEnvelope]
    by_cases hp5 : p = 5
    · subst p
      norm_num [alternatingQuadraticPrimeEnvelope]
    by_cases hp7 : p = 7
    · subst p
      norm_num [alternatingQuadraticPrimeEnvelope]
    have hp11 :=
      eleven_le_of_prime_of_ne_small
        hpPrime hp2 hp3 hp5 hp7
    simp [alternatingQuadraticPrimeEnvelope,
      hp2, hp3, hp5, hp7, hp11]
  calc
    (∑ p ∈ s, alternatingQuadraticPrimeEnvelope p) ≤
        ∑ p ∈ s,
          ((if p = 2 then (3 : ℝ) / 16 else 0) +
          (if p = 3 then (1 : ℝ) / 25 else 0) +
          (if p = 5 then (1 : ℝ) / 10000 else 0) +
          (if p = 7 then (1 : ℝ) / 2400 else 0) +
          (if 11 ≤ p then (2 : ℝ)⁻¹ ^ p else 0)) :=
      Finset.sum_le_sum fun p hp ↦ hpoint p hp
    _ ≤ (3 : ℝ) / 16 + 1 / 25 + 1 / 10000 +
          1 / 2400 + 1 / 1024 := by
      have htwo :
          (∑ p ∈ s,
            if p = 2 then (3 : ℝ) / 16 else 0) ≤
            (3 : ℝ) / 16 := by
        simp only [Finset.sum_ite_eq']
        split_ifs <;> norm_num
      have hthree :
          (∑ p ∈ s,
            if p = 3 then (1 : ℝ) / 25 else 0) ≤
            (1 : ℝ) / 25 := by
        simp only [Finset.sum_ite_eq']
        split_ifs <;> norm_num
      have hfive :
          (∑ p ∈ s,
            if p = 5 then (1 : ℝ) / 10000 else 0) ≤
            (1 : ℝ) / 10000 := by
        simp only [Finset.sum_ite_eq']
        split_ifs <;> norm_num
      have hseven :
          (∑ p ∈ s,
            if p = 7 then (1 : ℝ) / 2400 else 0) ≤
            (1 : ℝ) / 2400 := by
        simp only [Finset.sum_ite_eq']
        split_ifs <;> norm_num
      have htail' :
          (∑ p ∈ s,
            if 11 ≤ p then (2 : ℝ)⁻¹ ^ p else 0) ≤
              1 / 1024 := by
        calc
          (∑ p ∈ s,
              if 11 ≤ p then (2 : ℝ)⁻¹ ^ p else 0) =
              ∑ p ∈ tail, (2 : ℝ)⁻¹ ^ p := by
            simp only [tail, Finset.sum_filter]
          _ ≤ 1 / 1024 := htail
      simp only [Finset.sum_add_distrib]
      linarith
    _ < 1 / 4 := by norm_num

theorem sum_alternatingSylowProfileQuadraticCost_lt_one_div_four
    {ι : Type*} (s : Finset ι) (p : ι → ℕ)
    (n : ℕ) (hn : 40 ≤ n)
    (hp : ∀ i ∈ s, (p i).Prime)
    (hinj : Set.InjOn p s) :
    (∑ i ∈ s,
      alternatingSylowProfileQuadraticCost n (p i)) <
        1 / 4 := by
  calc
    (∑ i ∈ s,
        alternatingSylowProfileQuadraticCost n (p i)) ≤
        ∑ i ∈ s, alternatingQuadraticPrimeEnvelope (p i) :=
      Finset.sum_le_sum fun i hi ↦
        alternatingSylowProfileQuadraticCost_le_primeEnvelope
          hn (hp i hi)
    _ =
        ∑ q ∈ s.image p, alternatingQuadraticPrimeEnvelope q := by
      rw [Finset.sum_image hinj]
    _ < 1 / 4 :=
      sum_alternatingQuadraticPrimeEnvelope_lt_one_div_four
        (s.image p)
        (by
          intro q hq
          obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
          exact hp i hi)

end LisiSabatini
