import LisiSabatini.SchurCenterHalfOrbitCore
import LisiSabatini.FixedPointFreeOffZero
import LisiSabatini.CyclicCenterOperatorSpectrum
import LisiSabatini.FixedSpectrumNonregularBound

/-!
# One-row estimates for mixed prime-core domination

These two general estimates are the only part of the historical mixed-marker
module needed by the quasiprimitive publication proof.
-/

noncomputable section

namespace LisiSabatini

/-- A nontrivial fixed-point-free group has canonical fixed-spectrum charge
exactly one. -/
theorem fixedSpectrumNonregularBound_eq_one_of_fixedPointFreeOffZero
    {R V : Type*} [Semiring R] [AddCommGroup V] [Module R V] [Finite V]
    (P : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hne : P ≠ ⊥) (hfp : FixedPointFreeOffZero P) :
    fixedSpectrumNonregularBound P = 1 := by
  classical
  letI : Finite P := finite_linearSubgroup_of_finite P
  letI : Fintype P := Fintype.ofFinite P
  rw [fixedSpectrumNonregularBound, if_neg hne]
  have hfixed (g : P) (hg : g ≠ 1) : fixedVectorSet g.1 = {0} := by
    ext v
    constructor
    · intro hv
      have hvfix : g • v = v := hv
      simp [hfp g hg v hvfix]
    · intro hv
      have hvzero : v = 0 := by simpa using hv
      subst v
      simp [fixedVectorSet]
  have hzero : ∀ g ∈ nonidentityElements P,
      (fixedVectorSet g.1).ncard - 1 = 0 := by
    intro g hg
    have hgne : g ≠ 1 := by
      simpa [nonidentityElements] using hg
    rw [hfixed g hgne]
    simp
  rw [Finset.sum_eq_zero hzero]
  simp

/-- Full-center Schur divisibility gives a three-orbit reserve inside the
same compressed spectrum budget used for the fixed-space count. -/
theorem three_mul_natCard_le_cyclicCenterOperatorSpectrumBound_of_fullCenterRow
    {r e q a m : ℕ} [Fact r.Prime]
    {P : Type*} [Group P] [Finite P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (hrTwo : r ≠ 2)
    (ha : 0 < a) (hm : 0 < m)
    (hcenterDvd : Nat.card (Subgroup.center P) ∣ r ^ a - 1)
    (hdim : e = a * q ^ hP.cyclicCenterStructuralRank * m) :
    3 * Nat.card P ≤ cyclicCenterOperatorSpectrumBound
      r e q hP.cyclicCenterStructuralRank := by
  let n := hP.cyclicCenterStructuralRank
  let z := Nat.card (Subgroup.center P)
  letI : Fact q.Prime := ⟨hP.prime⟩
  have hn : 0 < n := hP.cyclicCenterStructuralRank_pos
  have hqThree : 3 ≤ q := by
    obtain ⟨k, hk⟩ := hP.odd
    have := hP.prime.two_le
    omega
  have hrOdd : Odd r := (Fact.out : Nat.Prime r).odd_of_ne_two hrTwo
  obtain ⟨s, hs⟩ := IsPGroup.iff_card.mp
    (hP.pGroup.to_subgroup (Subgroup.center P))
  have hzOdd : Odd z := by
    rw [show z = q ^ s by simpa [z] using hs]
    exact hP.odd.pow
  obtain ⟨k, hk⟩ := hcenterDvd
  have hkEven : Even k := by
    have htargetEven : Even (r ^ a - 1) :=
      hrOdd.pow.tsub_odd odd_one
    have hprodEven : Even (z * k) := by
      rw [← hk]
      exact htargetEven
    exact (Nat.even_mul.mp hprodEven).resolve_left
      (Nat.not_even_iff_odd.mpr hzOdd)
  have hkZero : k ≠ 0 := by
    intro hk0
    subst k
    simp at hk
    have hrThree : 3 ≤ r := by
      obtain ⟨j, hj⟩ := hrOdd
      have := (Fact.out : Nat.Prime r).two_le
      omega
    have hpow : 3 ≤ r ^ a := by
      calc
        3 ≤ r := hrThree
        _ = r ^ 1 := by simp
        _ ≤ r ^ a := Nat.pow_le_pow_right
          (Fact.out : Nat.Prime r).pos ha
    omega
  have hkTwo : 2 ≤ k := by
    have := Nat.one_lt_of_ne_zero_of_even hkZero hkEven
    omega
  have htwoCenter : 2 * z ≤ r ^ a - 1 := by
    calc
      2 * z ≤ k * z := Nat.mul_le_mul_right z hkTwo
      _ = z * k := by ring
      _ = r ^ a - 1 := hk.symm
  obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hnEq : n = t + 1 := by simpa [n] using ht
  have hnEq' : hP.cyclicCenterStructuralRank = t + 1 := by
    simpa [n] using hnEq
  change e = a * q ^ n * m at hdim
  change 3 * Nat.card P ≤ cyclicCenterOperatorSpectrumBound r e q n
  rw [hnEq] at hdim ⊢
  have hquot : (a * q ^ (t + 1) * m) / q = a * q ^ t * m := by
    rw [pow_succ]
    have hrearrange : a * (q ^ t * q) * m =
        q * (a * q ^ t * m) := by ring
    rw [hrearrange]
    exact Nat.mul_div_cancel_left (a * q ^ t * m) hP.prime.pos
  have haLeQuot : a ≤ (a * q ^ (t + 1) * m) / q := by
    rw [hquot]
    calc
      a = a * 1 := by simp
      _ ≤ a * (q ^ t * m) := by
        apply Nat.mul_le_mul_left
        exact Nat.one_le_iff_ne_zero.mpr
          (mul_ne_zero (pow_ne_zero _ hP.prime.ne_zero) hm.ne')
      _ = a * q ^ t * m := by ring
  have hpowLe : r ^ a ≤ r ^ ((a * q ^ (t + 1) * m) / q) :=
    Nat.pow_le_pow_right (Fact.out : Nat.Prime r).pos haLeQuot
  let X := r ^ ((a * q ^ (t + 1) * m) / q) - 1
  have htwoCenterX : 2 * z ≤ X := by
    exact htwoCenter.trans (Nat.sub_le_sub_right hpowLe 1)
  have hthreeCenter : 3 * z ≤ 2 * X := by
    have hzLe : z ≤ X := by omega
    omega
  let Q := q ^ (2 * (t + 1))
  have hQpos : 0 < Q := pow_pos hP.prime.pos _
  have hcoeff : 2 * Q ≤ q * Q - 1 := by
    have : 3 * Q ≤ q * Q := Nat.mul_le_mul_right Q hqThree
    omega
  have hcardP : Nat.card P = Q * z := by
    calc
      Nat.card P = Nat.card (P ⧸ Subgroup.center P) *
          Nat.card (Subgroup.center P) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center P)
      _ = Q * z := by
        rw [hP.cyclicCenterStructuralRank_card_quotient_center]
        rw [hnEq']
  rw [hdim, hcardP]
  unfold cyclicCenterOperatorSpectrumBound
  change 3 * (Q * z) ≤ 1 + (q ^ (2 * (t + 1) + 1) - 1) * X
  have hpowSucc : q ^ (2 * (t + 1) + 1) = q * Q := by
    rw [pow_succ]
    simp only [Q]
    ring
  rw [hpowSucc]
  calc
    3 * (Q * z) = Q * (3 * z) := by ring
    _ ≤ Q * (2 * X) := Nat.mul_le_mul_left Q hthreeCenter
    _ = (2 * Q) * X := by ring
    _ ≤ (q * Q - 1) * X := Nat.mul_le_mul_right X hcoeff
    _ ≤ 1 + (q * Q - 1) * X := Nat.le_add_left _ _

end LisiSabatini
