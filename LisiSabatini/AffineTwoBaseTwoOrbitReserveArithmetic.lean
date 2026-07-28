module

public import LisiSabatini.AffineTwoBasePairSpectrumArithmetic
public import LisiSabatini.MixedPrimeCoreOneRowEstimates

/-!
# Arithmetic reserves for two-orbit affine two-base synchronization

The recursive diagonal invariant must pay for two complete orbits of one
distinguished component in addition to the two-base bad loci.  This file
collects the numerical estimates which make that extra charge explicit.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

/-- In characteristic two, the direct pair-spectrum row of a noncommuting
odd cyclic-center prime group already contains the cost of two full group
orbits.

The center order is absorbed by one binary fixed-space block, while
`q ≥ 3` absorbs the factor `2` in front of the group order. -/
theorem two_mul_natCard_le_odd_cyclicCenter_pairSpectrum_of_fullCenterRow
    {e q a m : ℕ}
    {P : Type*} [Group P] [Finite P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (ha : 0 < a) (hm : 0 < m)
    (hcenterDvd : Nat.card (Subgroup.center P) ∣ 2 ^ a - 1)
    (hdim : e = a * q ^ hP.cyclicCenterStructuralRank * m) :
    2 * Nat.card P ≤
      1 + (q ^ (2 * hP.cyclicCenterStructuralRank + 1) - 1) *
        (2 ^ (2 * (e / q)) - 1) := by
  let n := hP.cyclicCenterStructuralRank
  let z := Nat.card (Subgroup.center P)
  let Q := q ^ (2 * n)
  have hn : 0 < n := hP.cyclicCenterStructuralRank_pos
  have hqThree : 3 ≤ q := by
    obtain ⟨k, hk⟩ := hP.odd
    have := hP.prime.two_le
    omega
  have haLeQuot : a ≤ e / q := by
    obtain ⟨t, ht⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hnEq : n = t + 1 := by simpa [n] using ht
    change e = a * q ^ n * m at hdim
    rw [hdim, hnEq, pow_succ]
    have hquot :
        (a * (q ^ t * q) * m) / q = a * q ^ t * m := by
      have hrearrange :
          a * (q ^ t * q) * m = q * (a * q ^ t * m) := by
        ring
      rw [hrearrange]
      exact Nat.mul_div_cancel_left (a * q ^ t * m) hP.prime.pos
    rw [hquot]
    calc
      a = a * 1 := by simp
      _ ≤ a * (q ^ t * m) := by
        apply Nat.mul_le_mul_left
        exact Nat.one_le_iff_ne_zero.mpr
          (mul_ne_zero (pow_ne_zero _ hP.prime.ne_zero) hm.ne')
      _ = a * q ^ t * m := by ring
  have htargetPos : 0 < 2 ^ a - 1 := by
    have : 1 < 2 ^ a :=
      one_lt_pow₀ (by norm_num) ha.ne'
    omega
  have hzSmall : z ≤ 2 ^ a - 1 :=
    Nat.le_of_dvd htargetPos hcenterDvd
  have hpowLe : 2 ^ a ≤ 2 ^ (e / q) :=
    Nat.pow_le_pow_right (by norm_num) haLeQuot
  have hzFixed : z ≤ 2 ^ (2 * (e / q)) - 1 := by
    have hfirst : z ≤ 2 ^ (e / q) - 1 :=
      hzSmall.trans (Nat.sub_le_sub_right hpowLe 1)
    have hpowOne : 1 ≤ 2 ^ (e / q) := by
      exact Nat.one_le_pow _ _ (by norm_num)
    have hpowSquare :
        2 ^ (2 * (e / q)) =
          2 ^ (e / q) * 2 ^ (e / q) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpowSquare]
    exact hfirst.trans
      (Nat.sub_le_sub_right
        (Nat.le_mul_of_pos_left _ (pow_pos (by norm_num) _)) 1)
  have hcardP : Nat.card P = Q * z := by
    calc
      Nat.card P =
          Nat.card (P ⧸ Subgroup.center P) *
            Nat.card (Subgroup.center P) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup
          (Subgroup.center P)
      _ = Q * z := by
        rw [hP.cyclicCenterStructuralRank_card_quotient_center]
  have hcoeff : 2 * Q ≤ q * Q - 1 := by
    have hQpos : 0 < Q := pow_pos hP.prime.pos _
    have : 3 * Q ≤ q * Q := Nat.mul_le_mul_right Q hqThree
    omega
  have hpowSucc :
      q ^ (2 * n + 1) = q * Q := by
    rw [pow_succ]
    change Q * q = q * Q
    exact Nat.mul_comm Q q
  rw [hcardP]
  change
    2 * (Q * z) ≤
      1 + (q ^ (2 * n + 1) - 1) *
        (2 ^ (2 * (e / q)) - 1)
  rw [hpowSucc]
  calc
    2 * (Q * z) = (2 * Q) * z := by ring
    _ ≤ (q * Q - 1) * z :=
      Nat.mul_le_mul_right z hcoeff
    _ ≤ (q * Q - 1) * (2 ^ (2 * (e / q)) - 1) :=
      Nat.mul_le_mul_left (q * Q - 1) hzFixed
    _ ≤ 1 + (q * Q - 1) * (2 ^ (2 * (e / q)) - 1) :=
      Nat.le_add_left _ _

end LisiSabatini
