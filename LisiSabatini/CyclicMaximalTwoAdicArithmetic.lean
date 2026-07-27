import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

/-!
# Two-adic arithmetic for cyclic maximal subgroups

This file isolates the elementary congruence classification used for the
conjugation parameter of a finite `2`-group with a cyclic maximal subgroup.
-/

namespace LisiSabatini

/-- A multiple of `q` is congruent either to `0` or to `q` modulo `2 * q`.
This is the elementary two-to-one lifting step for natural congruences. -/
theorem modEq_two_mul_zero_or_self_of_dvd
    {q n : ℕ} (hqn : q ∣ n) :
    Nat.ModEq (2 * q) n 0 ∨ Nat.ModEq (2 * q) n q := by
  obtain ⟨a, rfl⟩ := hqn
  obtain ⟨b, hb | hb⟩ := Nat.even_or_odd' a
  · left
    rw [hb, Nat.modEq_zero_iff_dvd]
    refine ⟨b, ?_⟩
    ring
  · right
    rw [hb]
    simpa [mul_add, mul_assoc, mul_comm, mul_left_comm] using
      (Nat.ModEq.modulus_mul_add (m := 2 * q) (a := b) (b := q))

/-- If `q` divides `k + 1`, then `k` is the normalized residue `q - 1`
modulo `q`. -/
theorem modEq_pred_of_dvd_add_one
    {q k : ℕ} (hq : 0 < q) (hdiv : q ∣ k + 1) :
    Nat.ModEq q k (q - 1) := by
  apply Nat.ModEq.add_right_cancel' 1
  calc
    k + 1 ≡ 0 [MOD q] := hdiv.modEq_zero_nat
    _ ≡ q [MOD q] := Nat.modulus_modEq_zero.symm
    _ = (q - 1) + 1 := by omega

/-- A square root of `1` modulo `2 ^ m`, for `m ≥ 3`, is already
congruent to `1` or `-1` modulo `2 ^ (m - 1)`.

The second residue is written as the normalized natural number
`2 ^ (m - 1) - 1`. -/
theorem modEq_one_or_pred_pow_pred_of_sq_modEq_one
    {m k : ℕ} (hm : 3 ≤ m)
    (hsq : Nat.ModEq (2 ^ m) (k * k) 1) :
    Nat.ModEq (2 ^ (m - 1)) k 1 ∨
      Nat.ModEq (2 ^ (m - 1)) k (2 ^ (m - 1) - 1) := by
  have hm0 : m ≠ 0 := by omega
  have hsqTwo : Nat.ModEq 2 (k * k) 1 :=
    hsq.of_dvd (dvd_pow_self 2 hm0)
  have hkmod : k % 2 = 1 := by
    obtain hk0 | hk1 := Nat.mod_two_eq_zero_or_one k
    · exfalso
      simp [Nat.ModEq, Nat.mul_mod, hk0] at hsqTwo
    · exact hk1
  obtain ⟨t, ht⟩ := (Nat.odd_iff.mpr hkmod)
  subst k
  have hsquare :
      (2 * t + 1) * (2 * t + 1) =
        4 * (t * (t + 1)) + 1 := by
    ring
  rw [hsquare] at hsq
  have hproductMod : Nat.ModEq (2 ^ m) (4 * (t * (t + 1))) 0 := by
    apply Nat.ModEq.add_right_cancel' 1
    simpa using hsq
  have hproduct : 2 ^ m ∣ 4 * (t * (t + 1)) :=
    Nat.modEq_zero_iff_dvd.mp hproductMod
  have hmTwo : 2 ≤ m := by omega
  have hpow :
      2 ^ m = 4 * 2 ^ (m - 2) := by
    calc
      2 ^ m = 2 ^ ((m - 2) + 2) := by
        rw [Nat.sub_add_cancel hmTwo]
      _ = 4 * 2 ^ (m - 2) := by
        rw [pow_add]
        ring
  rw [hpow] at hproduct
  have hsmall : 2 ^ (m - 2) ∣ t * (t + 1) :=
    (mul_dvd_mul_iff_left (by norm_num : (4 : ℕ) ≠ 0)).mp hproduct
  have hcoprime : Nat.Coprime t (t + 1) := by
    exact
      (Nat.coprime_self_add_right (m := t) (n := 1)).mpr
        ((Nat.coprime_one_right_iff t).mpr trivial)
  have hprimePow : IsPrimePow (2 ^ (m - 2)) :=
    Nat.prime_two.isPrimePow.pow (by omega)
  have hsplit :
      2 ^ (m - 2) ∣ t ∨ 2 ^ (m - 2) ∣ t + 1 :=
    (hcoprime.isPrimePow_dvd_mul hprimePow).mp hsmall
  have hhalf :
      2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    calc
      2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by
        congr 1
        omega
      _ = 2 * 2 ^ (m - 2) := by
        rw [pow_add]
        ring
  rcases hsplit with htdiv | htdiv
  · left
    have htmod : Nat.ModEq (2 ^ (m - 2)) t 0 :=
      htdiv.modEq_zero_nat
    have htwomod :
        Nat.ModEq (2 * 2 ^ (m - 2)) (2 * t) (2 * 0) :=
      htmod.mul_left' 2
    simpa [hhalf] using htwomod.add_right 1
  · right
    apply modEq_pred_of_dvd_add_one (by positivity)
    rw [hhalf]
    have hmul :
        2 * 2 ^ (m - 2) ∣ 2 * (t + 1) :=
      mul_dvd_mul_left 2 htdiv
    simpa [mul_add, add_assoc] using hmul

/-- Exact two-adic classification needed for the cyclic-maximal-subgroup
conjugation parameter.

Among the four square roots of `1` modulo `2 ^ m`, the hypothesis excluding
the residue `1` modulo `2 ^ (m - 1)` leaves precisely the normalized residues
`-1` and `2 ^ (m - 1) - 1` modulo `2 ^ m`. -/
theorem modEq_neg_one_or_half_pred_of_sq_modEq_one
    {m k : ℕ} (hm : 3 ≤ m)
    (hsq : Nat.ModEq (2 ^ m) (k * k) 1)
    (hne : ¬Nat.ModEq (2 ^ (m - 1)) k 1) :
    Nat.ModEq (2 ^ m) k (2 ^ m - 1) ∨
      Nat.ModEq (2 ^ m) k (2 ^ (m - 1) - 1) := by
  have hnegHalf :
      Nat.ModEq (2 ^ (m - 1)) k (2 ^ (m - 1) - 1) :=
    (modEq_one_or_pred_pow_pred_of_sq_modEq_one hm hsq).resolve_left hne
  have hhalfPos : 0 < 2 ^ (m - 1) := by positivity
  have hsumHalf :
      Nat.ModEq (2 ^ (m - 1)) (k + 1) (2 ^ (m - 1)) := by
    simpa [Nat.sub_add_cancel hhalfPos] using hnegHalf.add_right 1
  have hhalfDiv : 2 ^ (m - 1) ∣ k + 1 := by
    rw [← Nat.modEq_zero_iff_dvd]
    exact hsumHalf.trans Nat.modulus_modEq_zero
  have hpow :
      2 ^ m = 2 * 2 ^ (m - 1) := by
    calc
      2 ^ m = 2 ^ ((m - 1) + 1) := by
        congr 1
        omega
      _ = 2 * 2 ^ (m - 1) := by
        rw [pow_add]
        ring
  rcases modEq_two_mul_zero_or_self_of_dvd hhalfDiv with hzero | hhalf
  · left
    apply Nat.ModEq.add_right_cancel' 1
    rw [hpow]
    calc
      k + 1 ≡ 0 [MOD 2 * 2 ^ (m - 1)] := hzero
      _ ≡ 2 * 2 ^ (m - 1) [MOD 2 * 2 ^ (m - 1)] :=
        Nat.modulus_modEq_zero.symm
      _ = (2 * 2 ^ (m - 1) - 1) + 1 := by omega
  · right
    apply Nat.ModEq.add_right_cancel' 1
    rw [hpow]
    calc
      k + 1 ≡ 2 ^ (m - 1) [MOD 2 * 2 ^ (m - 1)] := hhalf
      _ = (2 ^ (m - 1) - 1) + 1 := by omega

end LisiSabatini
