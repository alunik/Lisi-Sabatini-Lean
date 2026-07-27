import LisiSabatini.HallBergerCyclicMaximalSubgroup
import LisiSabatini.CyclicMaximalTwoAdicArithmetic
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Finite two-groups with a cyclic maximal subgroup

This file proves the classical metacyclic classification in the precise
noncentral-square form needed by the Hall--Berger reduction.  The proof keeps
the distinguished rotation and coset representative from
`CyclicMaximalTwoGroupData` throughout.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

namespace CyclicMaximalTwoGroup

variable {H : Type u} [Group H] [Finite H]

private def normalFormMap
    (a c : H) (N : ℕ) :
    ZMod N ⊕ ZMod N → H
  | .inl i => a ^ i.val
  | .inr i => c * a ^ i.val

omit [Finite H] in
private theorem pow_val_natCast
    (a : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N) (n : ℕ) :
    a ^ (n : ZMod N).val = a ^ n := by
  rw [pow_eq_pow_iff_modEq, horder,
    ← ZMod.natCast_eq_natCast_iff]
  simp only [ZMod.natCast_zmod_val]

omit [Finite H] in
private theorem pow_val_injective
    (a : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N) :
    Function.Injective (fun i : ZMod N ↦ a ^ i.val) := by
  intro i j hij
  rw [← ZMod.natCast_zmod_val i,
    ← ZMod.natCast_zmod_val j]
  exact
    (ZMod.natCast_eq_natCast_iff i.val j.val N).2
      (by simpa only [horder] using
        (pow_eq_pow_iff_modEq.mp hij))

private theorem normalFormMap_bijective
    (a c : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a) :
    Function.Bijective (normalFormMap a c N) := by
  classical
  let A : Subgroup H := Subgroup.zpowers a
  have hpowInjective :
      Function.Injective (fun i : ZMod N ↦ a ^ i.val) :=
    pow_val_injective a horder
  constructor
  · intro x y hxy
    cases x with
    | inl i =>
        cases y with
        | inl j =>
            congr 1
            change a ^ i.val = a ^ j.val at hxy
            exact hpowInjective hxy
        | inr j =>
            exfalso
            apply hc
            apply
              (A.mul_mem_cancel_right
                (Subgroup.npow_mem_zpowers a j.val)).mp
            change a ^ i.val = c * a ^ j.val at hxy
            rw [← hxy]
            exact Subgroup.npow_mem_zpowers a i.val
    | inr i =>
        cases y with
        | inl j =>
            exfalso
            apply hc
            apply
              (A.mul_mem_cancel_right
                (Subgroup.npow_mem_zpowers a i.val)).mp
            change c * a ^ i.val = a ^ j.val at hxy
            rw [hxy]
            exact Subgroup.npow_mem_zpowers a j.val
        | inr j =>
            congr 1
            apply hpowInjective
            change c * a ^ i.val = c * a ^ j.val at hxy
            exact mul_left_cancel hxy
  · intro x
    by_cases hx : x ∈ A
    · have hxPowers : x ∈ Submonoid.powers a :=
        mem_powers_iff_mem_zpowers.mpr hx
      obtain ⟨n, hn⟩ :=
        (Submonoid.mem_powers_iff x a).mp hxPowers
      refine ⟨.inl (n : ZMod N), ?_⟩
      exact (pow_val_natCast a horder n).trans hn
    · have hcinv : c⁻¹ ∉ A := by
        simpa only [inv_mem_iff] using hc
      have hy : c⁻¹ * x ∈ A := by
        rw [A.mul_mem_iff_of_index_two hindex]
        simp only [hcinv, hx, iff_self]
      have hyPowers :
          c⁻¹ * x ∈ Submonoid.powers a :=
        mem_powers_iff_mem_zpowers.mpr hy
      obtain ⟨n, hn⟩ :=
        (Submonoid.mem_powers_iff (c⁻¹ * x) a).mp
          hyPowers
      refine ⟨.inr (n : ZMod N), ?_⟩
      change c * a ^ (n : ZMod N).val = x
      rw [pow_val_natCast a horder n, hn]
      group

private def normalFormEquiv
    (a c : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a) :
    (ZMod N ⊕ ZMod N) ≃ H :=
  Equiv.ofBijective (normalFormMap a c N)
    (normalFormMap_bijective a c horder hindex hc)

@[simp]
private theorem normalFormEquiv_inl
    (a c : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (i : ZMod N) :
    normalFormEquiv a c horder hindex hc (.inl i) =
      a ^ i.val :=
  rfl

@[simp]
private theorem normalFormEquiv_inr
    (a c : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (i : ZMod N) :
    normalFormEquiv a c horder hindex hc (.inr i) =
      c * a ^ i.val :=
  rfl

omit [Finite H] in
private theorem pow_eq_pow_val
    (a : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (n : ℕ) (i : ZMod N)
    (hcast : (n : ZMod N) = i) :
    a ^ n = a ^ i.val := by
  rw [pow_eq_pow_iff_modEq, horder,
    ← ZMod.natCast_eq_natCast_iff]
  exact hcast.trans (ZMod.natCast_zmod_val i).symm

omit [Finite H] in
private theorem conjugate_pow
    (a c : H) {r : ℕ}
    (hconj : c * a * c⁻¹ = a ^ r)
    (n : ℕ) :
    c * a ^ n * c⁻¹ = a ^ (r * n) := by
  calc
    c * a ^ n * c⁻¹ =
        (c * a * c⁻¹) ^ n := conj_pow.symm
    _ = (a ^ r) ^ n := by rw [hconj]
    _ = a ^ (r * n) := (pow_mul a r n).symm

omit [Finite H] in
private theorem rotation_mul_coset
    (a c : H) {N r : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hconj : c * a * c⁻¹ = a ^ r)
    (hrsq : Nat.ModEq N (r * r) 1)
    (n : ℕ) :
    a ^ n * c = c * a ^ (r * n) := by
  have hrr :
      a ^ (r * (r * n)) = a ^ n := by
    rw [pow_eq_pow_iff_modEq, horder]
    simpa only [mul_assoc, one_mul] using
      hrsq.mul_right n
  calc
    a ^ n * c =
        (c * a ^ (r * n) * c⁻¹) * c := by
      rw [conjugate_pow a c hconj, hrr]
    _ = c * a ^ (r * n) := by group

private theorem normalForm_rotation_mul_rotation
    (a c : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (i j : ZMod N) :
    normalFormEquiv a c horder hindex hc (.inl i) *
        normalFormEquiv a c horder hindex hc (.inl j) =
      normalFormEquiv a c horder hindex hc (.inl (i + j)) := by
  change a ^ i.val * a ^ j.val = a ^ (i + j).val
  rw [← pow_add]
  apply pow_eq_pow_val a horder
  simp only [Nat.cast_add, ZMod.natCast_zmod_val]

private theorem normalForm_rotation_mul_coset
    (a c : H) {N r : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (hconj : c * a * c⁻¹ = a ^ r)
    (hrsq : Nat.ModEq N (r * r) 1)
    (i j : ZMod N) :
    normalFormEquiv a c horder hindex hc (.inl i) *
        normalFormEquiv a c horder hindex hc (.inr j) =
      normalFormEquiv a c horder hindex hc
        (.inr (j + (r : ZMod N) * i)) := by
  change
    a ^ i.val * (c * a ^ j.val) =
      c * a ^ (j + (r : ZMod N) * i).val
  rw [← mul_assoc, rotation_mul_coset a c horder hconj hrsq]
  rw [mul_assoc, ← pow_add]
  congr 1
  apply pow_eq_pow_val a horder
  simp only [Nat.cast_add, Nat.cast_mul,
    ZMod.natCast_zmod_val]
  ac_rfl

private theorem normalForm_coset_mul_rotation
    (a c : H) {N : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (i j : ZMod N) :
    normalFormEquiv a c horder hindex hc (.inr i) *
        normalFormEquiv a c horder hindex hc (.inl j) =
      normalFormEquiv a c horder hindex hc (.inr (i + j)) := by
  change
    (c * a ^ i.val) * a ^ j.val =
      c * a ^ (i + j).val
  rw [mul_assoc, ← pow_add]
  congr 1
  apply pow_eq_pow_val a horder
  simp only [Nat.cast_add, ZMod.natCast_zmod_val]

private theorem normalForm_coset_mul_coset
    (a c : H) {N r s : ℕ} [NeZero N]
    (horder : orderOf a = N)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (hconj : c * a * c⁻¹ = a ^ r)
    (hrsq : Nat.ModEq N (r * r) 1)
    (hcsq : c ^ 2 = a ^ s)
    (i j : ZMod N) :
    normalFormEquiv a c horder hindex hc (.inr i) *
        normalFormEquiv a c horder hindex hc (.inr j) =
      normalFormEquiv a c horder hindex hc
        (.inl ((s : ZMod N) + j + (r : ZMod N) * i)) := by
  change
    (c * a ^ i.val) * (c * a ^ j.val) =
      a ^ ((s : ZMod N) + j + (r : ZMod N) * i).val
  calc
    (c * a ^ i.val) * (c * a ^ j.val) =
        c * (a ^ i.val * c) * a ^ j.val := by group
    _ = c * (c * a ^ (r * i.val)) * a ^ j.val := by
      rw [rotation_mul_coset a c horder hconj hrsq]
    _ =
        c ^ 2 * (a ^ (r * i.val) * a ^ j.val) := by
      simp only [pow_two]
      group
    _ = a ^ s * (a ^ (r * i.val) * a ^ j.val) := by
      rw [hcsq]
    _ = a ^ (s + (r * i.val + j.val)) := by
      simp only [← pow_add]
    _ = a ^ ((s : ZMod N) + j + (r : ZMod N) * i).val := by
      apply pow_eq_pow_val a horder
      simp only [Nat.cast_add, Nat.cast_mul,
        ZMod.natCast_zmod_val]
      ac_rfl

private theorem pred_cast_eq_neg_one
    (N : ℕ) (hN : 0 < N) :
    ((N - 1 : ℕ) : ZMod N) = -1 := by
  rw [Nat.cast_sub (by omega), Nat.cast_one]
  simp only [ZMod.natCast_self, zero_sub]

private theorem pred_sq_modEq_one
    (N : ℕ) (hN : 0 < N) :
    Nat.ModEq N ((N - 1) * (N - 1)) 1 := by
  rw [← ZMod.natCast_eq_natCast_iff]
  simp only [Nat.cast_mul, pred_cast_eq_neg_one N hN]
  ring

private theorem semidihedral_twist_sq_modEq_one
    (q : ℕ) (hq : 0 < q) :
    Nat.ModEq (8 * q)
      ((4 * q - 1) * (4 * q - 1)) 1 := by
  rw [← ZMod.natCast_eq_natCast_iff]
  have hsub :
      ((4 * q - 1 : ℕ) : ZMod (8 * q)) =
        (4 * q : ZMod (8 * q)) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
  have hmod :
      ((8 * q : ℕ) : ZMod (8 * q)) = 0 := by simp
  have hmod' :
      (8 : ZMod (8 * q)) * (q : ZMod (8 * q)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmod
  simp only [Nat.cast_mul, hsub]
  linear_combination
    (2 * (q : ZMod (8 * q)) - 1) * hmod'

private theorem semidihedral_twist_cast
    (q : ℕ) (hq : 0 < q) :
    ((4 * q - 1 : ℕ) : ZMod (8 * q)) =
      semidihedralTwist q := by
  simp only [semidihedralTwist]
  rw [Nat.cast_sub (by omega), Nat.cast_one]

private def quaternionEquivSum (n : ℕ) :
    QuaternionGroup n ≃
      (ZMod (2 * n) ⊕ ZMod (2 * n)) where
  toFun
    | .a i => .inl i
    | .xa i => .inr i
  invFun
    | .inl i => .a i
    | .inr i => .xa i
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro (i | i) <;> rfl

private def dihedralHead
    (q : ℕ) (hq : 2 ≤ q)
    (a c : H)
    (horder : orderOf a = 4 * q)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (hconj :
      c * a * c⁻¹ = a ^ (4 * q - 1))
    (hcsq : c ^ 2 = 1) :
    BergerMaximalClassHead H := by
  letI : NeZero (4 * q) := ⟨by omega⟩
  let nf : (ZMod (4 * q) ⊕ ZMod (4 * q)) ≃ H :=
    normalFormEquiv a c horder hindex hc
  let e : DihedralGroup (4 * q) ≃ H :=
    DihedralGroup.equivSum.trans nf
  have hrsq :
      Nat.ModEq (4 * q)
        ((4 * q - 1) * (4 * q - 1)) 1 :=
    pred_sq_modEq_one (4 * q) (by omega)
  have hcsq' : c ^ 2 = a ^ 0 := by
    simpa only [pow_zero] using hcsq
  let me : DihedralGroup (4 * q) ≃* H :=
    MulEquiv.mk e (by
      intro x y
      cases x with
      | r i =>
          cases y with
          | r j =>
              exact
                (normalForm_rotation_mul_rotation
                  a c horder hindex hc i j).symm
          | sr j =>
              change
                nf (.inr (j - i)) =
                  nf (.inl i) * nf (.inr j)
              rw [normalForm_rotation_mul_coset
                a c horder hindex hc hconj hrsq]
              apply congrArg nf
              congr 1
              rw [pred_cast_eq_neg_one (4 * q) (by omega)]
              ring
      | sr i =>
          cases y with
          | r j =>
              exact
                (normalForm_coset_mul_rotation
                  a c horder hindex hc i j).symm
          | sr j =>
              change
                nf (.inl (j - i)) =
                  nf (.inr i) * nf (.inr j)
              rw [normalForm_coset_mul_coset
                a c horder hindex hc hconj hrsq hcsq']
              apply congrArg nf
              congr 1
              rw [pred_cast_eq_neg_one (4 * q) (by omega)]
              ring)
  exact .dihedral q hq me.symm

private def generalizedQuaternionHead
    (n : ℕ) (hn : 4 ≤ n)
    (a c : H)
    (horder : orderOf a = 2 * n)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (hconj :
      c * a * c⁻¹ = a ^ (2 * n - 1))
    (hcsq : c ^ 2 = a ^ n) :
    BergerMaximalClassHead H := by
  letI : NeZero (2 * n) := ⟨by omega⟩
  let nf : (ZMod (2 * n) ⊕ ZMod (2 * n)) ≃ H :=
    normalFormEquiv a c horder hindex hc
  let e : QuaternionGroup n ≃ H :=
    (quaternionEquivSum n).trans nf
  have hrsq :
      Nat.ModEq (2 * n)
        ((2 * n - 1) * (2 * n - 1)) 1 :=
    pred_sq_modEq_one (2 * n) (by omega)
  let me : QuaternionGroup n ≃* H :=
    MulEquiv.mk e (by
      intro x y
      cases x with
      | a i =>
          cases y with
          | a j =>
              exact
                (normalForm_rotation_mul_rotation
                  a c horder hindex hc i j).symm
          | xa j =>
              change
                nf (.inr (j - i)) =
                  nf (.inl i) * nf (.inr j)
              rw [normalForm_rotation_mul_coset
                a c horder hindex hc hconj hrsq]
              apply congrArg nf
              congr 1
              rw [pred_cast_eq_neg_one (2 * n) (by omega)]
              ring
      | xa i =>
          cases y with
          | a j =>
              exact
                (normalForm_coset_mul_rotation
                  a c horder hindex hc i j).symm
          | xa j =>
              change
                nf (.inl ((n : ZMod (2 * n)) + j - i)) =
                  nf (.inr i) * nf (.inr j)
              rw [normalForm_coset_mul_coset
                a c horder hindex hc hconj hrsq hcsq]
              apply congrArg nf
              congr 1
              rw [pred_cast_eq_neg_one (2 * n) (by omega)]
              ring)
  exact .generalizedQuaternion n hn me.symm

private def semidihedralHead
    (q : ℕ) (hq : 0 < q)
    (a c : H)
    (horder : orderOf a = 8 * q)
    (hindex : (Subgroup.zpowers a).index = 2)
    (hc : c ∉ Subgroup.zpowers a)
    (hconj :
      c * a * c⁻¹ = a ^ (4 * q - 1))
    (hcsq : c ^ 2 = 1) :
    BergerMaximalClassHead H := by
  letI : NeZero (8 * q) := ⟨by omega⟩
  let nf : (ZMod (8 * q) ⊕ ZMod (8 * q)) ≃ H :=
    normalFormEquiv a c horder hindex hc
  have hrsq :
      Nat.ModEq (8 * q)
        ((4 * q - 1) * (4 * q - 1)) 1 :=
    semidihedral_twist_sq_modEq_one q hq
  have hcsq' : c ^ 2 = a ^ 0 := by
    simpa only [pow_zero] using hcsq
  refine .semidihedral q hq ?_
  exact
    {
      normalForm := nf
      one_eq_rotation_zero := by
        change a ^ (0 : ZMod (8 * q)).val = 1
        simp only [ZMod.val_zero, pow_zero]
      rotation_mul_rotation := fun i j ↦
        normalForm_rotation_mul_rotation
          a c horder hindex hc i j
      rotation_mul_coset := fun i j ↦ by
        rw [normalForm_rotation_mul_coset
          a c horder hindex hc hconj hrsq]
        apply congrArg nf
        congr 1
        rw [semidihedral_twist_cast q hq]
      coset_mul_rotation := fun i j ↦
        normalForm_coset_mul_rotation
          a c horder hindex hc i j
      coset_mul_coset := fun i j ↦ by
        rw [normalForm_coset_mul_coset
          a c horder hindex hc hconj hrsq hcsq']
        apply congrArg nf
        congr 1
        rw [semidihedral_twist_cast q hq]
        ring
    }

private theorem fixed_by_pred_zero_or_half
    {h s : ℕ} (hh : 1 ≤ h)
    (hfix :
      Nat.ModEq (2 * h) ((2 * h - 1) * s) s) :
    Nat.ModEq (2 * h) s 0 ∨
      Nat.ModEq (2 * h) s h := by
  have hcoef : 1 ≤ 2 * h - 1 := by omega
  have hle :
      s ≤ (2 * h - 1) * s := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right s hcoef
  have hdiv :
      2 * h ∣ (2 * h - 1) * s - s :=
    (Nat.modEq_iff_dvd' hle).mp hfix.symm
  have hdiff :
      (2 * h - 1) * s - s =
        2 * ((h - 1) * s) := by
    calc
      (2 * h - 1) * s - s =
          ((2 * h - 1) - 1) * s := by
        simpa only [one_mul] using
          (Nat.sub_mul (2 * h - 1) 1 s).symm
      _ = 2 * ((h - 1) * s) := by
        rw [show (2 * h - 1) - 1 = 2 * (h - 1) by omega]
        ring
  have hhdiv : h ∣ (h - 1) * s := by
    apply
      (Nat.mul_dvd_mul_iff_left
        (by norm_num : 0 < 2)).mp
    simpa only [hdiff] using hdiv
  have hcoprime : h.Coprime (h - 1) := by
    exact
      (Nat.coprime_self_sub_right hh).2
        (Nat.coprime_one_right h)
  have hs : h ∣ s :=
    hcoprime.dvd_of_dvd_mul_left hhdiv
  exact modEq_two_mul_zero_or_self_of_dvd hs

private theorem fixed_by_semidihedral_zero_or_half
    {q s : ℕ} (hq : 1 ≤ q) (hqEven : Even q)
    (hfix :
      Nat.ModEq (4 * q) ((2 * q - 1) * s) s) :
    Nat.ModEq (4 * q) s 0 ∨
      Nat.ModEq (4 * q) s (2 * q) := by
  have hcoef : 1 ≤ 2 * q - 1 := by omega
  have hle :
      s ≤ (2 * q - 1) * s := by
    simpa only [one_mul] using
      Nat.mul_le_mul_right s hcoef
  have hdiv :
      4 * q ∣ (2 * q - 1) * s - s :=
    (Nat.modEq_iff_dvd' hle).mp hfix.symm
  have hdiff :
      (2 * q - 1) * s - s =
        2 * ((q - 1) * s) := by
    calc
      (2 * q - 1) * s - s =
          ((2 * q - 1) - 1) * s := by
        simpa only [one_mul] using
          (Nat.sub_mul (2 * q - 1) 1 s).symm
      _ = 2 * ((q - 1) * s) := by
        rw [show (2 * q - 1) - 1 = 2 * (q - 1) by omega]
        ring
  have hhalfDiv : 2 * q ∣ (q - 1) * s := by
    apply
      (Nat.mul_dvd_mul_iff_left
        (by norm_num : 0 < 2)).mp
    simpa only [show 4 * q = 2 * (2 * q) by ring,
      hdiff]
      using hdiv
  have hqPredCoprime : (q - 1).Coprime q := by
    exact
      (Nat.coprime_self_sub_left hq).2
        (Nat.coprime_one_left q)
  have hqPredOdd : Odd (q - 1) := by
    exact
      (Nat.odd_sub' hq).2
        (by simp only [odd_one, hqEven, iff_self])
  have hqPredTwo : (q - 1).Coprime 2 :=
    Nat.coprime_two_right.mpr hqPredOdd
  have hcoprime : (2 * q).Coprime (q - 1) :=
    (hqPredTwo.mul_right hqPredCoprime).symm
  have hs : 2 * q ∣ s :=
    hcoprime.dvd_of_dvd_mul_left hhalfDiv
  simpa only [show 4 * q = 2 * (2 * q) by ring] using
    (modEq_two_mul_zero_or_self_of_dvd hs)

omit [Finite H] in
private theorem conjugate_square_eq_inv
    (a b : H) {N k : ℕ}
    (horder : orderOf a = N)
    (hconj : b * a * b⁻¹ = a ^ k)
    (hneg :
      Nat.ModEq N (k * 2 + 2) 0) :
    b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹ := by
  have hp :
      a ^ (k * 2 + 2) = 1 := by
    rw [pow_eq_one_iff_modEq, horder]
    exact hneg
  have hmul :
      a ^ (k * 2) * a ^ 2 = 1 := by
    rw [← pow_add]
    exact hp
  calc
    b * a ^ 2 * b⁻¹ = a ^ (k * 2) :=
      conjugate_pow a b hconj 2
    _ = (a ^ 2)⁻¹ :=
      eq_inv_of_mul_eq_one_left hmul

/-- The classification together with the alignment retained from the supplied
rotation and coset representative. -/
theorem classification_and_alignment
    (hH : IsPGroup 2 H)
    (data : CyclicMaximalTwoGroupData H) :
    Nonempty (BergerMaximalClassHead H) ∧
      data.coset * (data.rotation ^ 2) * data.coset⁻¹ =
        (data.rotation ^ 2)⁻¹ := by
  classical
  let a : H := data.rotation
  let b : H := data.coset
  let A : Subgroup H := Subgroup.zpowers a
  change
    Nonempty (BergerMaximalClassHead H) ∧
      b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹
  have hindex : A.index = 2 := by
    simpa only [A, a] using data.rotation_index_two
  have hnormal : A.Normal :=
    Subgroup.normal_of_index_eq_two hindex
  letI : A.Normal := hnormal
  have hbNot : b ∉ A := by
    intro hb
    obtain ⟨z, hz⟩ :=
      Subgroup.mem_zpowers_iff.mp hb
    apply data.rotationSquare_not_commute
    change Commute (a ^ 2) b
    rw [← hz]
    exact ((Commute.refl a).pow_left 2).zpow_right z
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, horder⟩ :=
    (IsPGroup.iff_orderOf.mp hH) a
  have hge : 8 ≤ 2 ^ m := by
    simpa only [a, horder] using
      data.rotation_order_ge_eight
  have hm : 3 ≤ m := by
    by_contra hm'
    have hmle : m ≤ 2 := by omega
    interval_cases m <;> norm_num at hge
  have hconjMem : b * a * b⁻¹ ∈ A :=
    hnormal.conj_mem
      a (Subgroup.mem_zpowers a) b
  have hconjPowers :
      b * a * b⁻¹ ∈ Submonoid.powers a :=
    mem_powers_iff_mem_zpowers.mpr hconjMem
  obtain ⟨k, hk⟩ :=
    (Submonoid.mem_powers_iff
      (b * a * b⁻¹) a).mp hconjPowers
  have hconj :
      b * a * b⁻¹ = a ^ k :=
    hk.symm
  have hsqPowers :
      b ^ 2 ∈ Submonoid.powers a :=
    mem_powers_iff_mem_zpowers.mpr
      (by
        simpa only [A] using
          data.cosetSquare_mem_rotation)
  obtain ⟨s, hs⟩ :=
    (Submonoid.mem_powers_iff (b ^ 2) a).mp
      hsqPowers
  have hsq : a ^ s = b ^ 2 := hs
  have hbsqCommute : Commute (b ^ 2) a := by
    rw [← hsq]
    exact (Commute.refl a).pow_left s
  have hkkPow : a ^ (k * k) = a := by
    calc
      a ^ (k * k) = (a ^ k) ^ k := pow_mul a k k
      _ = (b * a * b⁻¹) ^ k := by rw [hconj]
      _ = b * a ^ k * b⁻¹ := conj_pow
      _ = b * (b * a * b⁻¹) * b⁻¹ := by
        rw [hconj]
      _ = b ^ 2 * a * (b ^ 2)⁻¹ := by
        simp only [pow_two]
        group
      _ = a := by
        rw [hbsqCommute.eq]
        group
  have hkk :
      Nat.ModEq (2 ^ m) (k * k) 1 := by
    have hkkPow' : a ^ (k * k) = a ^ 1 := by
      simpa only [pow_one] using hkkPow
    simpa only [horder] using
      (pow_eq_pow_iff_modEq.mp hkkPow')
  have hfixPow : a ^ (k * s) = a ^ s := by
    calc
      a ^ (k * s) =
          b * a ^ s * b⁻¹ :=
        (conjugate_pow a b hconj s).symm
      _ = b * b ^ 2 * b⁻¹ := by rw [hs]
      _ = b ^ 2 := by group
      _ = a ^ s := hs.symm
  have hfix :
      Nat.ModEq (2 ^ m) (k * s) s := by
    simpa only [horder] using
      (pow_eq_pow_iff_modEq.mp hfixPow)
  have hhalf :
      2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    calc
      2 ^ (m - 1) = 2 ^ ((m - 2) + 1) := by
        congr 1
        omega
      _ = 2 * 2 ^ (m - 2) := by
        rw [pow_add]
        ring
  have hfour :
      2 ^ m = 4 * 2 ^ (m - 2) := by
    calc
      2 ^ m = 2 ^ ((m - 2) + 2) := by
        congr 1
        omega
      _ = 4 * 2 ^ (m - 2) := by
        rw [pow_add]
        ring
  have height :
      2 ^ m = 8 * 2 ^ (m - 3) := by
    calc
      2 ^ m = 2 ^ ((m - 3) + 3) := by
        congr 1
        omega
      _ = 8 * 2 ^ (m - 3) := by
        rw [pow_add]
        ring
  have hhalfEight :
      2 ^ (m - 1) = 4 * 2 ^ (m - 3) := by
    calc
      2 ^ (m - 1) = 2 ^ ((m - 3) + 2) := by
        congr 1
        omega
      _ = 4 * 2 ^ (m - 3) := by
        rw [pow_add]
        ring
  have hqFour : 2 ≤ 2 ^ (m - 2) := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (by norm_num : 0 < 2)
        (show 1 ≤ m - 2 by omega))
  have hqFourEven : Even (2 ^ (m - 2)) := by
    rw [Nat.even_pow]
    exact ⟨even_two, by omega⟩
  have hqEight : 0 < 2 ^ (m - 3) :=
    Nat.two_pow_pos _
  have htwoHalf :
      2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [hhalf, hfour]
    ring
  have hne :
      ¬Nat.ModEq (2 ^ (m - 1)) k 1 := by
    intro hkHalf
    have htwo :
        Nat.ModEq (2 ^ m) (k * 2) 2 := by
      have hscaled := hkHalf.mul_right' 2
      simpa only [one_mul, mul_comm, htwoHalf] using hscaled
    have hpowTwo : a ^ (k * 2) = a ^ 2 := by
      rw [pow_eq_pow_iff_modEq, horder]
      exact htwo
    have hconjTwo :
        b * a ^ 2 * b⁻¹ = a ^ 2 :=
      (conjugate_pow a b hconj 2).trans hpowTwo
    apply data.rotationSquare_not_commute
    change Commute (a ^ 2) b
    rw [Commute]
    have hba : b * a ^ 2 = a ^ 2 * b := by
      calc
        b * a ^ 2 =
            (b * a ^ 2 * b⁻¹) * b := by group
        _ = a ^ 2 * b := by rw [hconjTwo]
    exact hba.symm
  rcases
      modEq_neg_one_or_half_pred_of_sq_modEq_one
        hm hkk hne with
    hkInv | hkSemi
  · have hconjInv :
        b * a * b⁻¹ = a ^ (2 ^ m - 1) := by
      calc
        b * a * b⁻¹ = a ^ k := hconj
        _ = a ^ (2 ^ m - 1) := by
          rw [pow_eq_pow_iff_modEq, horder]
          exact hkInv
    have hneg :
        Nat.ModEq (2 ^ m) (k * 2 + 2) 0 := by
      calc
        k * 2 + 2 ≡
            (2 ^ m - 1) * 2 + 2 [MOD 2 ^ m] :=
          (hkInv.mul_right 2).add_right 2
        _ = (2 ^ m) * 2 + 0 := by
          omega
        _ ≡ 0 [MOD 2 ^ m] :=
          Nat.ModEq.modulus_mul_add
    have halign :
        b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹ :=
      conjugate_square_eq_inv a b horder hconj hneg
    have hfixInv :
        Nat.ModEq (2 ^ m)
          ((2 ^ m - 1) * s) s :=
      (hkInv.mul_right s).symm.trans hfix
    have hsCases :
        Nat.ModEq (2 ^ m) s 0 ∨
          Nat.ModEq (2 ^ m) s (2 ^ (m - 1)) := by
      simpa only [htwoHalf] using
        (fixed_by_pred_zero_or_half
          (Nat.one_le_pow (m - 1) 2 (by norm_num))
          (by simpa only [htwoHalf] using hfixInv))
    rcases hsCases with hsZero | hsHalf
    · have hbSq : b ^ 2 = 1 := by
        rw [← hs]
        rw [pow_eq_one_iff_modEq, horder]
        exact hsZero
      refine ⟨?_, halign⟩
      exact ⟨
        dihedralHead
          (2 ^ (m - 2)) hqFour a b
          (by simpa only [hfour] using horder)
          (by simpa only [A] using hindex)
          (by simpa only [A] using hbNot)
          (by simpa only [hfour] using hconjInv)
          hbSq⟩
    · have hbSq :
          b ^ 2 = a ^ (2 ^ (m - 1)) := by
        rw [← hs]
        rw [pow_eq_pow_iff_modEq, horder]
        exact hsHalf
      refine ⟨?_, halign⟩
      exact ⟨
        generalizedQuaternionHead
          (2 ^ (m - 1))
          (by omega) a b
          (by simpa only [htwoHalf] using horder)
          (by simpa only [A] using hindex)
          (by simpa only [A] using hbNot)
          (by simpa only [htwoHalf] using hconjInv)
          hbSq⟩
  · have hconjSemi :
        b * a * b⁻¹ =
          a ^ (2 ^ (m - 1) - 1) := by
      calc
        b * a * b⁻¹ = a ^ k := hconj
        _ = a ^ (2 ^ (m - 1) - 1) := by
          rw [pow_eq_pow_iff_modEq, horder]
          exact hkSemi
    have hneg :
        Nat.ModEq (2 ^ m) (k * 2 + 2) 0 := by
      calc
        k * 2 + 2 ≡
            (2 ^ (m - 1) - 1) * 2 + 2
              [MOD 2 ^ m] :=
          (hkSemi.mul_right 2).add_right 2
        _ = 2 ^ m := by
          rw [hhalf]
          omega
        _ ≡ 0 [MOD 2 ^ m] :=
          Nat.modulus_modEq_zero
    have halign :
        b * a ^ 2 * b⁻¹ = (a ^ 2)⁻¹ :=
      conjugate_square_eq_inv a b horder hconj hneg
    have hfixSemi :
        Nat.ModEq (2 ^ m)
          ((2 ^ (m - 1) - 1) * s) s :=
      (hkSemi.mul_right s).symm.trans hfix
    have hsCases :
        Nat.ModEq (2 ^ m) s 0 ∨
          Nat.ModEq (2 ^ m) s (2 ^ (m - 1)) := by
      simpa only [hfour, hhalf] using
        (fixed_by_semidihedral_zero_or_half
          (Nat.one_le_pow (m - 2) 2 (by norm_num))
          hqFourEven
          (by simpa only [hfour, hhalf] using hfixSemi))
    have hrSq :
        Nat.ModEq (2 ^ m)
          ((2 ^ (m - 1) - 1) *
            (2 ^ (m - 1) - 1)) 1 :=
      (hkSemi.mul hkSemi).symm.trans hkk
    rcases hsCases with hsZero | hsHalf
    · have hbSq : b ^ 2 = 1 := by
        rw [← hs]
        rw [pow_eq_one_iff_modEq, horder]
        exact hsZero
      refine ⟨?_, halign⟩
      exact ⟨
        semidihedralHead
          (2 ^ (m - 3)) hqEight a b
          (by simpa only [height] using horder)
          (by simpa only [A] using hindex)
          (by simpa only [A] using hbNot)
          (by simpa only [hhalfEight] using hconjSemi)
          hbSq⟩
    · have hbSq :
          b ^ 2 = a ^ (2 ^ (m - 1)) := by
        rw [← hs]
        rw [pow_eq_pow_iff_modEq, horder]
        exact hsHalf
      let c : H := b * a
      have hcNot : c ∉ A := by
        intro hc
        apply hbNot
        apply
          (A.mul_mem_cancel_right
            (Subgroup.mem_zpowers a)).mp
        exact hc
      have hcConj :
          c * a * c⁻¹ =
            a ^ (2 ^ (m - 1) - 1) := by
        calc
          c * a * c⁻¹ = b * a * b⁻¹ := by
            dsimp only [c]
            group
          _ = a ^ (2 ^ (m - 1) - 1) :=
            hconjSemi
      have hmove :
          a * b =
            b * a ^ (2 ^ (m - 1) - 1) := by
        simpa only [pow_one, mul_one] using
          (rotation_mul_coset a b horder
            hconjSemi hrSq 1)
      have hcSq : c ^ 2 = 1 := by
        have hp :
            a ^
                (2 ^ (m - 1) +
                  ((2 ^ (m - 1) - 1) + 1)) =
              1 := by
          rw [pow_eq_one_iff_modEq, horder]
          rw [show
            2 ^ (m - 1) +
                ((2 ^ (m - 1) - 1) + 1) =
              2 ^ m by
                rw [hhalf]
                omega]
          exact Nat.modulus_modEq_zero
        calc
          c ^ 2 = (b * a) * (b * a) := by
            simp only [c, pow_two]
          _ = b * (a * b) * a := by group
          _ =
              b * (b *
                a ^ (2 ^ (m - 1) - 1)) * a := by
            rw [hmove]
          _ =
              b ^ 2 *
                (a ^ (2 ^ (m - 1) - 1) * a) := by
            simp only [pow_two]
            group
          _ =
              a ^ (2 ^ (m - 1)) *
                (a ^ (2 ^ (m - 1) - 1) * a) := by
            rw [hbSq]
          _ =
              a ^ (2 ^ (m - 1)) *
                a ^ ((2 ^ (m - 1) - 1) + 1) := by
            congr 1
            exact
              (pow_succ a (2 ^ (m - 1) - 1)).symm
          _ =
              a ^
                (2 ^ (m - 1) +
                  ((2 ^ (m - 1) - 1) + 1)) := by
            exact
              (pow_add a (2 ^ (m - 1))
                ((2 ^ (m - 1) - 1) + 1)).symm
          _ = 1 := hp
      refine ⟨?_, halign⟩
      exact ⟨
        semidihedralHead
          (2 ^ (m - 3)) hqEight a c
          (by simpa only [height] using horder)
          (by simpa only [A] using hindex)
          (by simpa only [A] using hcNot)
          (by simpa only [hhalfEight] using hcConj)
          hcSq⟩

end CyclicMaximalTwoGroup

namespace CyclicMaximalTwoGroupData

variable {H : Type u} [Group H] [Finite H]

/-- The maximal-class head classified from cyclic-maximal two-group data. -/
theorem maximalClassHead
    (data : CyclicMaximalTwoGroupData H)
    (hH : IsPGroup 2 H) :
    Nonempty (BergerMaximalClassHead H) :=
  (CyclicMaximalTwoGroup.classification_and_alignment hH data).1

/-- The supplied coset representative inverts the square of the supplied
rotation.  This alignment statement does not depend on any choices made in
the resulting maximal-class presentation. -/
theorem coset_conj_rotation_sq_inv
    (data : CyclicMaximalTwoGroupData H)
    (hH : IsPGroup 2 H) :
    data.coset * (data.rotation ^ 2) * data.coset⁻¹ =
      (data.rotation ^ 2)⁻¹ :=
  (CyclicMaximalTwoGroup.classification_and_alignment hH data).2

end CyclicMaximalTwoGroupData

/-- The classical cyclic-maximal-subgroup classification, in the exact form
isolated by `CyclicMaximalTwoGroupClassificationStatement`. -/
theorem cyclicMaximalTwoGroupClassification :
    CyclicMaximalTwoGroupClassificationStatement := by
  unfold CyclicMaximalTwoGroupClassificationStatement
  intro H _ _ hH data
  exact data.maximalClassHead hH

end LisiSabatini
