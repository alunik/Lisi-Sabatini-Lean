import LisiSabatini.TwoCoreSymplecticTypeFrontier

/-!
# The distinguished rotation in a maximal-class head

This file packages the elementary normal-form facts about the cyclic
rotation subgroup of a dihedral, semidihedral, or generalized-quaternion
head.  In every case the chosen rotation has order `rotationOrder`, its
half-power is the unique nonidentity central involution, and a standard
coset element does not commute with it.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

namespace IsSemidihedralPresentation

variable {H : Type u} [Group H] [Finite H] {k : ℕ}

omit [Finite H] in
@[simp] theorem rotation_one_pow
    (h : IsSemidihedralPresentation H k) (m : ℕ) :
    h.rotation 1 ^ m = h.rotation (m : ZMod (8 * k)) := by
  induction m with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, h.rotation_zero]
  | succ m ih =>
      rw [pow_succ, ih, h.rotation_mul_rotation_apply]
      congr 1
      norm_cast

/-- The standard semidihedral rotation has the advertised order. -/
theorem orderOf_rotation_one
    (h : IsSemidihedralPresentation H k) (hk : 0 < k) :
    orderOf (h.rotation 1) = 8 * k := by
  letI : NeZero (8 * k) := ⟨by omega⟩
  apply
    (Nat.le_of_dvd (by omega)
      (orderOf_dvd_of_pow_eq_one (by
        rw [h.rotation_one_pow]
        simp))).antisymm
  by_contra hlt
  have hlt' : orderOf (h.rotation 1) < 8 * k := by omega
  have hp := pow_orderOf_eq_one (h.rotation 1)
  rw [h.rotation_one_pow] at hp
  have hz :
      ((orderOf (h.rotation 1) : ℕ) : ZMod (8 * k)) = 0 := by
    apply h.rotation_injective
    simpa using hp
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_natCast, ZMod.val_zero,
    Nat.mod_eq_of_lt hlt'] at hval
  exact (orderOf_pos (h.rotation 1)).ne' hval

end IsSemidihedralPresentation

namespace BergerMaximalClassHead

variable {H : Type u} [Group H] [Finite H]

/-- The canonical generator of the cyclic rotation subgroup. -/
def rotation (head : BergerMaximalClassHead H) : H :=
  match head with
  | .dihedral _ _ equiv =>
      equiv.symm (DihedralGroup.r 1)
  | .semidihedral _ _ presentation =>
      presentation.rotation 1
  | .generalizedQuaternion _ _ equiv =>
      equiv.symm (QuaternionGroup.a 1)

/-- A standard element outside the cyclic rotation subgroup. -/
def companion (head : BergerMaximalClassHead H) : H :=
  match head with
  | .dihedral _ _ equiv =>
      equiv.symm (DihedralGroup.sr 0)
  | .semidihedral _ _ presentation =>
      presentation.coset 0
  | .generalizedQuaternion _ _ equiv =>
      equiv.symm (QuaternionGroup.xa 0)

/-- The central half-turn of the rotation subgroup. -/
def halfTurn (head : BergerMaximalClassHead H) : H :=
  head.rotation ^ (head.rotationOrder / 2)

theorem orderOf_rotation
    (head : BergerMaximalClassHead H) :
    orderOf head.rotation = head.rotationOrder := by
  cases head with
  | dihedral k hk equiv =>
      simp only [rotation, rotationOrder]
      rw [equiv.symm.orderOf_eq]
      exact DihedralGroup.orderOf_r_one
  | semidihedral k hk presentation =>
      simpa only [rotation, rotationOrder] using
        presentation.orderOf_rotation_one hk
  | generalizedQuaternion n hn equiv =>
      simp only [rotation, rotationOrder]
      rw [equiv.symm.orderOf_eq]
      exact QuaternionGroup.orderOf_a_one

private theorem quaternion_halfTurn_mem_center
    (n : ℕ) (hn : 0 < n) :
    QuaternionGroup.a
        ((n : ℕ) : ZMod (2 * n)) ∈
      Subgroup.center (QuaternionGroup n) := by
  letI : NeZero n := ⟨hn.ne'⟩
  apply quaternionGroup_allInvolutionsCentral n
  apply orderOf_eq_prime
  · rw [pow_two, QuaternionGroup.a_mul_a]
    rw [← QuaternionGroup.a_zero]
    congr 1
    have hcast :
        ((2 * n : ℕ) : ZMod (2 * n)) = 0 := by simp
    simpa [Nat.cast_mul, two_mul] using hcast
  · intro h
    have hz :
        ((n : ℕ) : ZMod (2 * n)) = 0 := by
      exact QuaternionGroup.a.inj
        (h.trans QuaternionGroup.a_zero.symm)
    have hval := congrArg ZMod.val hz
    rw [ZMod.val_natCast, ZMod.val_zero] at hval
    have hlt : n < 2 * n := by omega
    rw [Nat.mod_eq_of_lt hlt] at hval
    omega

private theorem quaternion_halfTurn_ne_one
    (n : ℕ) (hn : 0 < n) :
    QuaternionGroup.a
        ((n : ℕ) : ZMod (2 * n)) ≠ 1 := by
  intro h
  have hz :
      ((n : ℕ) : ZMod (2 * n)) = 0 := by
    exact QuaternionGroup.a.inj
      (h.trans QuaternionGroup.a_zero.symm)
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_natCast, ZMod.val_zero] at hval
  have hlt : n < 2 * n := by omega
  rw [Nat.mod_eq_of_lt hlt] at hval
  omega

private theorem quaternion_halfTurn_sq
    (n : ℕ) :
    QuaternionGroup.a
        ((n : ℕ) : ZMod (2 * n)) ^ 2 = 1 := by
  rw [pow_two, QuaternionGroup.a_mul_a]
  rw [← QuaternionGroup.a_zero]
  congr 1
  have hcast :
      ((2 * n : ℕ) : ZMod (2 * n)) = 0 := by simp
  simpa [Nat.cast_mul, two_mul] using hcast

theorem halfTurn_mem_center
    (head : BergerMaximalClassHead H) :
    head.halfTurn ∈ Subgroup.center H := by
  cases head with
  | dihedral k hk equiv =>
      have hdiv : 4 * k / 2 = 2 * k := by omega
      apply (MulEquivClass.apply_mem_center_iff equiv).mp
      simpa [halfTurn, rotation, rotationOrder, hdiv] using
        DihedralGroup.r_two_mul_mem_center k
  | semidihedral k hk presentation =>
      have hdiv : 8 * k / 2 = 4 * k := by omega
      simpa [halfTurn, rotation, rotationOrder,
        presentation.rotation_one_pow, hdiv] using
          presentation.halfTurn_mem_center
  | generalizedQuaternion n hn equiv =>
      have hdiv : 2 * n / 2 = n := by omega
      apply (MulEquivClass.apply_mem_center_iff equiv).mp
      simpa [halfTurn, rotation, rotationOrder, hdiv] using
        quaternion_halfTurn_mem_center n (by omega)

theorem halfTurn_ne_one
    (head : BergerMaximalClassHead H) :
    head.halfTurn ≠ 1 := by
  cases head with
  | dihedral k hk equiv =>
      have hdiv : 4 * k / 2 = 2 * k := by omega
      intro h
      apply DihedralGroup.r_two_mul_ne_one k (by omega)
      have := congrArg equiv h
      simpa [halfTurn, rotation, rotationOrder, hdiv] using this
  | semidihedral k hk presentation =>
      have hdiv : 8 * k / 2 = 4 * k := by omega
      simpa [halfTurn, rotation, rotationOrder,
        presentation.rotation_one_pow, hdiv] using
          presentation.halfTurn_ne_one hk
  | generalizedQuaternion n hn equiv =>
      have hdiv : 2 * n / 2 = n := by omega
      intro h
      apply quaternion_halfTurn_ne_one n (by omega)
      have := congrArg equiv h
      simpa [halfTurn, rotation, rotationOrder, hdiv] using this

theorem halfTurn_sq
    (head : BergerMaximalClassHead H) :
    head.halfTurn ^ 2 = 1 := by
  cases head with
  | dihedral k hk equiv =>
      have hdiv : 4 * k / 2 = 2 * k := by omega
      apply equiv.injective
      simpa [halfTurn, rotation, rotationOrder, hdiv] using
        DihedralGroup.r_two_mul_sq k
  | semidihedral k hk presentation =>
      have hdiv : 8 * k / 2 = 4 * k := by omega
      simpa [halfTurn, rotation, rotationOrder,
        presentation.rotation_one_pow, hdiv] using
          presentation.halfTurn_sq
  | generalizedQuaternion n hn equiv =>
      have hdiv : 2 * n / 2 = n := by omega
      apply equiv.injective
      simpa [halfTurn, rotation, rotationOrder, hdiv] using
        quaternion_halfTurn_sq n

/-- The standard companion witnesses that every head is noncommutative. -/
theorem rotation_companion_ne_companion_rotation
    (head : BergerMaximalClassHead H) :
    head.rotation * head.companion ≠
      head.companion * head.rotation := by
  cases head with
  | dihedral k hk equiv =>
      intro h
      have h' := congrArg equiv h
      simp only [rotation, companion, map_mul,
        MulEquiv.apply_symm_apply, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, zero_sub, zero_add] at h'
      have hz :
          (-1 : ZMod (4 * k)) = 1 :=
        DihedralGroup.sr.inj h'
      have htwo : (2 : ZMod (4 * k)) = 0 := by
        calc
          (2 : ZMod (4 * k)) = 1 + 1 := by norm_num
          _ = -1 + 1 :=
            congrArg (fun t : ZMod (4 * k) ↦ t + 1) hz.symm
          _ = 0 := by simp
      have hdvd : 4 * k ∣ 2 :=
        (ZMod.natCast_eq_zero_iff 2 (4 * k)).mp htwo
      exact (not_le_of_gt (by omega : 2 < 4 * k))
        (Nat.le_of_dvd (by omega) hdvd)
  | semidihedral k hk presentation =>
      intro h
      simp only [rotation, companion,
        presentation.rotation_mul_coset_apply,
        presentation.coset_mul_rotation_apply] at h
      have hz :
          semidihedralTwist k = 1 :=
        presentation.coset_injective (by simpa using h)
      have hcast :
          ((4 * k : ℕ) : ZMod (8 * k)) = 2 := by
        dsimp only [semidihedralTwist] at hz
        linear_combination hz
      have hmod : 4 * k ≡ 2 [MOD 8 * k] :=
        (ZMod.natCast_eq_natCast_iff (4 * k) 2 (8 * k)).mp
          (by simpa using hcast)
      have hdvd : 8 * k ∣ 4 * k - 2 :=
        (Nat.modEq_iff_dvd' (by omega : 2 ≤ 4 * k)).mp
          hmod.symm
      exact (not_le_of_gt (by omega : 4 * k - 2 < 8 * k))
        (Nat.le_of_dvd (by omega) hdvd)
  | generalizedQuaternion n hn equiv =>
      intro h
      have h' := congrArg equiv h
      simp only [rotation, companion, map_mul,
        MulEquiv.apply_symm_apply, QuaternionGroup.a_mul_xa,
        QuaternionGroup.xa_mul_a, zero_sub, zero_add] at h'
      have hz :
          (-1 : ZMod (2 * n)) = 1 :=
        QuaternionGroup.xa.inj h'
      have htwo : (2 : ZMod (2 * n)) = 0 := by
        calc
          (2 : ZMod (2 * n)) = 1 + 1 := by norm_num
          _ = -1 + 1 :=
            congrArg (fun t : ZMod (2 * n) ↦ t + 1) hz.symm
          _ = 0 := by simp
      have hdvd : 2 * n ∣ 2 :=
        (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp htwo
      exact (not_le_of_gt (by omega : 2 < 2 * n))
        (Nat.le_of_dvd (by omega) hdvd)

private theorem zmod_eq_half_of_two_mul_eq_zero
    (N : ℕ) (hN : 0 < N) (hEven : Even N)
    (i : ZMod N) (hiSq : i + i = 0) (hiNe : i ≠ 0) :
    i = ((N / 2 : ℕ) : ZMod N) := by
  letI : NeZero N := ⟨hN.ne'⟩
  have hdiv : N ∣ 2 * i.val := by
    have hcast : ((2 * i.val : ℕ) : ZMod N) = 0 := by
      rw [Nat.cast_mul, Nat.cast_ofNat,
        ← ZMod.natCast_zmod_val i]
      simpa [two_mul] using hiSq
    exact (ZMod.natCast_eq_zero_iff (2 * i.val) N).mp hcast
  have hiValPos : 0 < i.val := by
    exact Nat.pos_of_ne_zero fun hzero =>
      hiNe (i.val_eq_zero.mp hzero)
  have hiValLt : i.val < N := i.val_lt
  have hbounds :
      N ≤ 2 * i.val ∧ 2 * i.val < 2 * N := by
    constructor
    · exact Nat.le_of_dvd (by omega) hdiv
    · omega
  have hEq : 2 * i.val = N := by
    exact Nat.eq_of_dvd_of_lt_two_mul
      (by omega : 2 * i.val ≠ 0) hdiv hbounds.2
  apply ZMod.val_injective
  rw [ZMod.val_natCast]
  have hhalfLt : N / 2 < N := by
    have hNtwo : 2 ≤ N := by
      obtain ⟨m, rfl⟩ := hEven
      omega
    omega
  rw [Nat.mod_eq_of_lt hhalfLt]
  omega

/-- The half-turn is the unique nonidentity central involution of a
maximal-class head. -/
theorem eq_halfTurn_of_mem_center_of_sq_eq_one_of_ne_one
    (head : BergerMaximalClassHead H)
    (z : H) (hzCenter : z ∈ Subgroup.center H)
    (hzSq : z ^ 2 = 1) (hzNe : z ≠ 1) :
    z = head.halfTurn := by
  cases head with
  | dihedral k hk equiv =>
      cases hzImage : equiv z with
      | r i =>
          have hiSq : i + i = 0 := by
            have hzSqMap :
                (equiv z) ^ 2 = 1 := by
              simpa using congrArg equiv hzSq
            rw [hzImage] at hzSqMap
            apply DihedralGroup.r.inj
            simpa only [pow_two, DihedralGroup.r_mul_r,
              DihedralGroup.r_zero] using hzSqMap
          have hiNe : i ≠ 0 := by
            intro hi
            apply hzNe
            apply equiv.injective
            simp [hzImage, hi]
          have hi :=
            zmod_eq_half_of_two_mul_eq_zero
              (4 * k) (by omega) ⟨2 * k, by omega⟩
              i hiSq hiNe
          apply equiv.injective
          have hdiv : 4 * k / 2 = 2 * k := by omega
          simp [hzImage, halfTurn, rotation, rotationOrder,
            hi, hdiv]
      | sr i =>
          exfalso
          have hc :=
            Subgroup.mem_center_iff.mp
              ((MulEquivClass.apply_mem_center_iff equiv).mpr
                hzCenter)
              (DihedralGroup.r (1 : ZMod (4 * k)))
          simp only [hzImage, DihedralGroup.sr_mul_r,
            DihedralGroup.r_mul_sr] at hc
          have hi : i + 1 = i - 1 :=
            DihedralGroup.sr.inj hc.symm
          have htwo : (2 : ZMod (4 * k)) = 0 := by
            linear_combination hi
          have hcast :=
            (ZMod.natCast_eq_zero_iff 2 (4 * k)).mp htwo
          have : 4 * k ∣ 2 := by simpa using hcast
          exact (not_le_of_gt (by omega : 2 < 4 * k))
            (Nat.le_of_dvd (by omega) this)
  | semidihedral k hk presentation =>
      rcases presentation.exists_rotation_or_coset z with
        ⟨i, rfl⟩ | ⟨i, rfl⟩
      · have hiSq : i + i = 0 := by
          apply presentation.rotation_injective
          simpa only [pow_two,
            presentation.rotation_mul_rotation_apply,
            presentation.rotation_zero] using hzSq
        have hiNe : i ≠ 0 := by
          intro hi
          apply hzNe
          simp [hi]
        have hi :=
          zmod_eq_half_of_two_mul_eq_zero
            (8 * k) (by omega) ⟨4 * k, by omega⟩
            i hiSq hiNe
        have hdiv : 8 * k / 2 = 4 * k := by omega
        simp [halfTurn, rotation, rotationOrder,
          presentation.rotation_one_pow, hi, hdiv]
      · exfalso
        have hc :=
          Subgroup.mem_center_iff.mp hzCenter
            (presentation.rotation (1 : ZMod (8 * k)))
        simp only [presentation.coset_mul_rotation_apply,
          presentation.rotation_mul_coset_apply] at hc
        have hi :
            i + 1 = i + semidihedralTwist k :=
          presentation.coset_injective (by simpa using hc.symm)
        have htwist :
            (1 : ZMod (8 * k)) = semidihedralTwist k := by
          exact add_left_cancel hi
        have hcast :
            ((4 * k : ℕ) : ZMod (8 * k)) = 2 := by
          dsimp only [semidihedralTwist] at htwist
          calc
            ((4 * k : ℕ) : ZMod (8 * k)) =
                (((4 * k : ℕ) : ZMod (8 * k)) - 1) + 1 := by
              ring
            _ = 1 + 1 :=
              congrArg (fun t : ZMod (8 * k) ↦ t + 1)
                htwist.symm
            _ = 2 := by norm_num
        have hmod : 4 * k ≡ 2 [MOD 8 * k] :=
          (ZMod.natCast_eq_natCast_iff
            (4 * k) 2 (8 * k)).mp (by simpa using hcast)
        have hdvd : 8 * k ∣ 4 * k - 2 :=
          (Nat.modEq_iff_dvd' (by omega : 2 ≤ 4 * k)).mp
            hmod.symm
        exact (not_le_of_gt (by omega : 4 * k - 2 < 8 * k))
          (Nat.le_of_dvd (by omega) hdvd)
  | generalizedQuaternion n hn equiv =>
      cases hzImage : equiv z with
      | a i =>
          have hiSq : i + i = 0 := by
            have hzSqMap :
                (equiv z) ^ 2 = 1 := by
              simpa using congrArg equiv hzSq
            rw [hzImage] at hzSqMap
            apply QuaternionGroup.a.inj
            simpa only [pow_two, QuaternionGroup.a_mul_a,
              QuaternionGroup.a_zero] using hzSqMap
          have hiNe : i ≠ 0 := by
            intro hi
            apply hzNe
            apply equiv.injective
            simp [hzImage, hi]
          have hi :=
            zmod_eq_half_of_two_mul_eq_zero
              (2 * n) (by omega) ⟨n, by omega⟩
              i hiSq hiNe
          apply equiv.injective
          have hdiv : 2 * n / 2 = n := by omega
          simp [hzImage, halfTurn, rotation, rotationOrder,
            hi, hdiv]
      | xa i =>
          exfalso
          have hc :=
            Subgroup.mem_center_iff.mp
              ((MulEquivClass.apply_mem_center_iff equiv).mpr
                hzCenter)
              (QuaternionGroup.a (1 : ZMod (2 * n)))
          simp only [hzImage, QuaternionGroup.xa_mul_a,
            QuaternionGroup.a_mul_xa] at hc
          have hi : i + 1 = i - 1 :=
            QuaternionGroup.xa.inj hc.symm
          have htwo : (2 : ZMod (2 * n)) = 0 := by
            linear_combination hi
          have hcast :=
            (ZMod.natCast_eq_zero_iff 2 (2 * n)).mp htwo
          have : 2 * n ∣ 2 := by simpa using hcast
          exact (not_le_of_gt (by omega : 2 < 2 * n))
            (Nat.le_of_dvd (by omega) this)

end BergerMaximalClassHead

end LisiSabatini
