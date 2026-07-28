module

public import LisiSabatini.TwoCoreSymplecticTypeStructure
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

/-!
# The dihedral symplectic-type branch

Mathlib supplies explicit normal forms for `DihedralGroup n`.  This file
uses them to prove the two facts needed by the affine two-base count:

* every noncentral involution is a reflection;
* when the rotation order is divisible by four, every reflection admits a
  commutator cycle through the central half-turn.

Thus an active involution in a fixed-point-free-center linear copy of
`DihedralGroup (4*k)` has a half-dimensional fixed space.  We also bound
the number of active involutions by the number of reflections.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

namespace DihedralGroup

/-- A rotation of order two is central in a dihedral group. -/
theorem r_mem_center_of_orderOf_eq_two
    {n : ℕ} (i : ZMod n)
    (hi : orderOf (DihedralGroup.r i) = 2) :
    DihedralGroup.r i ∈
      Subgroup.center (DihedralGroup n) := by
  have hiSq : DihedralGroup.r i ^ 2 = 1 := by
    rw [← hi]
    exact pow_orderOf_eq_one (DihedralGroup.r i)
  have hiTwo : i + i = 0 := by
    simpa [pow_two, DihedralGroup.one_def] using
      DihedralGroup.r.inj hiSq
  rw [Subgroup.mem_center_iff]
  intro y
  cases y with
  | r j =>
      simp only [DihedralGroup.r_mul_r]
      exact congrArg DihedralGroup.r (add_comm j i)
  | sr j =>
      simp only [DihedralGroup.sr_mul_r,
        DihedralGroup.r_mul_sr]
      apply congrArg DihedralGroup.sr
      have hneg : -i = i :=
        (neg_eq_iff_add_eq_zero).2 hiTwo
      rw [sub_eq_add_neg, hneg]

private theorem halfTurn_add_halfTurn
    (k : ℕ) :
    ((2 * k : ℕ) : ZMod (4 * k)) +
        ((2 * k : ℕ) : ZMod (4 * k)) = 0 := by
  have hmod :
      ((4 * k : ℕ) : ZMod (4 * k)) = 0 := by simp
  have hmod' :
      (4 : ZMod (4 * k)) * (k : ZMod (4 * k)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmod
  norm_num [Nat.cast_mul]
  linear_combination hmod'

/-- The half-turn is central. -/
theorem r_two_mul_mem_center
    (k : ℕ) :
    DihedralGroup.r ((2 * k : ℕ) : ZMod (4 * k)) ∈
      Subgroup.center (DihedralGroup (4 * k)) := by
  let t : ZMod (4 * k) := (2 * k : ℕ)
  have htNeg : -t = t := by
    exact (neg_eq_iff_add_eq_zero).2 (halfTurn_add_halfTurn k)
  rw [Subgroup.mem_center_iff]
  intro y
  cases y with
  | r j =>
      simp only [DihedralGroup.r_mul_r]
      exact congrArg DihedralGroup.r (add_comm j t)
  | sr j =>
      simp only [DihedralGroup.sr_mul_r,
        DihedralGroup.r_mul_sr]
      apply congrArg DihedralGroup.sr
      rw [sub_eq_add_neg, htNeg]

/-- In positive rotation order, the half-turn is nontrivial. -/
theorem r_two_mul_ne_one
    (k : ℕ) (hk : 0 < k) :
    DihedralGroup.r ((2 * k : ℕ) : ZMod (4 * k)) ≠ 1 := by
  intro h
  have hz :
      ((2 * k : ℕ) : ZMod (4 * k)) = 0 := by
    exact DihedralGroup.r.inj
      (h.trans DihedralGroup.r_zero.symm)
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_natCast, ZMod.val_zero] at hval
  have hlt : 2 * k < 4 * k := by omega
  rw [Nat.mod_eq_of_lt hlt] at hval
  omega

/-- The half-turn has square one. -/
theorem r_two_mul_sq
    (k : ℕ) :
    DihedralGroup.r ((2 * k : ℕ) : ZMod (4 * k)) ^ 2 = 1 := by
  rw [pow_two, DihedralGroup.r_mul_r,
    halfTurn_add_halfTurn, DihedralGroup.r_zero]

/-- Every reflection has a central-involution commutator cycle. -/
theorem reflection_centralInvolutionCycle
    (k : ℕ) (i : ZMod (4 * k)) :
    let y := DihedralGroup.r ((k : ℕ) : ZMod (4 * k))
    let z := DihedralGroup.r ((2 * k : ℕ) : ZMod (4 * k))
    DihedralGroup.sr i * y = z * y * DihedralGroup.sr i := by
  dsimp only
  simp only [DihedralGroup.sr_mul_r,
    DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr]
  apply congrArg DihedralGroup.sr
  have hmod :
      ((4 * k : ℕ) : ZMod (4 * k)) = 0 := by simp
  have hmod' :
      (4 : ZMod (4 * k)) * (k : ZMod (4 * k)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmod
  norm_num [Nat.cast_mul]
  linear_combination hmod'

end DihedralGroup

/-! ## Transfer to a concrete linear copy -/

/-- An active involution in a fixed-point-free-center dihedral copy must
map to a reflection. -/
private theorem exists_eq_sr_of_active_dihedral
    {r d n : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (e : P ≃* DihedralGroup n)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    ∃ i : ZMod n, e x = DihedralGroup.sr i := by
  have hxOrder : orderOf x = 2 :=
    (mem_activePrimeOrderElements 2 P x).mp hx |>.1
  have hxActive : x ∈ nonzeroFixingElements P :=
    (mem_activePrimeOrderElements 2 P x).mp hx |>.2
  have hxNoncentral : x ∉ Subgroup.center P :=
    C.active_not_mem_center x hxActive
  have heOrder : orderOf (e x) = 2 := by
    rw [e.orderOf_eq, hxOrder]
  cases hex : e x with
  | r i =>
      exfalso
      apply hxNoncentral
      have hcenter :
          e x ∈ Subgroup.center (DihedralGroup n) := by
        rw [hex]
        exact
          DihedralGroup.r_mem_center_of_orderOf_eq_two i
            (by simpa [hex] using heOrder)
      exact (MulEquivClass.apply_mem_center_iff e).mp hcenter
  | sr i =>
      exact ⟨i, rfl⟩

/-- A fixed-point-free-center dihedral copy has at most `n` active
involutions. -/
theorem card_activePrimeOrderElements_two_le_of_dihedral
    {r d n : ℕ} [Fact r.Prime]
    (hn : 0 < n)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (e : P ≃* DihedralGroup n)
    (C : CenterFixedPointFreeAction r d P) :
    (activePrimeOrderElements 2 P).card ≤ n := by
  classical
  letI : NeZero n := ⟨hn.ne'⟩
  let A := {x : P // x ∈ activePrimeOrderElements 2 P}
  let index : A → ZMod n := fun x ↦
    Classical.choose
      (exists_eq_sr_of_active_dihedral P e C x.1 x.2)
  have hindex (x : A) :
      e x.1 = DihedralGroup.sr (index x) :=
    Classical.choose_spec
      (exists_eq_sr_of_active_dihedral P e C x.1 x.2)
  have hinjective : Function.Injective index := by
    intro x y hxy
    apply Subtype.ext
    apply e.injective
    rw [hindex x, hindex y, hxy]
  have hcard := Fintype.card_le_of_injective index hinjective
  calc
    (activePrimeOrderElements 2 P).card =
        Fintype.card A :=
      (Fintype.card_coe (activePrimeOrderElements 2 P)).symm
    _ ≤ Fintype.card (ZMod n) := hcard
    _ = n := ZMod.card n

/-- Every active involution in a linear copy of
`DihedralGroup (4*k)` has a half-dimensional fixed space. -/
theorem activeInvolution_fixedVectorSet_sq_le_of_dihedral
    {r d k : ℕ} [Fact r.Prime]
    (hdeven : Even d) (hk : 0 < k)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (e : P ≃* DihedralGroup (4 * k))
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    (fixedVectorSet x.1).ncard *
        (fixedVectorSet x.1).ncard ≤
      r ^ d := by
  obtain ⟨i, hi⟩ :=
    exists_eq_sr_of_active_dihedral P e C x hx
  let y : P :=
    e.symm (DihedralGroup.r ((k : ℕ) : ZMod (4 * k)))
  let zP : P :=
    e.symm (DihedralGroup.r ((2 * k : ℕ) : ZMod (4 * k)))
  have hzCenter : zP ∈ Subgroup.center P := by
    exact (MulEquivClass.apply_mem_center_iff e).mp
      (by simpa [zP] using DihedralGroup.r_two_mul_mem_center k)
  let z : Subgroup.center P := ⟨zP, hzCenter⟩
  have hzNe : z ≠ 1 := by
    intro hz
    have hzP : zP = 1 := congrArg Subtype.val hz
    have hmap := congrArg e hzP
    exact DihedralGroup.r_two_mul_ne_one k hk (by
      simpa [zP] using hmap)
  have hzSq : z ^ 2 = 1 := by
    apply Subtype.ext
    apply e.injective
    simpa [z, zP] using DihedralGroup.r_two_mul_sq k
  have hxy : x * y = z.1 * y * x := by
    apply e.injective
    simpa [y, z, zP, hi] using
      DihedralGroup.reflection_centralInvolutionCycle k i
  exact
    fixedVectorSet_sq_le_of_symplecticType_centralInvolutionCycle
      hdeven P C x y z hzNe hzSq hxy

end LisiSabatini
