import LisiSabatini.TwoCoreAffineTwoBaseHalfDensity
import LisiSabatini.CyclicCenterOperatorFixedSpaceRowCore
import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Classification-free structure for symplectic-type two-cores

This file develops the group-theoretic consequences that are available
before invoking Hall--Berger classification.

The fixed-space cycle needs only a central commutator subgroup of order
two.  Every noncentral element then has a commutator partner whose
commutator is the unique nontrivial central involution.  For a linear
action with fixed-point-free center, this gives the half-dimensional
fixed-space estimate for every active involution.

We also treat the generalized-quaternion branch using mathlib's explicit
`QuaternionGroup`: every involution is central, hence a fixed-point-free
center leaves no active involutions at all.
-/

noncomputable section

namespace LisiSabatini

open scoped commutatorElement

set_option backward.isDefEq.respectTransparency false

/-- The exact class-two fragment needed for the involution fixed-space
cycle.  It is weaker than choosing an extraspecial factor or a central
product decomposition. -/
structure HasCentralCommutatorOfOrderTwo
    (P : Type*) [Group P] [Finite P] : Prop where
  commutator_le_center :
    commutator P ≤ Subgroup.center P
  card_commutator :
    Nat.card (commutator P) = 2

namespace HasCentralCommutatorOfOrderTwo

variable {P : Type*} [Group P] [Finite P]

/-- Every noncentral element has a commutator partner for which the
commutator is a nontrivial central involution. -/
theorem exists_central_involution_cycle
    (h : HasCentralCommutatorOfOrderTwo P)
    (x : P) (hx : x ∉ Subgroup.center P) :
    ∃ (y : P) (z : Subgroup.center P),
      z ≠ 1 ∧ z ^ 2 = 1 ∧
        x * y = z.1 * y * x := by
  have hnotAll : ¬ ∀ y : P, y * x = x * y := by
    intro hall
    exact hx ((Subgroup.mem_center_iff).2 hall)
  push Not at hnotAll
  obtain ⟨y, hy⟩ := hnotAll
  have hcommNe :
      ⁅x, y⁆ ≠ 1 := by
    intro hone
    have hxy :
        x * y = y * x :=
      commutatorElement_eq_one_iff_mul_comm.mp hone
    exact hy hxy.symm
  have hcommMem :
      ⁅x, y⁆ ∈ commutator P :=
    Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)
  let c : commutator P := ⟨⁅x, y⁆, hcommMem⟩
  let z : Subgroup.center P :=
    ⟨⁅x, y⁆, h.commutator_le_center hcommMem⟩
  have hzNe : z ≠ 1 := by
    intro hz
    exact hcommNe (congrArg Subtype.val hz)
  have hcSq : c ^ 2 = 1 := by
    have hpow :
        c ^ Nat.card (commutator P) = 1 :=
      pow_card_eq_one'
    simpa [h.card_commutator] using hpow
  have hzSq : z ^ 2 = 1 := by
    apply Subtype.ext
    change ⁅x, y⁆ ^ 2 = 1
    simpa only [c, Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg Subtype.val hcSq
  refine ⟨y, z, hzNe, hzSq, ?_⟩
  dsimp only [z]
  simp only [commutatorElement_def]
  group

end HasCentralCommutatorOfOrderTwo

/-- An extraspecial `2`-group has central commutator subgroup of order
two. -/
theorem IsExtraspecial.hasCentralCommutatorOfOrderTwo
    {P : Type*} [Group P] [Finite P]
    (h : IsExtraspecial 2 P) :
    HasCentralCommutatorOfOrderTwo P where
  commutator_le_center := by rw [h.commutator_eq_center]
  card_commutator := by
    rw [h.commutator_eq_center]
    exact h.card_center

/-- Linear-algebra realization of a supplied central involution cycle.
This is the symplectic-type specialization of the operator-valued cycle
theorem. -/
theorem fixedVectorSet_sq_le_of_symplecticType_centralInvolutionCycle
    {r d : ℕ} [Fact r.Prime]
    (hdeven : Even d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (C : CenterFixedPointFreeAction r d P)
    (x y : P) (z : Subgroup.center P)
    (hzNe : z ≠ 1) (hzSq : z ^ 2 = 1)
    (hxy : x * y = z.1 * y * x) :
    (fixedVectorSet x.1).ncard *
        (fixedVectorSet x.1).ncard ≤
      r ^ d := by
  have hxyGL :
      x.1 * y.1 = z.1.1 * y.1 * x.1 :=
    congrArg Subtype.val hxy
  have hxzGL : Commute x.1 z.1.1 := by
    have hxzP : x * z.1 = z.1 * x :=
      Subgroup.mem_center_iff.mp z.2 x
    exact congrArg Subtype.val hxzP
  have hzyGL : Commute z.1.1 y.1 := by
    have hyzP : y * z.1 = z.1 * y :=
      Subgroup.mem_center_iff.mp z.2 y
    exact (congrArg Subtype.val hyzP).symm
  have hzSqGL : z.1.1 ^ 2 = 1 := by
    simpa using congrArg (fun w : Subgroup.center P ↦ w.1.1) hzSq
  have hnonzero :
      (nonzeroFixedVectorSet x.1).ncard ≤
        r ^ (d / 2) - 1 := by
    apply
      ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_GL_fixedPointFree_cycle
        (by norm_num : 0 < 2) x.1 y.1 z.1.1
        hxyGL hxzGL hzyGL hzSqGL
    intro k hkPos hkLt v hv
    have hk : k = 1 := by omega
    subst k
    simpa only [pow_one] using C.fixedPointFree z hzNe v hv
  have hfixed :
      (fixedVectorSet x.1).ncard ≤ r ^ (d / 2) := by
    rw [ncard_nonzeroFixedVectorSet] at hnonzero
    have hcardPos : 0 < (fixedVectorSet x.1).ncard := by
      rw [Set.ncard_pos]
      exact ⟨0, by simp [fixedVectorSet]⟩
    have hpowPos : 0 < r ^ (d / 2) :=
      pow_pos (Fact.out : Nat.Prime r).pos _
    omega
  have hsquare :
      r ^ (d / 2) * r ^ (d / 2) = r ^ d := by
    rw [← pow_add]
    congr 1
    have := Nat.two_mul_div_two_of_even hdeven
    omega
  calc
    (fixedVectorSet x.1).ncard *
          (fixedVectorSet x.1).ncard ≤
        r ^ (d / 2) * r ^ (d / 2) :=
      Nat.mul_le_mul hfixed hfixed
    _ = r ^ d := hsquare

/-- In a fixed-point-free-center representation, every active involution
in a group with central commutator of order two fixes at most a
half-dimensional subspace. -/
theorem activeInvolution_fixedVectorSet_sq_le_of_centralCommutator
    {r d : ℕ} [Fact r.Prime]
    (hdeven : Even d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : HasCentralCommutatorOfOrderTwo P)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    (fixedVectorSet x.1).ncard *
        (fixedVectorSet x.1).ncard ≤
      r ^ d := by
  have hxActive :
      x ∈ nonzeroFixingElements P :=
    (mem_activePrimeOrderElements 2 P x).mp hx |>.2
  have hxNoncentral :
      x ∉ Subgroup.center P :=
    C.active_not_mem_center x hxActive
  obtain ⟨y, z, hzNe, hzSq, hxy⟩ :=
    hP.exists_central_involution_cycle x hxNoncentral
  exact fixedVectorSet_sq_le_of_symplecticType_centralInvolutionCycle
    hdeven P C x y z hzNe hzSq hxy

/-- Specialization to an extraspecial mapped `2`-core. -/
theorem activeInvolution_fixedVectorSet_sq_le_of_extraspecial
    {r d : ℕ} [Fact r.Prime]
    (hdeven : Even d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsExtraspecial 2 P)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    (fixedVectorSet x.1).ncard *
        (fixedVectorSet x.1).ncard ≤
      r ^ d :=
  activeInvolution_fixedVectorSet_sq_le_of_centralCommutator
    hdeven P hP.hasCentralCommutatorOfOrderTwo C x hx

/-! ## The generalized-quaternion branch -/

/-- Every element of order two is central. -/
def AllInvolutionsCentral (P : Type*) [Group P] : Prop :=
  ∀ x : P, orderOf x = 2 → x ∈ Subgroup.center P

/-- The property that every involution is central is invariant under group
isomorphism. -/
theorem AllInvolutionsCentral.of_mulEquiv
    {P Q : Type*} [Group P] [Group Q]
    (hQ : AllInvolutionsCentral Q)
    (e : P ≃* Q) :
    AllInvolutionsCentral P := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply e.injective
  have horder : orderOf (e x) = 2 := by
    rw [e.orderOf_eq, hx]
  have hcenter := Subgroup.mem_center_iff.mp (hQ (e x) horder) (e y)
  simpa using hcenter

/-- In a generalized quaternion group, every involution is central.

The proof uses only mathlib's normal forms `a i` and `xa i`.  An `xa`
element has order four.  If `a i` has order two, then `2i = 0`, which is
exactly the relation needed for `a i` to commute with every `xa j`. -/
theorem quaternionGroup_allInvolutionsCentral
    (n : ℕ) [NeZero n] :
    AllInvolutionsCentral (QuaternionGroup n) := by
  intro x hx
  cases x with
  | a i =>
      have hiSq : QuaternionGroup.a i ^ 2 = 1 := by
        rw [← hx]
        exact pow_orderOf_eq_one (QuaternionGroup.a i)
      have hiTwo : i + i = 0 := by
        simpa [pow_two, QuaternionGroup.one_def] using
          QuaternionGroup.a.inj hiSq
      rw [Subgroup.mem_center_iff]
      intro y
      cases y with
      | a j =>
          simp only [QuaternionGroup.a_mul_a]
          exact congrArg QuaternionGroup.a (add_comm j i)
      | xa j =>
          simp only [QuaternionGroup.xa_mul_a,
            QuaternionGroup.a_mul_xa]
          apply congrArg QuaternionGroup.xa
          have hneg : -i = i := by
            exact (neg_eq_iff_add_eq_zero).2 hiTwo
          rw [sub_eq_add_neg, hneg]
  | xa i =>
      have hfour : orderOf (QuaternionGroup.xa i) = 4 :=
        QuaternionGroup.orderOf_xa i
      omega

/-- A fixed-point-free center eliminates every active involution when all
involutions are central. -/
theorem activePrimeOrderElements_two_eq_empty_of_allInvolutionsCentral
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hcentral : AllInvolutionsCentral P)
    (C : CenterFixedPointFreeAction r d P) :
    activePrimeOrderElements 2 P = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.2
  intro x hx
  obtain ⟨hxOrder, hxActive⟩ :=
    (mem_activePrimeOrderElements 2 P x).mp hx
  exact C.active_not_mem_center x hxActive
    (hcentral x hxOrder)

/-- The generalized-quaternion branch contributes no active
involutions. -/
theorem activePrimeOrderElements_two_eq_empty_of_quaternion
    {r d n : ℕ} [Fact r.Prime] [NeZero n]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (e : P ≃* QuaternionGroup n)
    (C : CenterFixedPointFreeAction r d P) :
    activePrimeOrderElements 2 P = ∅ := by
  apply
    activePrimeOrderElements_two_eq_empty_of_allInvolutionsCentral
      P _ C
  exact
    (quaternionGroup_allInvolutionsCentral n).of_mulEquiv e

end LisiSabatini
