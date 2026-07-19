import LisiSabatini.HallClassTwoCore

/-!
# Odd class-two cores with cyclic center

Hall's theorem is usually stated by splitting a nonabelian odd `p`-group as
a central product of an extraspecial group and a cyclic group.  For the
linear fixed-space argument, the split subgroup is not essential.  The
larger group already has the correct symplectic quotient as soon as

* its center is cyclic;
* its derived subgroup is the prime-order kernel in that center; and
* the group has class at most two.

This file packages exactly those hypotheses.  It proves that the central
quotient is elementary abelian and constructs its intrinsic nondegenerate
commutator pairing, with values in the canonical order-`p` central kernel.
The subsequent linearization can therefore work with a cyclic central
factor directly, without first choosing a central-product complement.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

/-- The intrinsic class-two structure needed from Hall's theorem, without a
choice of extraspecial central-product factor. -/
structure IsOddCyclicCenterClassTwo
    (p : ℕ) (P : Type*) [Group P] [Finite P] : Prop where
  prime : p.Prime
  odd : Odd p
  pGroup : IsPGroup p P
  noncommutative : ¬ IsMulCommutative P
  commutator_le_center : commutator P ≤ Subgroup.center P
  center_isCyclic : IsCyclic (Subgroup.center P)
  commutator_eq_centerPrimeKernel :
    commutator P = centerPrimeKernel p P

namespace IsOddCyclicCenterClassTwo

variable {p : ℕ} {P : Type*} [Group P] [Finite P]

local instance centerPrimeKernel_isMulCommutative_instance :
    IsMulCommutative (centerPrimeKernel p P) :=
  centerPrimeKernel_isMulCommutative p P

/-- Noncommutativity supplies nontriviality. -/
theorem nontrivial (h : IsOddCyclicCenterClassTwo p P) : Nontrivial P := by
  apply not_subsingleton_iff_nontrivial.mp
  intro hsub
  apply h.noncommutative
  exact ⟨⟨fun x y ↦ hsub.elim (x * y) (y * x)⟩⟩

/-- The canonical derived kernel has order `p`. -/
theorem card_centerPrimeKernel (h : IsOddCyclicCenterClassTwo p P) :
    Nat.card (centerPrimeKernel p P) = p := by
  letI : Nontrivial P := h.nontrivial
  exact card_centerPrimeKernel_of_center_isCyclic
    h.prime h.pGroup h.center_isCyclic

/-- The derived subgroup has order `p`. -/
theorem card_commutator (h : IsOddCyclicCenterClassTwo p P) :
    Nat.card (commutator P) = p := by
  rw [h.commutator_eq_centerPrimeKernel]
  exact h.card_centerPrimeKernel

/-- The canonical derived kernel is cyclic. -/
theorem centerPrimeKernel_isCyclic
    (h : IsOddCyclicCenterClassTwo p P) :
    IsCyclic (centerPrimeKernel p P) := by
  letI : IsCyclic (Subgroup.center P) := h.center_isCyclic
  exact Subgroup.isCyclic_of_le (centerPrimeKernel_le_center p P)

/-- The central quotient is abelian. -/
theorem quotient_center_commutative
    (h : IsOddCyclicCenterClassTwo p P) :
    Std.Commutative
      (· * · : (P ⧸ Subgroup.center P) → _ → _) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  exact h.commutator_le_center

/-- Every derived element has `p`-th power one. -/
theorem commutator_pow_prime_eq_one
    (h : IsOddCyclicCenterClassTwo p P)
    (c : commutator P) : (c : P) ^ p = 1 := by
  have hc : (c : P) ∈ centerPrimeKernel p P := by
    rw [← h.commutator_eq_centerPrimeKernel]
    exact c.2
  rw [centerPrimeKernel] at hc
  obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.mp hc
  have hzpow : z ^ p = 1 := MonoidHom.mem_ker.mp hz
  rw [← hzc]
  exact congrArg Subtype.val hzpow

/-- Every `p`-th power is central. -/
theorem pow_prime_mem_center
    (h : IsOddCyclicCenterClassTwo p P) (x : P) :
    x ^ p ∈ Subgroup.center P := by
  exact pow_mem_center_of_commutator_le_center
    h.commutator_le_center p h.commutator_pow_prime_eq_one x

/-- The central quotient has exponent dividing `p`. -/
theorem quotient_center_pow_prime_eq_one
    (h : IsOddCyclicCenterClassTwo p P) :
    ∀ x : P ⧸ Subgroup.center P, x ^ p = 1 := by
  intro x
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.center P) x
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact h.pow_prime_mem_center x

/-- The central quotient remains a `p`-group. -/
theorem quotient_center_isPGroup
    (h : IsOddCyclicCenterClassTwo p P) :
    IsPGroup p (P ⧸ Subgroup.center P) :=
  h.pGroup.to_quotient (Subgroup.center P)

/-- Its cardinality is a power of `p`. -/
theorem exists_card_quotient_center_eq_prime_pow
    (h : IsOddCyclicCenterClassTwo p P) :
    ∃ m : ℕ, Nat.card (P ⧸ Subgroup.center P) = p ^ m := by
  letI : Fact p.Prime := ⟨h.prime⟩
  exact IsPGroup.iff_card.mp h.quotient_center_isPGroup

/-! ## The kernel-valued commutator pairing -/

/-- A commutator, regarded as an element of the canonical order-`p`
central kernel. -/
def kernelCommutator (h : IsOddCyclicCenterClassTwo p P) (x y : P) :
    centerPrimeKernel p P :=
  ⟨⁅x, y⁆, by
    rw [← h.commutator_eq_centerPrimeKernel]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

@[simp]
theorem coe_kernelCommutator
    (h : IsOddCyclicCenterClassTwo p P) (x y : P) :
    (h.kernelCommutator x y : P) = ⁅x, y⁆ :=
  rfl

@[simp]
theorem kernelCommutator_one_left
    (h : IsOddCyclicCenterClassTwo p P) (y : P) :
    h.kernelCommutator 1 y = 1 := by
  apply Subtype.ext
  simp

@[simp]
theorem kernelCommutator_one_right
    (h : IsOddCyclicCenterClassTwo p P) (x : P) :
    h.kernelCommutator x 1 = 1 := by
  apply Subtype.ext
  simp

@[simp]
theorem kernelCommutator_self
    (h : IsOddCyclicCenterClassTwo p P) (x : P) :
    h.kernelCommutator x x = 1 := by
  apply Subtype.ext
  simp

theorem kernelCommutator_mul_left
    (h : IsOddCyclicCenterClassTwo p P) (x₁ x₂ y : P) :
    h.kernelCommutator (x₁ * x₂) y =
      h.kernelCommutator x₂ y * h.kernelCommutator x₁ y := by
  apply Subtype.ext
  exact commutatorElement_mul_left_of_mem_center x₁ x₂ y
    (h.commutator_le_center
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x₂) (Subgroup.mem_top y)))

theorem kernelCommutator_mul_right
    (h : IsOddCyclicCenterClassTwo p P) (x y₁ y₂ : P) :
    h.kernelCommutator x (y₁ * y₂) =
      h.kernelCommutator x y₁ * h.kernelCommutator x y₂ := by
  apply Subtype.ext
  exact commutatorElement_mul_right_of_mem_center x y₁ y₂
    (h.commutator_le_center
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y₂)))

/-- The right commutator character. -/
def kernelCommutatorRightHom
    (h : IsOddCyclicCenterClassTwo p P) (x : P) :
    P →* centerPrimeKernel p P where
  toFun := h.kernelCommutator x
  map_one' := h.kernelCommutator_one_right x
  map_mul' := h.kernelCommutator_mul_right x

@[simp]
theorem kernelCommutatorRightHom_apply
    (h : IsOddCyclicCenterClassTwo p P) (x y : P) :
    h.kernelCommutatorRightHom x y = h.kernelCommutator x y :=
  rfl

/-- The left radical of the pairing is exactly the full center. -/
theorem kernelCommutator_left_radical
    (h : IsOddCyclicCenterClassTwo p P) (x : P) :
    (∀ y : P, h.kernelCommutator x y = 1) ↔
      x ∈ Subgroup.center P := by
  constructor
  · intro hx
    rw [Subgroup.mem_center_iff]
    intro y
    rw [eq_comm, ← commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hx y)
  · intro hx y
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hx y).symm

/-- The right radical is exactly the full center. -/
theorem kernelCommutator_right_radical
    (h : IsOddCyclicCenterClassTwo p P) (y : P) :
    (∀ x : P, h.kernelCommutator x y = 1) ↔
      y ∈ Subgroup.center P := by
  constructor
  · intro hy
    rw [Subgroup.mem_center_iff]
    intro x
    rw [← commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (hy x)
  · intro hy x
    apply Subtype.ext
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subgroup.mem_center_iff.mp hy x)

theorem center_le_ker_kernelCommutatorRightHom
    (h : IsOddCyclicCenterClassTwo p P) (x : P) :
    Subgroup.center P ≤ (h.kernelCommutatorRightHom x).ker := by
  intro y hy
  exact MonoidHom.mem_ker.mpr
    ((h.kernelCommutator_right_radical y).mpr hy x)

/-- Descend the right character through the central quotient. -/
def quotientKernelCommutatorRightHom
    (h : IsOddCyclicCenterClassTwo p P) (x : P) :
    (P ⧸ Subgroup.center P) →* centerPrimeKernel p P :=
  QuotientGroup.lift (Subgroup.center P)
    (h.kernelCommutatorRightHom x)
    (h.center_le_ker_kernelCommutatorRightHom x)

@[simp]
theorem quotientKernelCommutatorRightHom_mk
    (h : IsOddCyclicCenterClassTwo p P) (x y : P) :
    h.quotientKernelCommutatorRightHom x
        (QuotientGroup.mk' (Subgroup.center P) y) =
      h.kernelCommutator x y :=
  rfl

/-- The quotient characters form a homomorphism before descending the first
variable. -/
def quotientKernelCommutatorOuterHom
    (h : IsOddCyclicCenterClassTwo p P) :
    P →* ((P ⧸ Subgroup.center P) →* centerPrimeKernel p P) where
  toFun := h.quotientKernelCommutatorRightHom
  map_one' := by
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | _ y => simp [quotientKernelCommutatorRightHom]
  map_mul' := by
    intro x₁ x₂
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | _ y =>
        change h.kernelCommutator (x₁ * x₂) y =
          h.kernelCommutator x₁ y * h.kernelCommutator x₂ y
        rw [h.kernelCommutator_mul_left]
        exact mul_comm _ _

@[simp]
theorem quotientKernelCommutatorOuterHom_apply_mk
    (h : IsOddCyclicCenterClassTwo p P) (x y : P) :
    h.quotientKernelCommutatorOuterHom x
        (QuotientGroup.mk' (Subgroup.center P) y) =
      h.kernelCommutator x y :=
  rfl

theorem center_le_ker_quotientKernelCommutatorOuterHom
    (h : IsOddCyclicCenterClassTwo p P) :
    Subgroup.center P ≤ h.quotientKernelCommutatorOuterHom.ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | _ y =>
      change h.kernelCommutator x y = 1
      exact (h.kernelCommutator_left_radical x).mpr hx y

/-- The nondegenerate commutator pairing on `P / Z(P)`, valued in the
canonical order-`p` central kernel. -/
def centralQuotientKernelPairing
    (h : IsOddCyclicCenterClassTwo p P) :
    (P ⧸ Subgroup.center P) →*
      ((P ⧸ Subgroup.center P) →* centerPrimeKernel p P) :=
  QuotientGroup.lift (Subgroup.center P)
    h.quotientKernelCommutatorOuterHom
    h.center_le_ker_quotientKernelCommutatorOuterHom

@[simp]
theorem centralQuotientKernelPairing_mk_mk
    (h : IsOddCyclicCenterClassTwo p P) (x y : P) :
    h.centralQuotientKernelPairing
        (QuotientGroup.mk' (Subgroup.center P) x)
        (QuotientGroup.mk' (Subgroup.center P) y) =
      h.kernelCommutator x y :=
  rfl

theorem centralQuotientKernelPairing_alternating
    (h : IsOddCyclicCenterClassTwo p P) :
    ∀ x : P ⧸ Subgroup.center P,
      h.centralQuotientKernelPairing x x = 1 := by
  intro x
  induction x using QuotientGroup.induction_on with
  | _ x => exact h.kernelCommutator_self x

/-- Nondegeneracy of the quotient pairing. -/
theorem centralQuotientKernelPairing_injective
    (h : IsOddCyclicCenterClassTwo p P) :
    Function.Injective h.centralQuotientKernelPairing := by
  apply (MonoidHom.ker_eq_bot_iff h.centralQuotientKernelPairing).mp
  ext q
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hq
    induction q using QuotientGroup.induction_on with
    | _ x =>
        rw [QuotientGroup.eq_one_iff]
        apply (h.kernelCommutator_left_radical x).mp
        intro y
        have heval := DFunLike.congr_fun hq
          (QuotientGroup.mk' (Subgroup.center P) y)
        simpa using heval
  · rintro rfl
    exact map_one _

end IsOddCyclicCenterClassTwo

namespace IsHallClassTwoIntermediate

variable {p : ℕ} {P : Type*} [Group P] [Finite P]

/-- A Hall intermediate with central Frattini subgroup already has the
unsplit cyclic-center symplectic structure. -/
def toOddCyclicCenterClassTwo
    (h : IsHallClassTwoIntermediate p P)
    (hPhi : frattini P ≤ Subgroup.center P) :
    IsOddCyclicCenterClassTwo p P where
  prime := h.prime
  odd := h.odd
  pGroup := h.pGroup
  noncommutative := h.noncommutative
  commutator_le_center := h.commutator_le_center
  center_isCyclic := h.center_isCyclic
  commutator_eq_centerPrimeKernel :=
    h.commutator_eq_centerPrimeKernel_of_frattini_le_center hPhi

end IsHallClassTwoIntermediate

end LisiSabatini
