import LisiSabatini.CyclicCenterClassTwo
import LisiSabatini.AlternatingDimension
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.TransferInstance
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# The symplectic quotient of an unsplit cyclic-center core

An odd class-two `p`-group with cyclic center and derived subgroup equal to
the canonical central subgroup of order `p` has the same symplectic central
quotient as an extraspecial group.  The center itself may be larger.

This file linearizes the kernel-valued pairing from
`CyclicCenterClassTwo`.  It proves

`|P / Z(P)| = p^(2*n)`

for a positive `n`, without choosing or assuming an extraspecial factor.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LisiSabatini

namespace IsOddCyclicCenterClassTwo

variable {p : ℕ} {P : Type*} [Group P] [Finite P]

local instance centerPrimeKernel_isMulCommutative_for_symplectic :
    IsMulCommutative (centerPrimeKernel p P) :=
  centerPrimeKernel_isMulCommutative p P

/-- Additive wrapper for the central quotient, indexed by the structural
certificate that supplies its canonical `ZMod p` module. -/
@[ext]
structure CentralQuotientVector
    (h : IsOddCyclicCenterClassTwo p P) where
  val : Additive (P ⧸ Subgroup.center P)

def centralQuotientVectorEquiv
    (h : IsOddCyclicCenterClassTwo p P) :
    h.CentralQuotientVector ≃ Additive (P ⧸ Subgroup.center P) where
  toFun := CentralQuotientVector.val
  invFun := CentralQuotientVector.mk
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

instance centralQuotientVectorAddCommGroup
    (h : IsOddCyclicCenterClassTwo p P) :
    AddCommGroup h.CentralQuotientVector := by
  letI : CommGroup (P ⧸ Subgroup.center P) :=
    { (inferInstance : Group (P ⧸ Subgroup.center P)) with
      mul_comm := h.quotient_center_commutative.comm }
  exact h.centralQuotientVectorEquiv.addCommGroup

@[simp]
theorem centralQuotientVector_val_zero
    (h : IsOddCyclicCenterClassTwo p P) :
    (0 : h.CentralQuotientVector).val = 0 :=
  rfl

@[simp]
theorem centralQuotientVector_val_add
    (h : IsOddCyclicCenterClassTwo p P)
    (x y : h.CentralQuotientVector) :
    (x + y).val = x.val + y.val :=
  rfl

def centralQuotientVectorAddEquiv
    (h : IsOddCyclicCenterClassTwo p P) :
    h.CentralQuotientVector ≃+ Additive (P ⧸ Subgroup.center P) :=
  { h.centralQuotientVectorEquiv with
    map_add' := fun _ _ ↦ rfl }

instance centralQuotientVectorModule
    (h : IsOddCyclicCenterClassTwo p P) :
    Module (ZMod p) h.CentralQuotientVector := by
  letI : CommGroup (P ⧸ Subgroup.center P) :=
    { (inferInstance : Group (P ⧸ Subgroup.center P)) with
      mul_comm := h.quotient_center_commutative.comm }
  letI : Module (ZMod p) (Additive (P ⧸ Subgroup.center P)) := by
    apply AddCommGroup.zmodModule
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul]
    exact h.quotient_center_pow_prime_eq_one x.toMul
  exact h.centralQuotientVectorAddEquiv.module (ZMod p)

instance centralQuotientVectorFinite
    (h : IsOddCyclicCenterClassTwo p P) :
    Finite h.CentralQuotientVector := by
  exact Finite.of_equiv (Additive (P ⧸ Subgroup.center P))
    h.centralQuotientVectorEquiv.symm

/-- The canonical central kernel, written additively, is `ZMod p`. -/
def centerPrimeKernelAddEquivZMod
    (h : IsOddCyclicCenterClassTwo p P) :
    Additive (centerPrimeKernel p P) ≃+ ZMod p := by
  exact (zmodAddCyclicAddEquiv
    (isAddCyclic_additive_iff.mpr h.centerPrimeKernel_isCyclic)).symm
      |>.trans
        (ZMod.ringEquivCongr h.card_centerPrimeKernel).toAddEquiv

/-- Scalar value of the quotient commutator pairing. -/
def commutatorPairingValue
    (h : IsOddCyclicCenterClassTwo p P)
    (x y : h.CentralQuotientVector) : ZMod p :=
  h.centerPrimeKernelAddEquivZMod (Additive.ofMul
    (h.centralQuotientKernelPairing x.val.toMul y.val.toMul))

@[simp]
theorem commutatorPairingValue_zero_left
    (h : IsOddCyclicCenterClassTwo p P)
    (y : h.CentralQuotientVector) :
    h.commutatorPairingValue 0 y = 0 := by
  simp [commutatorPairingValue]

@[simp]
theorem commutatorPairingValue_zero_right
    (h : IsOddCyclicCenterClassTwo p P)
    (x : h.CentralQuotientVector) :
    h.commutatorPairingValue x 0 = 0 := by
  simp [commutatorPairingValue]

theorem commutatorPairingValue_add_left
    (h : IsOddCyclicCenterClassTwo p P)
    (x₁ x₂ y : h.CentralQuotientVector) :
    h.commutatorPairingValue (x₁ + x₂) y =
      h.commutatorPairingValue x₁ y +
        h.commutatorPairingValue x₂ y := by
  simp only [commutatorPairingValue, centralQuotientVector_val_add,
    toMul_add, map_mul, MonoidHom.mul_apply, ofMul_mul, map_add]

theorem commutatorPairingValue_add_right
    (h : IsOddCyclicCenterClassTwo p P)
    (x y₁ y₂ : h.CentralQuotientVector) :
    h.commutatorPairingValue x (y₁ + y₂) =
      h.commutatorPairingValue x y₁ +
        h.commutatorPairingValue x y₂ := by
  simp [commutatorPairingValue]

def commutatorPairingRightAddHom
    (h : IsOddCyclicCenterClassTwo p P)
    (x : h.CentralQuotientVector) :
    h.CentralQuotientVector →+ ZMod p where
  toFun := h.commutatorPairingValue x
  map_zero' := h.commutatorPairingValue_zero_right x
  map_add' := h.commutatorPairingValue_add_right x

def commutatorPairingRightLinear
    (h : IsOddCyclicCenterClassTwo p P)
    (x : h.CentralQuotientVector) :
    h.CentralQuotientVector →ₗ[ZMod p] ZMod p :=
  (h.commutatorPairingRightAddHom x).toZModLinearMap p

def commutatorPairingOuterAddHom
    (h : IsOddCyclicCenterClassTwo p P) :
    h.CentralQuotientVector →+
      (h.CentralQuotientVector →ₗ[ZMod p] ZMod p) where
  toFun := h.commutatorPairingRightLinear
  map_zero' := by
    ext y
    exact h.commutatorPairingValue_zero_left y
  map_add' := by
    intro x₁ x₂
    ext y
    exact h.commutatorPairingValue_add_left x₁ x₂ y

/-- The commutator pairing as a bilinear form over `ZMod p`. -/
def commutatorBilin
    (h : IsOddCyclicCenterClassTwo p P) :
    LinearMap.BilinForm (ZMod p) h.CentralQuotientVector :=
  h.commutatorPairingOuterAddHom.toZModLinearMap p

@[simp]
theorem commutatorBilin_apply
    (h : IsOddCyclicCenterClassTwo p P)
    (x y : h.CentralQuotientVector) :
    h.commutatorBilin x y = h.commutatorPairingValue x y :=
  rfl

theorem commutatorPairingValue_eq_zero_iff
    (h : IsOddCyclicCenterClassTwo p P)
    (x y : h.CentralQuotientVector) :
    h.commutatorPairingValue x y = 0 ↔
      h.centralQuotientKernelPairing x.val.toMul y.val.toMul = 1 := by
  constructor
  · intro hzero
    have hadd : Additive.ofMul
        (h.centralQuotientKernelPairing x.val.toMul y.val.toMul) = 0 := by
      apply h.centerPrimeKernelAddEquivZMod.injective
      simpa [commutatorPairingValue] using hzero
    exact ofMul_eq_zero.mp hadd
  · intro hone
    simp [commutatorPairingValue, hone]

theorem commutatorBilin_isAlt
    (h : IsOddCyclicCenterClassTwo p P) :
    h.commutatorBilin.IsAlt := by
  intro x
  rw [commutatorBilin_apply,
    h.commutatorPairingValue_eq_zero_iff]
  exact h.centralQuotientKernelPairing_alternating x.val.toMul

theorem commutatorBilin_separatingLeft
    (h : IsOddCyclicCenterClassTwo p P) :
    h.commutatorBilin.SeparatingLeft := by
  intro x hx
  have hchar : h.centralQuotientKernelPairing x.val.toMul = 1 := by
    apply MonoidHom.ext
    intro q
    let y : h.CentralQuotientVector :=
      ⟨Additive.ofMul q⟩
    have hy := (h.commutatorPairingValue_eq_zero_iff x y).mp (hx y)
    exact hy
  have hxone : x.val.toMul = 1 :=
    h.centralQuotientKernelPairing_injective
      (hchar.trans
        (map_one h.centralQuotientKernelPairing).symm)
  apply CentralQuotientVector.ext
  apply Additive.toMul.injective
  simpa using hxone

theorem commutatorBilin_nondegenerate
    (h : IsOddCyclicCenterClassTwo p P) :
    h.commutatorBilin.Nondegenerate := by
  refine ⟨h.commutatorBilin_separatingLeft, ?_⟩
  intro y hy
  apply h.commutatorBilin_separatingLeft y
  intro x
  have hneg := h.commutatorBilin_isAlt.neg_eq y x
  rw [hy x] at hneg
  exact neg_eq_zero.mp hneg

/-- The central quotient has even vector-space dimension. -/
theorem even_finrank_centralQuotient
    (h : IsOddCyclicCenterClassTwo p P)
    [Fact p.Prime] :
    Even (Module.finrank (ZMod p) h.CentralQuotientVector) := by
  have hpTwo : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h.odd) even_two
  exact even_finrank_of_nondegenerate_alternating
    (k := ZMod p) (V := h.CentralQuotientVector)
    (two_ne_zero_zmod_of_prime_ne_two h.prime hpTwo)
    (B := h.commutatorBilin) h.commutatorBilin_isAlt
    h.commutatorBilin_nondegenerate

/-- The unsplit cyclic-center core has a square-order central quotient. -/
theorem exists_card_quotient_center_eq_prime_pow_two_mul
    (h : IsOddCyclicCenterClassTwo p P) :
    ∃ n : ℕ, Nat.card (P ⧸ Subgroup.center P) = p ^ (2 * n) := by
  letI : Fact p.Prime := ⟨h.prime⟩
  have hpTwo : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr h.odd) even_two
  obtain ⟨n, hn⟩ :=
    exists_natCard_eq_pow_two_mul_of_nondegenerate_alternating
      (k := ZMod p) (V := h.CentralQuotientVector)
      (two_ne_zero_zmod_of_prime_ne_two h.prime hpTwo)
      (B := h.commutatorBilin)
      h.commutatorBilin_isAlt h.commutatorBilin_nondegenerate
  refine ⟨n, ?_⟩
  calc
    Nat.card (P ⧸ Subgroup.center P) =
        Nat.card h.CentralQuotientVector :=
      Nat.card_congr h.centralQuotientVectorEquiv.symm
    _ = Nat.card (ZMod p) ^ (2 * n) := hn
    _ = p ^ (2 * n) := by rw [Nat.card_zmod]

/-- Noncommutativity makes the symplectic rank positive. -/
theorem exists_pos_card_quotient_center_eq_prime_pow_two_mul
    (h : IsOddCyclicCenterClassTwo p P) :
    ∃ n : ℕ, 0 < n ∧
      Nat.card (P ⧸ Subgroup.center P) = p ^ (2 * n) := by
  obtain ⟨n, hn⟩ := h.exists_card_quotient_center_eq_prime_pow_two_mul
  refine ⟨n, ?_, hn⟩
  apply Nat.pos_of_ne_zero
  intro hnzero
  subst n
  have hcardQ : Nat.card (P ⧸ Subgroup.center P) = 1 := by
    simpa using hn
  have hindex : (Subgroup.center P).index = 1 := by
    rw [(Subgroup.center P).index_eq_card]
    exact hcardQ
  have hcenterTop : Subgroup.center P = ⊤ :=
    Subgroup.index_eq_one.mp hindex
  apply h.noncommutative
  refine ⟨⟨fun x y ↦ ?_⟩⟩
  have hx : x ∈ Subgroup.center P := by
    rw [hcenterTop]
    exact Subgroup.mem_top x
  exact (Subgroup.mem_center_iff.mp hx y).symm

/-! ## A canonical unsplit structural rank -/

/-- A chosen positive symplectic rank for the central quotient. -/
noncomputable def cyclicCenterStructuralRank
    (h : IsOddCyclicCenterClassTwo p P) : ℕ :=
  Classical.choose
    h.exists_pos_card_quotient_center_eq_prime_pow_two_mul

/-- The chosen unsplit structural rank is positive. -/
theorem cyclicCenterStructuralRank_pos
    (h : IsOddCyclicCenterClassTwo p P) :
    0 < h.cyclicCenterStructuralRank :=
  (Classical.choose_spec
    h.exists_pos_card_quotient_center_eq_prime_pow_two_mul).1

/-- The chosen rank gives the exact number of central cosets. -/
theorem cyclicCenterStructuralRank_card_quotient_center
    (h : IsOddCyclicCenterClassTwo p P) :
    Nat.card (P ⧸ Subgroup.center P) =
      p ^ (2 * h.cyclicCenterStructuralRank) :=
  (Classical.choose_spec
    h.exists_pos_card_quotient_center_eq_prime_pow_two_mul).2

end IsOddCyclicCenterClassTwo

end LisiSabatini
