module

public import LisiSabatini.CyclicCenterSymplectic
public import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# Central automorphisms of extraspecial two-groups

An automorphism of an extraspecial two-group which induces the identity on
the quotient by the center is inner.  The proof is intrinsic.  The
commutator gives a nondegenerate bilinear form on `E / Z(E)` over `ZMod 2`,
and the central error `α(x) * x⁻¹` is a linear functional on this quotient.
The linear equivalence `LinearMap.BilinForm.toDual` then supplies the
conjugating element.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

namespace IsExtraspecial

variable {E : Type*} [Group E] [Finite E]

/-! ## The commutator form -/

/-- Every element of the center of an extraspecial two-group has square one. -/
theorem center_sq_eq_one
    (h : IsExtraspecial 2 E) (z : Subgroup.center E) :
    z ^ 2 = 1 := by
  have hz : z ^ Nat.card (Subgroup.center E) = 1 :=
    pow_card_eq_one'
  simpa [h.card_center] using hz

/-- Every element of the derived subgroup has square one. -/
theorem commutator_sq_eq_one
    (h : IsExtraspecial 2 E) (c : commutator E) :
    (c : E) ^ 2 = 1 := by
  have hc : c ^ Nat.card (commutator E) = 1 :=
    pow_card_eq_one'
  have hcard : Nat.card (commutator E) = 2 := by
    rw [h.commutator_eq_center]
    exact h.card_center
  exact congrArg Subtype.val (by simpa [hcard] using hc)

/-- Squares are central in an extraspecial two-group. -/
theorem square_mem_center
    (h : IsExtraspecial 2 E) (x : E) :
    x ^ 2 ∈ Subgroup.center E := by
  apply pow_mem_center_of_commutator_le_center
    (by rw [h.commutator_eq_center]) 2
  exact h.commutator_sq_eq_one

/-- The central quotient has exponent two. -/
theorem quotient_center_sq_eq_one
    (h : IsExtraspecial 2 E) :
    ∀ q : E ⧸ Subgroup.center E, q ^ 2 = 1 := by
  intro q
  obtain ⟨x, rfl⟩ :=
    QuotientGroup.mk'_surjective (Subgroup.center E) q
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact h.square_mem_center x

/-- A commutator, regarded as an element of the center. -/
def centerCommutator
    (h : IsExtraspecial 2 E) (x y : E) :
    Subgroup.center E :=
  ⟨⁅x, y⁆, by
    rw [← h.commutator_eq_center]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)⟩

@[simp]
theorem coe_centerCommutator
    (h : IsExtraspecial 2 E) (x y : E) :
    (h.centerCommutator x y : E) = ⁅x, y⁆ :=
  rfl

@[simp]
theorem centerCommutator_one_left
    (h : IsExtraspecial 2 E) (y : E) :
    h.centerCommutator 1 y = 1 := by
  apply Subtype.ext
  simp

@[simp]
theorem centerCommutator_one_right
    (h : IsExtraspecial 2 E) (x : E) :
    h.centerCommutator x 1 = 1 := by
  apply Subtype.ext
  simp

@[simp]
theorem centerCommutator_self
    (h : IsExtraspecial 2 E) (x : E) :
    h.centerCommutator x x = 1 := by
  apply Subtype.ext
  simp

theorem centerCommutator_mul_left
    (h : IsExtraspecial 2 E) (x₁ x₂ y : E) :
    h.centerCommutator (x₁ * x₂) y =
      h.centerCommutator x₂ y * h.centerCommutator x₁ y := by
  apply Subtype.ext
  exact commutatorElement_mul_left_of_mem_center x₁ x₂ y
    (by
      rw [← h.commutator_eq_center]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x₂) (Subgroup.mem_top y))

theorem centerCommutator_mul_right
    (h : IsExtraspecial 2 E) (x y₁ y₂ : E) :
    h.centerCommutator x (y₁ * y₂) =
      h.centerCommutator x y₁ * h.centerCommutator x y₂ := by
  apply Subtype.ext
  exact commutatorElement_mul_right_of_mem_center x y₁ y₂
    (by
      rw [← h.commutator_eq_center]
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y₂))

/-- The right commutator character. -/
def centerCommutatorRightHom
    (h : IsExtraspecial 2 E) (x : E) :
    E →* Subgroup.center E where
  toFun := h.centerCommutator x
  map_one' := h.centerCommutator_one_right x
  map_mul' := h.centerCommutator_mul_right x

@[simp]
theorem centerCommutatorRightHom_apply
    (h : IsExtraspecial 2 E) (x y : E) :
    h.centerCommutatorRightHom x y = h.centerCommutator x y :=
  rfl

theorem centerCommutator_left_radical
    (h : IsExtraspecial 2 E) (x : E) :
    (∀ y : E, h.centerCommutator x y = 1) ↔
      x ∈ Subgroup.center E := by
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

theorem centerCommutator_right_radical
    (h : IsExtraspecial 2 E) (y : E) :
    (∀ x : E, h.centerCommutator x y = 1) ↔
      y ∈ Subgroup.center E := by
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

theorem center_le_ker_centerCommutatorRightHom
    (h : IsExtraspecial 2 E) (x : E) :
    Subgroup.center E ≤ (h.centerCommutatorRightHom x).ker := by
  intro y hy
  exact MonoidHom.mem_ker.mpr
    ((h.centerCommutator_right_radical y).mpr hy x)

/-- Descend the right commutator character through the center. -/
def quotientCenterCommutatorRightHom
    (h : IsExtraspecial 2 E) (x : E) :
    (E ⧸ Subgroup.center E) →* Subgroup.center E :=
  QuotientGroup.lift (Subgroup.center E)
    (h.centerCommutatorRightHom x)
    (h.center_le_ker_centerCommutatorRightHom x)

@[simp]
theorem quotientCenterCommutatorRightHom_mk
    (h : IsExtraspecial 2 E) (x y : E) :
    h.quotientCenterCommutatorRightHom x
        (QuotientGroup.mk' (Subgroup.center E) y) =
      h.centerCommutator x y :=
  rfl

/-- The quotient characters are multiplicative in their first argument. -/
def quotientCenterCommutatorOuterHom
    (h : IsExtraspecial 2 E) :
    E →* ((E ⧸ Subgroup.center E) →* Subgroup.center E) where
  toFun := h.quotientCenterCommutatorRightHom
  map_one' := by
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | _ y => simp [quotientCenterCommutatorRightHom]
  map_mul' := by
    intro x₁ x₂
    apply MonoidHom.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | _ y =>
        change h.centerCommutator (x₁ * x₂) y =
          h.centerCommutator x₁ y * h.centerCommutator x₂ y
        rw [h.centerCommutator_mul_left]
        exact mul_comm _ _

@[simp]
theorem quotientCenterCommutatorOuterHom_apply_mk
    (h : IsExtraspecial 2 E) (x y : E) :
    h.quotientCenterCommutatorOuterHom x
        (QuotientGroup.mk' (Subgroup.center E) y) =
      h.centerCommutator x y :=
  rfl

theorem center_le_ker_quotientCenterCommutatorOuterHom
    (h : IsExtraspecial 2 E) :
    Subgroup.center E ≤ h.quotientCenterCommutatorOuterHom.ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | _ y =>
      change h.centerCommutator x y = 1
      exact (h.centerCommutator_left_radical x).mpr hx y

/-- The center-valued commutator pairing on `E / Z(E)`. -/
def centralQuotientCommutatorPairing
    (h : IsExtraspecial 2 E) :
    (E ⧸ Subgroup.center E) →*
      ((E ⧸ Subgroup.center E) →* Subgroup.center E) :=
  QuotientGroup.lift (Subgroup.center E)
    h.quotientCenterCommutatorOuterHom
    h.center_le_ker_quotientCenterCommutatorOuterHom

@[simp]
theorem centralQuotientCommutatorPairing_mk_mk
    (h : IsExtraspecial 2 E) (x y : E) :
    h.centralQuotientCommutatorPairing
        (QuotientGroup.mk' (Subgroup.center E) x)
        (QuotientGroup.mk' (Subgroup.center E) y) =
      h.centerCommutator x y :=
  rfl

theorem centralQuotientCommutatorPairing_alternating
    (h : IsExtraspecial 2 E) :
    ∀ q : E ⧸ Subgroup.center E,
      h.centralQuotientCommutatorPairing q q = 1 := by
  intro q
  induction q using QuotientGroup.induction_on with
  | _ x => exact h.centerCommutator_self x

theorem centralQuotientCommutatorPairing_injective
    (h : IsExtraspecial 2 E) :
    Function.Injective h.centralQuotientCommutatorPairing := by
  apply (MonoidHom.ker_eq_bot_iff h.centralQuotientCommutatorPairing).mp
  ext q
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot]
  constructor
  · intro hq
    induction q using QuotientGroup.induction_on with
    | _ x =>
        rw [QuotientGroup.eq_one_iff]
        apply (h.centerCommutator_left_radical x).mp
        intro y
        have heval := DFunLike.congr_fun hq
          (QuotientGroup.mk' (Subgroup.center E) y)
        simpa using heval
  · rintro rfl
    exact map_one _

/-! ## Linearization over `ZMod 2` -/

/-- Additive wrapper for the central quotient. -/
@[ext]
structure CentralQuotientVector
    (h : IsExtraspecial 2 E) where
  val : Additive (E ⧸ Subgroup.center E)

def centralQuotientVectorEquiv
    (h : IsExtraspecial 2 E) :
    h.CentralQuotientVector ≃ Additive (E ⧸ Subgroup.center E) where
  toFun := CentralQuotientVector.val
  invFun := CentralQuotientVector.mk
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

instance centralQuotientVectorAddCommGroup
    (h : IsExtraspecial 2 E) :
    AddCommGroup h.CentralQuotientVector := by
  letI : CommGroup (E ⧸ Subgroup.center E) :=
    { (inferInstance : Group (E ⧸ Subgroup.center E)) with
      mul_comm := h.quotient_center_commutative.comm }
  exact h.centralQuotientVectorEquiv.addCommGroup

@[simp]
theorem centralQuotientVector_val_zero
    (h : IsExtraspecial 2 E) :
    (0 : h.CentralQuotientVector).val = 0 :=
  rfl

@[simp]
theorem centralQuotientVector_val_add
    (h : IsExtraspecial 2 E)
    (x y : h.CentralQuotientVector) :
    (x + y).val = x.val + y.val :=
  rfl

def centralQuotientVectorAddEquiv
    (h : IsExtraspecial 2 E) :
    h.CentralQuotientVector ≃+
      Additive (E ⧸ Subgroup.center E) :=
  { h.centralQuotientVectorEquiv with
    map_add' := fun _ _ ↦ rfl }

instance centralQuotientVectorModule
    (h : IsExtraspecial 2 E) :
    Module (ZMod 2) h.CentralQuotientVector := by
  letI : CommGroup (E ⧸ Subgroup.center E) :=
    { (inferInstance : Group (E ⧸ Subgroup.center E)) with
      mul_comm := h.quotient_center_commutative.comm }
  letI : Module (ZMod 2)
      (Additive (E ⧸ Subgroup.center E)) := by
    apply AddCommGroup.zmodModule
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul]
    exact h.quotient_center_sq_eq_one x.toMul
  exact h.centralQuotientVectorAddEquiv.module (ZMod 2)

instance centralQuotientVectorFinite
    (h : IsExtraspecial 2 E) :
    Finite h.CentralQuotientVector := by
  exact Finite.of_equiv
    (Additive (E ⧸ Subgroup.center E))
    h.centralQuotientVectorEquiv.symm

/-- The order-two center, written additively, is `ZMod 2`. -/
def centerAddEquivZMod
    (h : IsExtraspecial 2 E) :
    Additive (Subgroup.center E) ≃+ ZMod 2 := by
  exact (zmodAddCyclicAddEquiv
    (isAddCyclic_additive_iff.mpr h.center_isCyclic)).symm
      |>.trans
        (ZMod.ringEquivCongr h.card_center).toAddEquiv

/-- Scalar value of the quotient commutator pairing. -/
def commutatorPairingValue
    (h : IsExtraspecial 2 E)
    (x y : h.CentralQuotientVector) : ZMod 2 :=
  h.centerAddEquivZMod (Additive.ofMul
    (h.centralQuotientCommutatorPairing x.val.toMul y.val.toMul))

@[simp]
theorem commutatorPairingValue_zero_left
    (h : IsExtraspecial 2 E)
    (y : h.CentralQuotientVector) :
    h.commutatorPairingValue 0 y = 0 := by
  simp [commutatorPairingValue]

@[simp]
theorem commutatorPairingValue_zero_right
    (h : IsExtraspecial 2 E)
    (x : h.CentralQuotientVector) :
    h.commutatorPairingValue x 0 = 0 := by
  simp [commutatorPairingValue]

theorem commutatorPairingValue_add_left
    (h : IsExtraspecial 2 E)
    (x₁ x₂ y : h.CentralQuotientVector) :
    h.commutatorPairingValue (x₁ + x₂) y =
      h.commutatorPairingValue x₁ y +
        h.commutatorPairingValue x₂ y := by
  simp only [commutatorPairingValue,
    centralQuotientVector_val_add, toMul_add, map_mul,
    MonoidHom.mul_apply, ofMul_mul, map_add]

theorem commutatorPairingValue_add_right
    (h : IsExtraspecial 2 E)
    (x y₁ y₂ : h.CentralQuotientVector) :
    h.commutatorPairingValue x (y₁ + y₂) =
      h.commutatorPairingValue x y₁ +
        h.commutatorPairingValue x y₂ := by
  simp [commutatorPairingValue]

def commutatorPairingRightAddHom
    (h : IsExtraspecial 2 E)
    (x : h.CentralQuotientVector) :
    h.CentralQuotientVector →+ ZMod 2 where
  toFun := h.commutatorPairingValue x
  map_zero' := h.commutatorPairingValue_zero_right x
  map_add' := h.commutatorPairingValue_add_right x

def commutatorPairingRightLinear
    (h : IsExtraspecial 2 E)
    (x : h.CentralQuotientVector) :
    h.CentralQuotientVector →ₗ[ZMod 2] ZMod 2 :=
  (h.commutatorPairingRightAddHom x).toZModLinearMap 2

def commutatorPairingOuterAddHom
    (h : IsExtraspecial 2 E) :
    h.CentralQuotientVector →+
      (h.CentralQuotientVector →ₗ[ZMod 2] ZMod 2) where
  toFun := h.commutatorPairingRightLinear
  map_zero' := by
    ext y
    exact h.commutatorPairingValue_zero_left y
  map_add' := by
    intro x₁ x₂
    ext y
    exact h.commutatorPairingValue_add_left x₁ x₂ y

/-- The commutator form on the central quotient over `ZMod 2`. -/
def commutatorBilin
    (h : IsExtraspecial 2 E) :
    LinearMap.BilinForm (ZMod 2) h.CentralQuotientVector :=
  h.commutatorPairingOuterAddHom.toZModLinearMap 2

@[simp]
theorem commutatorBilin_apply
    (h : IsExtraspecial 2 E)
    (x y : h.CentralQuotientVector) :
    h.commutatorBilin x y = h.commutatorPairingValue x y :=
  rfl

theorem commutatorPairingValue_eq_zero_iff
    (h : IsExtraspecial 2 E)
    (x y : h.CentralQuotientVector) :
    h.commutatorPairingValue x y = 0 ↔
      h.centralQuotientCommutatorPairing
        x.val.toMul y.val.toMul = 1 := by
  constructor
  · intro hzero
    have hadd : Additive.ofMul
        (h.centralQuotientCommutatorPairing
          x.val.toMul y.val.toMul) = 0 := by
      apply h.centerAddEquivZMod.injective
      simpa [commutatorPairingValue] using hzero
    exact ofMul_eq_zero.mp hadd
  · intro hone
    simp [commutatorPairingValue, hone]

theorem commutatorBilin_isAlt
    (h : IsExtraspecial 2 E) :
    h.commutatorBilin.IsAlt := by
  intro x
  rw [commutatorBilin_apply,
    h.commutatorPairingValue_eq_zero_iff]
  exact h.centralQuotientCommutatorPairing_alternating
    x.val.toMul

theorem commutatorBilin_separatingLeft
    (h : IsExtraspecial 2 E) :
    h.commutatorBilin.SeparatingLeft := by
  intro x hx
  have hchar :
      h.centralQuotientCommutatorPairing x.val.toMul = 1 := by
    apply MonoidHom.ext
    intro q
    let y : h.CentralQuotientVector := ⟨Additive.ofMul q⟩
    exact (h.commutatorPairingValue_eq_zero_iff x y).mp
      (hx y)
  have hxone : x.val.toMul = 1 :=
    h.centralQuotientCommutatorPairing_injective
      (hchar.trans
        (map_one h.centralQuotientCommutatorPairing).symm)
  apply CentralQuotientVector.ext
  apply Additive.toMul.injective
  simpa using hxone

theorem commutatorBilin_nondegenerate
    (h : IsExtraspecial 2 E) :
    h.commutatorBilin.Nondegenerate := by
  refine ⟨h.commutatorBilin_separatingLeft, ?_⟩
  intro y hy
  apply h.commutatorBilin_separatingLeft y
  intro x
  have hneg := h.commutatorBilin_isAlt.neg_eq y x
  rw [hy x] at hneg
  exact neg_eq_zero.mp hneg

/-! ## Central error terms of automorphisms -/

/-- Every automorphism of an extraspecial two-group fixes its center
pointwise. -/
theorem mulAut_apply_eq_self_of_mem_center
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (z : E) (hz : z ∈ Subgroup.center E) :
    α z = z := by
  have hαz : α z ∈ Subgroup.center E := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := α.surjective y
    simpa only [map_mul] using
      congrArg α (Subgroup.mem_center_iff.mp hz x)
  let zc : Subgroup.center E := ⟨z, hz⟩
  let αzc : Subgroup.center E := ⟨α z, hαz⟩
  obtain ⟨w, hwne, hwuniq⟩ :=
    (Nat.card_eq_two_iff' (1 : Subgroup.center E)).mp
      h.card_center
  by_cases hzOne : zc = 1
  · have hzval : z = 1 := congrArg Subtype.val hzOne
    simp [hzval]
  · have hαzcNe : αzc ≠ 1 := by
      intro hαone
      apply hzOne
      have hαzval : α z = 1 :=
        congrArg Subtype.val hαone
      have hzval : z = 1 := by
        apply α.injective
        simpa using hαzval
      apply Subtype.ext
      exact hzval
    exact congrArg Subtype.val
      ((hwuniq αzc hαzcNe).trans (hwuniq zc hzOne).symm)

/-- The central error `α(x) * x⁻¹`, as a homomorphism into the center. -/
def centralErrorHom
    (_h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E) :
    E →* Subgroup.center E where
  toFun x := ⟨α x * x⁻¹, hα x⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' := by
    intro x y
    apply Subtype.ext
    change α (x * y) * (x * y)⁻¹ =
      (α x * x⁻¹) * (α y * y⁻¹)
    have hcomm :
        x⁻¹ * (α y * y⁻¹) =
          (α y * y⁻¹) * x⁻¹ :=
      Subgroup.mem_center_iff.mp (hα y) x⁻¹
    rw [map_mul, mul_inv_rev]
    calc
      α x * α y * (y⁻¹ * x⁻¹) =
          α x * (α y * y⁻¹) * x⁻¹ := by group
      _ = α x * ((α y * y⁻¹) * x⁻¹) := by group
      _ = α x * (x⁻¹ * (α y * y⁻¹)) := by
        rw [← hcomm]
      _ = α x * x⁻¹ * (α y * y⁻¹) := by
        group

theorem center_le_ker_centralErrorHom
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E) :
    Subgroup.center E ≤ (h.centralErrorHom α hα).ker := by
  intro z hz
  apply MonoidHom.mem_ker.mpr
  apply Subtype.ext
  change α z * z⁻¹ = 1
  rw [h.mulAut_apply_eq_self_of_mem_center α z hz]
  exact mul_inv_cancel z

/-- The central error, descended to `E / Z(E)`. -/
def quotientCentralErrorHom
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E) :
    (E ⧸ Subgroup.center E) →* Subgroup.center E :=
  QuotientGroup.lift (Subgroup.center E)
    (h.centralErrorHom α hα)
    (h.center_le_ker_centralErrorHom α hα)

@[simp]
theorem quotientCentralErrorHom_mk
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E)
    (x : E) :
    h.quotientCentralErrorHom α hα
        (QuotientGroup.mk' (Subgroup.center E) x) =
      ⟨α x * x⁻¹, hα x⟩ :=
  rfl

def centralErrorAddHom
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E) :
    h.CentralQuotientVector →+
      Additive (Subgroup.center E) where
  toFun x :=
    Additive.ofMul
      (h.quotientCentralErrorHom α hα x.val.toMul)
  map_zero' := by
    change Additive.ofMul
      (h.quotientCentralErrorHom α hα 1) = 0
    simp
  map_add' := by
    intro x y
    change Additive.ofMul
      (h.quotientCentralErrorHom α hα
        (x.val.toMul * y.val.toMul)) =
      Additive.ofMul
          (h.quotientCentralErrorHom α hα x.val.toMul) +
        Additive.ofMul
          (h.quotientCentralErrorHom α hα y.val.toMul)
    simp

/-- The central error as a linear functional on the central quotient. -/
def centralErrorLinear
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E) :
    h.CentralQuotientVector →ₗ[ZMod 2] ZMod 2 :=
  ((h.centerAddEquivZMod.toAddMonoidHom).comp
    (h.centralErrorAddHom α hα)).toZModLinearMap 2

@[simp]
theorem centralErrorLinear_mk
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E)
    (x : E) :
    h.centralErrorLinear α hα
        ⟨Additive.ofMul
          (QuotientGroup.mk' (Subgroup.center E) x)⟩ =
      h.centerAddEquivZMod
        (Additive.ofMul ⟨α x * x⁻¹, hα x⟩) :=
  rfl

/-- A central automorphism of a finite extraspecial two-group is inner.

The hypothesis is the elementwise form of saying that `α` induces the
identity on `E / Z(E)`. -/
theorem exists_eq_conj_of_apply_mul_inv_mem_center
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E, α x * x⁻¹ ∈ Subgroup.center E) :
    ∃ c : E, α = MulAut.conj c := by
  let f : Module.Dual (ZMod 2) h.CentralQuotientVector :=
    h.centralErrorLinear α hα
  let cQ : h.CentralQuotientVector :=
    (h.commutatorBilin.toDual h.commutatorBilin_nondegenerate).symm f
  obtain ⟨c, hc⟩ :=
    QuotientGroup.mk'_surjective
      (Subgroup.center E) cQ.val.toMul
  refine ⟨c, ?_⟩
  apply MulEquiv.ext
  intro x
  have hform :
      h.commutatorBilin cQ
          ⟨Additive.ofMul
            (QuotientGroup.mk' (Subgroup.center E) x)⟩ =
        h.centralErrorLinear α hα
          ⟨Additive.ofMul
            (QuotientGroup.mk' (Subgroup.center E) x)⟩ := by
    exact LinearMap.BilinForm.apply_toDual_symm_apply
      (B := h.commutatorBilin) f _
  have hcenter :
      h.centerCommutator c x =
        ⟨α x * x⁻¹, hα x⟩ := by
    apply Additive.ofMul.injective
    apply h.centerAddEquivZMod.injective
    simpa only [commutatorBilin_apply, commutatorPairingValue,
      centralErrorLinear_mk, ← hc,
      centralQuotientCommutatorPairing_mk_mk] using hform
  change α x = c * x * c⁻¹
  have hval :
      ⁅c, x⁆ = α x * x⁻¹ :=
    congrArg Subtype.val hcenter
  simp only [commutatorElement_def] at hval
  exact mul_right_cancel hval.symm

/-- Quotient-action formulation of
`exists_eq_conj_of_apply_mul_inv_mem_center`. -/
theorem exists_eq_conj_of_quotient_apply_eq
    (h : IsExtraspecial 2 E) (α : MulAut E)
    (hα : ∀ x : E,
      QuotientGroup.mk' (Subgroup.center E) (α x) =
        QuotientGroup.mk' (Subgroup.center E) x) :
    ∃ c : E, α = MulAut.conj c := by
  apply h.exists_eq_conj_of_apply_mul_inv_mem_center α
  intro x
  simpa [div_eq_mul_inv] using
    QuotientGroup.eq_iff_div_mem.mp (hα x)

end IsExtraspecial

end LisiSabatini
