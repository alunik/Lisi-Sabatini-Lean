import LisiSabatini.TwoCoreSymplecticTypeFrontier

/-!
# Fixed-space structure of a mixed symplectic-type two-core

This file proves the fixed-rectangle part of the mixed
extraspecial--maximal-class branch.  The proof uses the internal central
product data directly.

Every element is written as `e * h`, with `e` in the extraspecial factor
and `h` in the maximal-class head.  If `e` is noncentral, an extraspecial
commutator supplies the central-involution cycle.  If `e` is central, then
an involutory noncentral product forces `h` to be a noncentral involution;
the explicit dihedral, semidihedral, and quaternion normal forms supply
the corresponding cycle (or rule the case out).
-/

noncomputable section

namespace LisiSabatini

open scoped commutatorElement

set_option backward.isDefEq.respectTransparency false

universe u

namespace BergerMixedCentralProductData

variable {P : Type u} [Group P] [Finite P]

/-- The commuting-generation fields give an actual two-factor normal
form, without choosing a quotient model of the central product. -/
theorem exists_extraspecial_mul_head
    (data : BergerMixedCentralProductData P) (x : P) :
    ∃ (e : data.extraspecialPart) (h : data.headPart),
      e.1 * h.1 = x := by
  let productSubgroup : Subgroup P :=
    { carrier := {x | ∃ (e : data.extraspecialPart)
        (h : data.headPart), e.1 * h.1 = x}
      one_mem' := ⟨1, 1, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨e₁, h₁, rfl⟩ ⟨e₂, h₂, rfl⟩
        refine ⟨e₁ * e₂, h₁ * h₂, ?_⟩
        simp only [Subgroup.coe_mul]
        calc
          (e₁.1 * e₂.1) * (h₁.1 * h₂.1) =
              e₁.1 * (e₂.1 * h₁.1) * h₂.1 := by group
          _ = e₁.1 * (h₁.1 * e₂.1) * h₂.1 := by
            rw [data.commute e₂ h₁]
          _ = (e₁.1 * h₁.1) * (e₂.1 * h₂.1) := by group
      inv_mem' := by
        rintro _ ⟨e, h, rfl⟩
        refine ⟨e⁻¹, h⁻¹, ?_⟩
        simp only [Subgroup.coe_inv, mul_inv_rev]
        exact data.commute e⁻¹ h⁻¹ }
  have hE : data.extraspecialPart ≤ productSubgroup := by
    intro e he
    exact ⟨⟨e, he⟩, 1, by simp⟩
  have hH : data.headPart ≤ productSubgroup := by
    intro h hh
    exact ⟨1, ⟨h, hh⟩, by simp⟩
  have hxSup : x ∈ data.extraspecialPart ⊔ data.headPart := by
    rw [data.generate]
    simp
  exact (sup_le hE hH hxSup : x ∈ productSubgroup)

/-- A fixed, proof-irrelevant choice of the two internal factors. -/
noncomputable def factor
    (data : BergerMixedCentralProductData P) (x : P) :
    data.extraspecialPart × data.headPart :=
  Classical.choose
    (show ∃ p : data.extraspecialPart × data.headPart,
        p.1.1 * p.2.1 = x from by
      obtain ⟨e, h, heh⟩ := data.exists_extraspecial_mul_head x
      exact ⟨(e, h), heh⟩)

@[simp]
theorem factor_mul
    (data : BergerMixedCentralProductData P) (x : P) :
    (data.factor x).1.1 * (data.factor x).2.1 = x :=
  Classical.choose_spec
    (show ∃ p : data.extraspecialPart × data.headPart,
        p.1.1 * p.2.1 = x from by
      obtain ⟨e, h, heh⟩ := data.exists_extraspecial_mul_head x
      exact ⟨(e, h), heh⟩)

/-- The center of the extraspecial factor embeds into the center of the
whole internal central product. -/
theorem extraspecialCenter_le_center
    (data : BergerMixedCentralProductData P)
    (z : Subgroup.center data.extraspecialPart) :
    z.1.1 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨e, h, rfl⟩ := data.exists_extraspecial_mul_head x
  have hze : e.1 * z.1.1 = z.1.1 * e.1 := by
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp z.2 e)
  have hzh : z.1.1 * h.1 = h.1 * z.1.1 :=
    data.commute z.1 h
  calc
    (e.1 * h.1) * z.1.1 =
        e.1 * (h.1 * z.1.1) := by group
    _ = e.1 * (z.1.1 * h.1) := by rw [← hzh]
    _ = (e.1 * z.1.1) * h.1 := by group
    _ = (z.1.1 * e.1) * h.1 := by rw [hze]
    _ = z.1.1 * (e.1 * h.1) := by group

/-- The center of the maximal-class head also embeds into the center of
the whole internal central product. -/
theorem headCenter_le_center
    (data : BergerMixedCentralProductData P)
    (z : Subgroup.center data.headPart) :
    z.1.1 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro x
  obtain ⟨e, h, rfl⟩ := data.exists_extraspecial_mul_head x
  have hzh : h.1 * z.1.1 = z.1.1 * h.1 := by
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp z.2 h)
  have hez : e.1 * z.1.1 = z.1.1 * e.1 :=
    data.commute e z.1
  calc
    (e.1 * h.1) * z.1.1 =
        e.1 * (h.1 * z.1.1) := by group
    _ = e.1 * (z.1.1 * h.1) := by rw [hzh]
    _ = (e.1 * z.1.1) * h.1 := by group
    _ = (z.1.1 * e.1) * h.1 := by rw [hez]
    _ = z.1.1 * (e.1 * h.1) := by group

end BergerMixedCentralProductData

namespace BergerMaximalClassHead

variable {H : Type u} [Group H] [Finite H]

/-- A noncentral involution in a maximal-class head has a
central-involution commutator cycle.  The quaternion branch is empty. -/
theorem exists_centralInvolutionCycle_of_orderOf_eq_two
    (head : BergerMaximalClassHead H)
    (x : H) (hxOrder : orderOf x = 2)
    (hxNoncentral : x ∉ Subgroup.center H) :
    ∃ (y : H) (z : Subgroup.center H),
      z ≠ 1 ∧ z ^ 2 = 1 ∧
        x * y = z.1 * y * x := by
  cases head with
  | dihedral k hk equiv =>
      cases hxImage : equiv x with
      | r i =>
          exfalso
          apply hxNoncentral
          apply (MulEquivClass.apply_mem_center_iff equiv).mp
          rw [hxImage]
          apply DihedralGroup.r_mem_center_of_orderOf_eq_two
          simpa [← hxImage, equiv.orderOf_eq] using hxOrder
      | sr i =>
          let y : H :=
            equiv.symm
              (DihedralGroup.r ((k : ℕ) : ZMod (4 * k)))
          let zValue : H :=
            equiv.symm
              (DihedralGroup.r ((2 * k : ℕ) : ZMod (4 * k)))
          have hzValueCenter :
              zValue ∈ Subgroup.center H := by
            apply (MulEquivClass.apply_mem_center_iff equiv).mp
            simp only [zValue, MulEquiv.apply_symm_apply]
            exact DihedralGroup.r_two_mul_mem_center k
          let z : Subgroup.center H :=
            ⟨zValue, hzValueCenter⟩
          have hzNe : z ≠ 1 := by
            intro hz
            apply DihedralGroup.r_two_mul_ne_one k (by omega)
            have hzValue : zValue = 1 :=
              congrArg Subtype.val hz
            simpa [zValue] using congrArg equiv hzValue
          have hzSq : z ^ 2 = 1 := by
            apply Subtype.ext
            apply equiv.injective
            simpa [z, zValue] using
              DihedralGroup.r_two_mul_sq k
          have hcycle : x * y = z.1 * y * x := by
            apply equiv.injective
            simpa [hxImage, y, z, zValue] using
              DihedralGroup.reflection_centralInvolutionCycle k i
          exact ⟨y, z, hzNe, hzSq, hcycle⟩
  | semidihedral k hk presentation =>
      rcases presentation.exists_rotation_or_coset x with
        ⟨i, hi⟩ | ⟨i, hi⟩
      · exfalso
        apply hxNoncentral
        rw [hi]
        apply presentation.rotation_mem_center_of_orderOf_eq_two
        simpa [← hi] using hxOrder
      · let y : H :=
          presentation.rotation
            ((2 * k : ℕ) : ZMod (8 * k))
        let zValue : H :=
          presentation.rotation
            ((4 * k : ℕ) : ZMod (8 * k))
        have hzValueCenter :
            zValue ∈ Subgroup.center H := by
          simpa [zValue] using presentation.halfTurn_mem_center
        let z : Subgroup.center H :=
          ⟨zValue, hzValueCenter⟩
        have hzNe : z ≠ 1 := by
          intro hz
          apply presentation.halfTurn_ne_one hk
          exact congrArg Subtype.val hz
        have hzSq : z ^ 2 = 1 := by
          apply Subtype.ext
          simpa [z, zValue] using presentation.halfTurn_sq
        have hcycle : x * y = z.1 * y * x := by
          rw [hi]
          simpa [y, z, zValue] using
            presentation.coset_centralInvolutionCycle i
        exact ⟨y, z, hzNe, hzSq, hcycle⟩
  | generalizedQuaternion n hn equiv =>
      letI : NeZero n := ⟨by omega⟩
      exfalso
      exact hxNoncentral
        ((quaternionGroup_allInvolutionsCentral n).of_mulEquiv equiv
          x hxOrder)

end BergerMaximalClassHead

namespace BergerMixedCentralProductData

variable {P : Type u} [Group P] [Finite P]

/-- Every noncentral involution in an internal mixed central product has
the central-involution cycle needed by the fixed-space argument. -/
theorem exists_centralInvolutionCycle_of_orderOf_eq_two
    (data : BergerMixedCentralProductData P)
    (x : P) (hxOrder : orderOf x = 2)
    (hxNoncentral : x ∉ Subgroup.center P) :
    ∃ (y : P) (z : Subgroup.center P),
      z ≠ 1 ∧ z ^ 2 = 1 ∧
        x * y = z.1 * y * x := by
  obtain ⟨e, h, heh⟩ := data.exists_extraspecial_mul_head x
  by_cases heCenter : e ∈ Subgroup.center data.extraspecialPart
  · have heSq : e.1 ^ 2 = 1 := by
      let ec : Subgroup.center data.extraspecialPart :=
        ⟨e, heCenter⟩
      have hpow :
          ec ^ Nat.card (Subgroup.center data.extraspecialPart) = 1 :=
        pow_card_eq_one'
      have hpowTwo : ec ^ 2 = 1 := by
        simpa [data.extraspecial.card_center] using hpow
      exact congrArg (fun w :
        Subgroup.center data.extraspecialPart ↦ w.1.1) hpowTwo
    have hxSq : x ^ 2 = 1 := by
      rw [← hxOrder]
      exact pow_orderOf_eq_one x
    have hhSq : h.1 ^ 2 = 1 := by
      have hehComm : Commute e.1 h.1 :=
        data.commute e h
      calc
        h.1 ^ 2 = e.1 ^ 2 * h.1 ^ 2 := by rw [heSq, one_mul]
        _ = (e.1 * h.1) ^ 2 := by
          exact (hehComm.mul_pow 2).symm
        _ = x ^ 2 := by rw [heh]
        _ = 1 := hxSq
    have hhOrder : orderOf h = 2 := by
      have hhSqHead : h ^ 2 = 1 := by
        apply Subtype.ext
        exact hhSq
      apply orderOf_eq_prime hhSqHead
      intro hhOne
      apply hxNoncentral
      have heWhole :
          e.1 ∈ Subgroup.center P :=
        data.extraspecialCenter_le_center ⟨e, heCenter⟩
      have hhWhole :
          h.1 ∈ Subgroup.center P := by
        subst h
        simp
      rw [← heh]
      exact Subgroup.center P |>.mul_mem heWhole hhWhole
    have hhNoncentral :
        h ∉ Subgroup.center data.headPart := by
      intro hhCenter
      apply hxNoncentral
      have heWhole :
          e.1 ∈ Subgroup.center P :=
        data.extraspecialCenter_le_center ⟨e, heCenter⟩
      have hhWhole :
          h.1 ∈ Subgroup.center P :=
        data.headCenter_le_center ⟨h, hhCenter⟩
      rw [← heh]
      exact Subgroup.center P |>.mul_mem heWhole hhWhole
    obtain ⟨y, zHead, hzNe, hzSq, hhy⟩ :=
      data.head.exists_centralInvolutionCycle_of_orderOf_eq_two
        h hhOrder hhNoncentral
    let z : Subgroup.center P :=
      ⟨zHead.1.1, data.headCenter_le_center zHead⟩
    have hzWholeNe : z ≠ 1 := by
      intro hz
      apply hzNe
      apply Subtype.ext
      simpa [z] using congrArg Subtype.val hz
    have hzWholeSq : z ^ 2 = 1 := by
      apply Subtype.ext
      exact congrArg (fun w :
        Subgroup.center data.headPart ↦ w.1.1) hzSq
    have hcycle : x * y.1 = z.1 * y.1 * x := by
      rw [← heh]
      have hey : e.1 * y.1 = y.1 * e.1 :=
        data.commute e y
      have hez : e.1 * zHead.1.1 = zHead.1.1 * e.1 :=
        data.commute e zHead.1
      have hhyP :
          h.1 * y.1 = zHead.1.1 * y.1 * h.1 :=
        congrArg Subtype.val hhy
      dsimp only [z]
      calc
        (e.1 * h.1) * y.1 =
            e.1 * (h.1 * y.1) := by group
        _ = e.1 * (zHead.1.1 * y.1 * h.1) := by rw [hhyP]
        _ = (e.1 * zHead.1.1) * y.1 * h.1 := by group
        _ = (zHead.1.1 * e.1) * y.1 * h.1 := by rw [hez]
        _ = zHead.1.1 * (e.1 * y.1) * h.1 := by group
        _ = zHead.1.1 * (y.1 * e.1) * h.1 := by rw [hey]
        _ = zHead.1.1 * y.1 * (e.1 * h.1) := by group
    exact ⟨y.1, z, hzWholeNe, hzWholeSq, hcycle⟩
  · obtain ⟨y, zExtra, hzNe, hzSq, hey⟩ :=
      data.extraspecial.hasCentralCommutatorOfOrderTwo
        |>.exists_central_involution_cycle e heCenter
    let z : Subgroup.center P :=
      ⟨zExtra.1.1, data.extraspecialCenter_le_center zExtra⟩
    have hzWholeNe : z ≠ 1 := by
      intro hz
      apply hzNe
      apply Subtype.ext
      simpa [z] using congrArg Subtype.val hz
    have hzWholeSq : z ^ 2 = 1 := by
      apply Subtype.ext
      exact congrArg (fun w :
        Subgroup.center data.extraspecialPart ↦ w.1.1) hzSq
    have hcycle : x * y.1 = z.1 * y.1 * x := by
      rw [← heh]
      have hhy : h.1 * y.1 = y.1 * h.1 :=
        (data.commute y h).symm
      have heyP :
          e.1 * y.1 = zExtra.1.1 * y.1 * e.1 :=
        congrArg Subtype.val hey
      dsimp only [z]
      calc
        (e.1 * h.1) * y.1 =
            e.1 * (h.1 * y.1) := by group
        _ = e.1 * (y.1 * h.1) := by rw [hhy]
        _ = (e.1 * y.1) * h.1 := by group
        _ = (zExtra.1.1 * y.1 * e.1) * h.1 := by rw [heyP]
        _ = zExtra.1.1 * y.1 * (e.1 * h.1) := by group
    exact ⟨y.1, z, hzWholeNe, hzWholeSq, hcycle⟩

end BergerMixedCentralProductData

/-- The mixed fixed-rectangle statement follows from the internal central
product data; it is not an additional classification input. -/
theorem mixedCentralProductFixedRectangle :
    MixedCentralProductFixedRectangleStatement := by
  intro r d _ P _ hdata hdeven C x hx
  obtain ⟨data⟩ := hdata
  have hxOrder : orderOf x = 2 :=
    (mem_activePrimeOrderElements 2 P x).mp hx |>.1
  have hxActive : x ∈ nonzeroFixingElements P :=
    (mem_activePrimeOrderElements 2 P x).mp hx |>.2
  have hxNoncentral : x ∉ Subgroup.center P :=
    C.active_not_mem_center x hxActive
  obtain ⟨y, z, hzNe, hzSq, hxy⟩ :=
    data.exists_centralInvolutionCycle_of_orderOf_eq_two
      x hxOrder hxNoncentral
  exact
    fixedVectorSet_sq_le_of_symplecticType_centralInvolutionCycle
      hdeven P C x y z hzNe hzSq hxy

end LisiSabatini
