import LisiSabatini.HallBergerInternalFactorComposition

/-!
# Projecting the Hall--Berger involution into a residual centralizer

Let `E` be an internal extraspecial factor of a class-two `2`-group and
put `D = C_C(E)`.  The cyclic omega-center hypothesis belongs to the
ambient group `C`; it need not be inherited by `D`.  The published
maximality argument therefore finds a noncommuting involution in `C`,
projects it through `C = ED`, and corrects its `D`-component by the
chosen involution when that component has order four.

This file formalizes exactly that projection-and-correction step.  In
particular, it does not make the invalid assumption that the residual
centralizer inherits the omega-center hypothesis.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

universe u

/-- A noncentral involution of the residual centralizer has a
noncommuting involution partner in that same residual centralizer. -/
theorem exists_residual_noncommuting_involution
    {C : Type u} [Group C] [Finite C]
    (hC : HasCentralCommutatorOfOrderTwo C)
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 C)))
    (E : Subgroup C)
    (hE : IsExtraspecial 2 E)
    (hFactor : IsInternalCentralFactor E)
    (x : Subgroup.centralizer (E : Set C))
    (hxSq : x ^ 2 = 1)
    (hxNotCenter :
      x ∉ Subgroup.center
        (Subgroup.centralizer (E : Set C))) :
    ∃ y : Subgroup.centralizer (E : Set C),
      y ^ 2 = 1 ∧ ⁅x, y⁆ ≠ 1 := by
  let D : Subgroup C :=
    Subgroup.centralizer (E : Set C)
  have hxSqC : (x : C) ^ 2 = 1 := by
    simpa using congrArg Subtype.val hxSq
  have hxNotCenterC :
      (x : C) ∉ Subgroup.center C := by
    intro hxCenterC
    apply hxNotCenter
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    exact
      Subgroup.mem_center_iff.mp hxCenterC d
  obtain ⟨t, htSq, hxt⟩ :=
    exists_noncommuting_involution_of_not_mem_center
      hOmegaCenter hxSqC hxNotCenterC
  have hcommED :
      ∀ (e : E) (d : D),
        (e : C) * d = d * e := by
    intro e d
    exact d.2 e e.2
  have htSup : t ∈ E ⊔ D := by
    rw [hFactor.generate]
    exact Subgroup.mem_top t
  obtain ⟨e, he, d, hd, hedt⟩ :=
    (mem_sup_iff_of_elementwise_commute
      E D hcommED).mp htSup
  let dD : D := ⟨d, hd⟩
  have hxd : ⁅(x : C), d⁆ ≠ 1 := by
    intro hxdOne
    apply hxt
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    rw [← hedt]
    have hxe :
        e * (x : C) = (x : C) * e :=
      x.2 e he
    have hxdComm :
        (x : C) * d = d * x :=
      commutatorElement_eq_one_iff_mul_comm.mp
        hxdOne
    calc
      (x : C) * (e * d) =
          ((x : C) * e) * d := by
        simp only [mul_assoc]
      _ = (e * x) * d := by rw [← hxe]
      _ = e * ((x : C) * d) := by
        simp only [mul_assoc]
      _ = e * (d * x) := by rw [hxdComm]
      _ = (e * d) * x := by
        simp only [mul_assoc]
  have hxdD : ⁅x, dD⁆ ≠ 1 := by
    intro hxdOne
    apply hxd
    exact congrArg Subtype.val hxdOne
  have hedSq : e ^ 2 * d ^ 2 = 1 := by
    calc
      e ^ 2 * d ^ 2 = e * (e * d) * d := by
        simp only [pow_two, mul_assoc]
      _ = e * (d * e) * d := by
        rw [hcommED ⟨e, he⟩ ⟨d, hd⟩]
      _ = (e * d) ^ 2 := by
        simp only [pow_two, mul_assoc]
      _ = t ^ 2 := by rw [hedt]
      _ = 1 := htSq
  have hdSqEq : d ^ 2 = (e ^ 2)⁻¹ :=
    eq_inv_of_mul_eq_one_right hedSq
  have hdSqE : d ^ 2 ∈ E := by
    rw [hdSqEq]
    exact E.inv_mem (E.pow_mem he 2)
  have hdSqD : d ^ 2 ∈ D :=
    D.pow_mem hd 2
  have hdSqCenterImage :
      d ^ 2 ∈ characteristicCenterImage E := by
    rw [← hFactor.overlap]
    exact ⟨hdSqE, hdSqD⟩
  have hcenterImageE :
      characteristicCenterImage E =
        commutator C :=
    characteristicCenterImage_eq_commutator_of_extraspecial
      hC E hE
  have hdSqComm :
      d ^ 2 ∈ commutator C := by
    rw [← hcenterImageE]
    exact hdSqCenterImage
  by_cases hdSq : dD ^ 2 = 1
  · exact ⟨dD, hdSq, hxdD⟩
  · let y : D := x * dD
    have hxInvC : (x : C)⁻¹ = x := by
      have hxx : (x : C) * x = 1 := by
        simpa only [pow_two] using hxSqC
      exact (mul_eq_one_iff_eq_inv.mp hxx).symm
    have hdSqNeC : d ^ 2 ≠ 1 := by
      intro hdSqC
      apply hdSq
      apply Subtype.ext
      exact hdSqC
    have hxdMem :
        ⁅(x : C), d⁆ ∈ commutator C :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top (x : C))
        (Subgroup.mem_top d)
    have hpair :
        ⁅(x : C), d⁆ * d ^ 2 = 1 :=
      mul_eq_one_of_mem_commutator_of_ne_one
        hC hxdMem hdSqComm hxd hdSqNeC
    have hySqC :
        ((x : C) * d) ^ 2 = 1 := by
      calc
        ((x : C) * d) ^ 2 =
            ⁅(x : C), d⁆ * d ^ 2 := by
          simp [pow_two, commutatorElement_def,
            hxInvC, mul_assoc]
        _ = 1 := hpair
    have hySq : y ^ 2 = 1 := by
      apply Subtype.ext
      exact hySqC
    have hxy : ⁅x, y⁆ ≠ 1 := by
      intro hxyOne
      apply hxdD
      apply commutatorElement_eq_one_iff_mul_comm.mpr
      have hxyComm :
          x * y = y * x :=
        commutatorElement_eq_one_iff_mul_comm.mp
          hxyOne
      apply mul_left_cancel (a := x)
      calc
        x * (x * dD) = x * y := by rfl
        _ = y * x := hxyComm
        _ = x * (dD * x) := by
          simp only [y, mul_assoc]
    exact ⟨y, hySq, hxy⟩

/-- A noncentral involution in the residual centralizer strictly enlarges
the chosen internal extraspecial factor.

This is the contradiction-producing form of the Hall--Berger maximality
step: the corrected residual partner generates a `D₈` central factor,
and adjoining its ambient image preserves both extraspeciality and the
internal-central-factor property. -/
theorem exists_strict_internal_extraspecial_extension
    {C : Type u} [Group C] [Finite C]
    (hC2 : IsPGroup 2 C)
    (hC : HasCentralCommutatorOfOrderTwo C)
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 C)))
    (E : Subgroup C)
    (hE : IsExtraspecial 2 E)
    (hFactor : IsInternalCentralFactor E)
    (x : Subgroup.centralizer (E : Set C))
    (hxSq : x ^ 2 = 1)
    (hxNotCenter :
      x ∉ Subgroup.center
        (Subgroup.centralizer (E : Set C))) :
    ∃ J : Subgroup C,
      IsExtraspecial 2 J ∧
      IsInternalCentralFactor J ∧
      E < J := by
  let D : Subgroup C :=
    Subgroup.centralizer (E : Set C)
  obtain ⟨y, hySq, hxy⟩ :=
    exists_residual_noncommuting_involution
      hC hOmegaCenter E hE hFactor
      x hxSq hxNotCenter
  have hDNoncomm : ¬ IsMulCommutative D := by
    intro hcomm
    apply hxy
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact hcomm.1.1 x y
  have hD :
      HasCentralCommutatorOfOrderTwo D :=
    hC.of_noncommutative_subgroup D hDNoncomm
  let H : Subgroup D :=
    twoGeneratorSubgroup x y
  have hHExtraspecial :
      IsExtraspecial 2 H :=
    twoGeneratorSubgroup_isExtraspecial
      hD hxSq hySq hxy
  have hHFactor :
      IsInternalCentralFactor H :=
    twoGeneratorSubgroup_isInternalCentralFactor
      hD x y hxy
  let H' : Subgroup C := H.map D.subtype
  let eH : H ≃* H' :=
    Subgroup.equivMapOfInjective
      H D.subtype Subtype.coe_injective
  have hH'Extraspecial :
      IsExtraspecial 2 H' :=
    hHExtraspecial.of_mulEquiv eH
  have hcommEH' :
      ∀ (e : E) (h : H'),
        (e : C) * h = h * e := by
    rintro e ⟨_, hh⟩
    obtain ⟨d, _, rfl⟩ :=
      Subgroup.mem_map.mp hh
    exact d.2 e e.2
  let J : Subgroup C := E ⊔ H'
  have hJExtraspecial :
      IsExtraspecial 2 J :=
    isExtraspecial_sup_of_elementwise_commute
      hC2 hC E H' hE hH'Extraspecial
        hcommEH'
  have hJFactor :
      IsInternalCentralFactor J :=
    hFactor.sup_map_of_centralizer H hHFactor
  have hcenterImageE :
      characteristicCenterImage E =
        commutator C :=
    characteristicCenterImage_eq_commutator_of_extraspecial
      hC E hE
  have hxNotE : (x : C) ∉ E := by
    intro hxE
    apply hxNotCenter
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have hxCenterImage :
        (x : C) ∈ characteristicCenterImage E := by
      rw [← hFactor.overlap]
      exact ⟨hxE, x.2⟩
    have hxCommutator :
        (x : C) ∈ commutator C := by
      rw [← hcenterImageE]
      exact hxCenterImage
    exact
      Subgroup.mem_center_iff.mp
        (hC.commutator_le_center hxCommutator) d
  have hxH : x ∈ H := by
    exact
      (show Subgroup.zpowers x ≤ H from le_sup_left)
        (Subgroup.mem_zpowers x)
  have hxH' : (x : C) ∈ H' :=
    Subgroup.mem_map.mpr ⟨x, hxH, rfl⟩
  have hxJ : (x : C) ∈ J :=
    (show H' ≤ J from le_sup_right) hxH'
  have hEJ : E < J :=
    lt_of_le_not_ge le_sup_left (by
      intro hJE
      exact hxNotE (hJE hxJ))
  exact ⟨J, hJExtraspecial, hJFactor, hEJ⟩

/-- A maximal internal extraspecial factor has a residual centralizer
with no noncentral involutions. -/
theorem exists_maximal_internal_extraspecial_factor
    {C : Type u} [Group C] [Finite C]
    (hC2 : IsPGroup 2 C)
    (hC : HasCentralCommutatorOfOrderTwo C)
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 C)))
    (E₀ : Subgroup C)
    (hE₀ : IsExtraspecial 2 E₀)
    (hE₀Factor : IsInternalCentralFactor E₀) :
    ∃ E : Subgroup C,
      E₀ ≤ E ∧
      IsExtraspecial 2 E ∧
      IsInternalCentralFactor E ∧
      ∀ x : Subgroup.centralizer (E : Set C),
        x ^ 2 = 1 →
        x ∈ Subgroup.center
          (Subgroup.centralizer (E : Set C)) := by
  classical
  let good : Subgroup C → Prop :=
    fun E =>
      IsExtraspecial 2 E ∧
      IsInternalCentralFactor E
  obtain ⟨E, hE₀E, hEmax⟩ :=
    Finite.exists_le_maximal
      (p := good) (a := E₀)
      (show good E₀ from ⟨hE₀, hE₀Factor⟩)
  have hE : IsExtraspecial 2 E :=
    hEmax.prop.1
  have hEFactor : IsInternalCentralFactor E :=
    hEmax.prop.2
  refine ⟨E, hE₀E, hE, hEFactor, ?_⟩
  intro x hxSq
  by_contra hxNotCenter
  obtain ⟨J, hJ, hJFactor, hEJ⟩ :=
    exists_strict_internal_extraspecial_extension
      hC2 hC hOmegaCenter E hE hEFactor
      x hxSq hxNotCenter
  have hEq : E = J :=
    hEmax.eq_of_le
      (show good J from ⟨hJ, hJFactor⟩)
      hEJ.le
  exact hEJ.ne hEq

/-- If the ambient group has a noncentral involution, the initial `D₈`
extraction and finite maximality produce an internal extraspecial factor
whose residual centralizer has no noncentral involutions. -/
theorem exists_maximal_internal_extraspecial_factor_of_noncentral_involution
    {C : Type u} [Group C] [Finite C]
    (hC2 : IsPGroup 2 C)
    (hC : HasCentralCommutatorOfOrderTwo C)
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 C)))
    {x : C} (hxSq : x ^ 2 = 1)
    (hxNotCenter : x ∉ Subgroup.center C) :
    ∃ E : Subgroup C,
      IsExtraspecial 2 E ∧
      IsInternalCentralFactor E ∧
      ∀ z : Subgroup.centralizer (E : Set C),
        z ^ 2 = 1 →
        z ∈ Subgroup.center
          (Subgroup.centralizer (E : Set C)) := by
  obtain
    ⟨y, hySq, hxy, _, hE, hEFactor, _⟩ :=
      exists_dihedralInternalCentralFactor_of_noncentralInvolution
        hC hOmegaCenter hxSq hxNotCenter
  obtain ⟨E, _, hE', hEFactor', hresidual⟩ :=
    exists_maximal_internal_extraspecial_factor
      hC2 hC hOmegaCenter
      (twoGeneratorSubgroup x y) hE hEFactor
  exact ⟨E, hE', hEFactor', hresidual⟩

end LisiSabatini
