module

public import LisiSabatini.HallBergerResidualUniqueInvolution
public import LisiSabatini.HallBergerResidualExtraspecial

/-!
# The cyclic residual in the Hall--Berger decomposition

The maximal internal extraspecial factor can be chosen so that its
residual centralizer is cyclic.  The point requiring care is the
quaternion-looking residual: absence of noncentral involutions does not
by itself imply commutativity.  The classification-free residual theorem
shows that a noncommutative residual would itself be extraspecial, so it
could be absorbed into the chosen maximal factor.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- A strengthened form of finite maximality which retains the maximal
property needed to absorb a possible extraspecial residual. -/
theorem exists_maximal_internal_extraspecial_factor_strong
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
      (∀ J : Subgroup C,
        E ≤ J →
        IsExtraspecial 2 J →
        IsInternalCentralFactor J →
        E = J) ∧
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
  refine
    ⟨E, hE₀E, hE, hEFactor, ?_, ?_⟩
  · intro J hEJ hJ hJFactor
    exact
      hEmax.eq_of_le
        (show good J from ⟨hJ, hJFactor⟩)
        hEJ
  · intro x hxSq
    by_contra hxNotCenter
    obtain ⟨J, hJ, hJFactor, hEJ⟩ :=
      exists_strict_internal_extraspecial_extension
        hC2 hC hOmegaCenter E hE hEFactor
        x hxSq hxNotCenter
    exact
      hEJ.ne
        (hEmax.eq_of_le
          (show good J from ⟨hJ, hJFactor⟩)
          hEJ.le)

/-- A maximal internal extraspecial factor has cyclic residual
centralizer.

This is the classification-free replacement for invoking the theorem
that a finite `2`-group with a unique involution is cyclic or generalized
quaternion. -/
theorem exists_internal_extraspecial_factor_with_cyclic_residual
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
      IsCyclic
        (Subgroup.centralizer (E : Set C)) := by
  obtain
    ⟨E, hE₀E, hE, hFactor, hmax, hinv⟩ :=
      exists_maximal_internal_extraspecial_factor_strong
        hC2 hC hOmegaCenter E₀ hE₀ hE₀Factor
  let D : Subgroup C :=
    Subgroup.centralizer (E : Set C)
  have hCenterC :
      IsCyclic (Subgroup.center C) :=
    center_isCyclic_of_omegaOne_center_isCyclic
      Nat.prime_two hC2 hOmegaCenter
  have hCenterD :
      IsCyclic (Subgroup.center D) :=
    centralizer_center_isCyclic_of_internalCentralFactor
      hCenterC E hFactor
  have hDcomm : IsMulCommutative D := by
    by_contra hDnoncomm
    have hD :
        HasCentralCommutatorOfOrderTwo D :=
      hC.of_noncommutative_subgroup D hDnoncomm
    have hDextra :
        IsExtraspecial 2 D :=
      isExtraspecial_of_cyclicCenter_of_squareOne_mem_center
        (hC2.to_subgroup D) hD hCenterD hinv
    let H : Subgroup D := ⊤
    have hHextra :
        IsExtraspecial 2 H :=
      hDextra.of_mulEquiv Subgroup.topEquiv.symm
    have hHFactor :
        IsInternalCentralFactor H :=
      { generate := by simp [H]
        overlap :=
          (characteristicCenterImage_eq_inf_centralizer H).symm }
    let H' : Subgroup C := H.map D.subtype
    let eH : H ≃* H' :=
      Subgroup.equivMapOfInjective
        H D.subtype Subtype.coe_injective
    have hH'extra :
        IsExtraspecial 2 H' :=
      hHextra.of_mulEquiv eH
    have hcommEH' :
        ∀ (e : E) (d : H'),
          (e : C) * d = d * e := by
      rintro e ⟨_, hd⟩
      obtain ⟨d, _, rfl⟩ :=
        Subgroup.mem_map.mp hd
      exact d.2 e e.2
    let J : Subgroup C := E ⊔ H'
    have hJextra :
        IsExtraspecial 2 J :=
      isExtraspecial_sup_of_elementwise_commute
        hC2 hC E H' hE hH'extra hcommEH'
    have hJFactor :
        IsInternalCentralFactor J :=
      hFactor.sup_map_of_centralizer H hHFactor
    have hH'eqD : H' = D := by
      calc
        H' = (⊤ : Subgroup D).map D.subtype := rfl
        _ = D.subtype.range :=
          (MonoidHom.range_eq_map D.subtype).symm
        _ = D := Subgroup.range_subtype D
    have hJtop : J = ⊤ := by
      dsimp only [J]
      rw [hH'eqD]
      exact hFactor.generate
    have hEJ : E = J :=
      hmax J le_sup_left hJextra hJFactor
    have hEtop : E = ⊤ :=
      hEJ.trans hJtop
    have hDeqCenter :
        D = Subgroup.center C := by
      dsimp only [D]
      rw [hEtop]
      simpa only [Subgroup.coe_top] using
        (Subgroup.centralizer_univ :
          Subgroup.centralizer (Set.univ : Set C) =
            Subgroup.center C)
    apply hDnoncomm
    refine ⟨⟨fun x y ↦ Subtype.ext ?_⟩⟩
    have hxCenter :
        (x : C) ∈ Subgroup.center C := by
      rw [← hDeqCenter]
      exact x.2
    exact
      (Subgroup.mem_center_iff.mp hxCenter
        (y : C)).symm
  let groupD : Group D := inferInstance
  letI : CommGroup D :=
    { groupD with mul_comm := hDcomm.1.1 }
  rw [CommGroup.center_eq_top] at hCenterD
  exact
    ⟨E, hE₀E, hE, hFactor,
      Subgroup.topEquiv.isCyclic.mp hCenterD⟩

/-- Starting from one noncentral involution, the initial `D₈` extraction
and the preceding maximality argument produce an internal extraspecial
factor with cyclic residual centralizer. -/
theorem exists_internal_extraspecial_factor_with_cyclic_residual_of_noncentral_involution
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
      IsCyclic
        (Subgroup.centralizer (E : Set C)) := by
  obtain
    ⟨y, hySq, hxy, _, hE, hFactor, _⟩ :=
      exists_dihedralInternalCentralFactor_of_noncentralInvolution
        hC hOmegaCenter hxSq hxNotCenter
  obtain ⟨E, _, hE', hFactor', hresidual⟩ :=
    exists_internal_extraspecial_factor_with_cyclic_residual
      hC2 hC hOmegaCenter
      (twoGeneratorSubgroup x y) hE hFactor
  exact ⟨E, hE', hFactor', hresidual⟩

/-- Complete intrinsic decomposition of a noncommutative Hall--Berger
centralizer.

If there is a noncentral involution, the preceding `D₈` extraction
applies.  If there is none, the whole group is extraspecial by the
classification-free residual theorem, and may itself be taken as the
factor. -/
theorem exists_internal_extraspecial_factor_with_cyclic_residual_of_centralCommutator
    {C : Type u} [Group C] [Finite C]
    (hC2 : IsPGroup 2 C)
    (hC : HasCentralCommutatorOfOrderTwo C)
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 C))) :
    ∃ E : Subgroup C,
      IsExtraspecial 2 E ∧
      IsInternalCentralFactor E ∧
      IsCyclic
        (Subgroup.centralizer (E : Set C)) := by
  have hCenterC :
      IsCyclic (Subgroup.center C) :=
    center_isCyclic_of_omegaOne_center_isCyclic
      Nat.prime_two hC2 hOmegaCenter
  by_cases hnoncentral :
      ∃ x : C,
        x ^ 2 = 1 ∧
        x ∉ Subgroup.center C
  · obtain ⟨x, hxSq, hxNotCenter⟩ :=
      hnoncentral
    exact
      exists_internal_extraspecial_factor_with_cyclic_residual_of_noncentral_involution
        hC2 hC hOmegaCenter hxSq hxNotCenter
  · have hinv :
        ∀ x : C, x ^ 2 = 1 →
          x ∈ Subgroup.center C := by
      intro x hxSq
      by_contra hxNotCenter
      exact hnoncentral ⟨x, hxSq, hxNotCenter⟩
    have hCextra :
        IsExtraspecial 2 C :=
      isExtraspecial_of_cyclicCenter_of_squareOne_mem_center
        hC2 hC hCenterC hinv
    let E : Subgroup C := ⊤
    have hEextra :
        IsExtraspecial 2 E :=
      hCextra.of_mulEquiv Subgroup.topEquiv.symm
    have hEFactor :
        IsInternalCentralFactor E :=
      { generate := by simp [E]
        overlap :=
          (characteristicCenterImage_eq_inf_centralizer E).symm }
    have hResidual :
        IsCyclic
          (Subgroup.centralizer (E : Set C)) := by
      have hcentralizer :
          Subgroup.centralizer (E : Set C) =
            Subgroup.center C := by
        dsimp only [E]
        simpa only [Subgroup.coe_top] using
          (Subgroup.centralizer_univ :
            Subgroup.centralizer (Set.univ : Set C) =
              Subgroup.center C)
      rw [hcentralizer]
      exact hCenterC
    exact ⟨E, hEextra, hEFactor, hResidual⟩

end LisiSabatini
