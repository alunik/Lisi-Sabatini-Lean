module

public import LisiSabatini.HallBergerResidualInvolution

/-!
# The unique-involution residual in Hall--Berger

After the maximal internal extraspecial factor has been chosen, its
residual centralizer has no noncentral involutions.  Its center is cyclic,
because an internal central factor has residual center equal to the
ambient center.  Hence the residual has at most one nonidentity
involution.

This is the exact point at which the published proof invokes the
classical theorem that a finite `2`-group with a unique subgroup of order
two is cyclic or generalized quaternion.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The residual centralizer of an internal central factor has cyclic
center whenever the ambient group does. -/
theorem centralizer_center_isCyclic_of_internalCentralFactor
    {C : Type u} [Group C] [Finite C]
    (hCenterC : IsCyclic (Subgroup.center C))
    (E : Subgroup C)
    (hFactor : IsInternalCentralFactor E) :
    IsCyclic
      (Subgroup.center
        (Subgroup.centralizer (E : Set C))) := by
  let D : Subgroup C :=
    Subgroup.centralizer (E : Set C)
  have hCenterImage :
      characteristicCenterImage D =
        Subgroup.center C :=
    centralizer_centerImage_eq_center_of_isInternalCentralFactor
      hFactor
  have hImageCyclic :
      IsCyclic (characteristicCenterImage D) := by
    rw [hCenterImage]
    exact hCenterC
  exact
    (Subgroup.equivMapOfInjective
      (Subgroup.center D) D.subtype
      Subtype.coe_injective).isCyclic.mpr
        hImageCyclic

/-- If every involution is central and the center is cyclic, then there
is at most one nonidentity involution. -/
theorem eq_of_involutions_of_center_isCyclic_of_all_involutions_central
    {D : Type u} [Group D] [Finite D]
    (hCenter : IsCyclic (Subgroup.center D))
    (hcentral :
      ∀ x : D, x ^ 2 = 1 →
        x ∈ Subgroup.center D)
    {x y : D}
    (hxSq : x ^ 2 = 1) (hySq : y ^ 2 = 1)
    (hxNe : x ≠ 1) (hyNe : y ≠ 1) :
    x = y := by
  let xZ : Subgroup.center D :=
    ⟨x, hcentral x hxSq⟩
  let yZ : Subgroup.center D :=
    ⟨y, hcentral y hySq⟩
  have hxZSq : xZ ^ 2 = 1 := by
    apply Subtype.ext
    exact hxSq
  have hyZSq : yZ ^ 2 = 1 := by
    apply Subtype.ext
    exact hySq
  have hxZNe : xZ ≠ 1 := by
    intro hxZ
    exact hxNe (congrArg Subtype.val hxZ)
  have hyZNe : yZ ≠ 1 := by
    intro hyZ
    exact hyNe (congrArg Subtype.val hyZ)
  exact congrArg Subtype.val
    (eq_of_sq_eq_one_of_ne_one_of_isCyclic
      hCenter hxZSq hyZSq hxZNe hyZNe)

/-- The maximal Hall--Berger construction produces an internal
extraspecial factor whose residual has at most one nonidentity
involution. -/
theorem exists_internal_extraspecial_factor_with_unique_involution_residual
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
      ∀ {a b :
          Subgroup.centralizer (E : Set C)},
        a ^ 2 = 1 →
        b ^ 2 = 1 →
        a ≠ 1 →
        b ≠ 1 →
        a = b := by
  obtain ⟨E, hE, hFactor, hcentral⟩ :=
    exists_maximal_internal_extraspecial_factor_of_noncentral_involution
      hC2 hC hOmegaCenter hxSq hxNotCenter
  have hCenterC :
      IsCyclic (Subgroup.center C) :=
    center_isCyclic_of_omegaOne_center_isCyclic
      Nat.prime_two hC2 hOmegaCenter
  have hCenterD :
      IsCyclic
        (Subgroup.center
          (Subgroup.centralizer (E : Set C))) :=
    centralizer_center_isCyclic_of_internalCentralFactor
      hCenterC E hFactor
  refine ⟨E, hE, hFactor, ?_⟩
  intro a b haSq hbSq haNe hbNe
  exact
    eq_of_involutions_of_center_isCyclic_of_all_involutions_central
      hCenterD hcentral haSq hbSq haNe hbNe

end LisiSabatini
