import LisiSabatini.HallBergerCentralFactor

/-!
# Extracting a noncommuting involution in the BKN proof

The maximal central-product step in Berger--Kovács--Newman repeatedly
uses the following consequence of its exact hypothesis.  If
`Z(Ω₁(C))` is cyclic, then a noncentral involution of `C` cannot lie in
`Z(Ω₁(C))`; hence it fails to commute with one of the involutions that
generate `Ω₁(C)`.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

universe u

/-- A finite cyclic group has at most one nonidentity element whose
square is one. -/
theorem eq_of_sq_eq_one_of_ne_one_of_isCyclic
    {A : Type u} [Group A] [Finite A]
    (hA : IsCyclic A)
    {a b : A}
    (haSq : a ^ 2 = 1) (hbSq : b ^ 2 = 1)
    (haNe : a ≠ 1) (hbNe : b ≠ 1) :
    a = b := by
  letI : IsCyclic A := hA
  let groupA : Group A := inferInstance
  letI : CommGroup A :=
    { groupA with mul_comm := IsCyclic.commutative.comm }
  let K : Subgroup A := (powMonoidHom 2 : A →* A).ker
  let aK : K := ⟨a, MonoidHom.mem_ker.mpr haSq⟩
  let bK : K := ⟨b, MonoidHom.mem_ker.mpr hbSq⟩
  have haKNe : aK ≠ 1 := by
    intro h
    exact haNe (congrArg Subtype.val h)
  have hbKNe : bK ≠ 1 := by
    intro h
    exact hbNe (congrArg Subtype.val h)
  letI : Nontrivial K := ⟨⟨aK, 1, haKNe⟩⟩
  have hcardLe : Nat.card K ≤ 2 := by
    rw [IsCyclic.card_powMonoidHom_ker A 2]
    exact Nat.gcd_le_right _ (by norm_num)
  have hcard : Nat.card K = 2 := by
    have hcardGt : 1 < Nat.card K := Finite.one_lt_card
    omega
  obtain ⟨z, _hzNe, hzUnique⟩ :=
    (Nat.card_eq_two_iff' (1 : K)).mp hcard
  exact congrArg Subtype.val
    ((hzUnique aK haKNe).trans (hzUnique bK hbKNe).symm)

/-- An involution lying in the center of `Ω₁(C)` is central in `C` when
that omega-one center is cyclic.

The proof uses characteristicity: every conjugate is another
nonidentity involution in the same finite cyclic subgroup, hence it is
the original element. -/
theorem involution_mem_center_of_mem_omegaOne_centerImage
    {C : Type u} [Group C] [Finite C]
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 C)))
    {x : C} (hxSq : x ^ 2 = 1) (hxNe : x ≠ 1)
    (hxCenterImage :
      x ∈ characteristicCenterImage (omegaOneSubgroup 2 C)) :
    x ∈ Subgroup.center C := by
  let Omega : Subgroup C := omegaOneSubgroup 2 C
  let A : Subgroup C := characteristicCenterImage Omega
  have hAcyclic : IsCyclic A :=
    (Subgroup.equivMapOfInjective
      (Subgroup.center Omega) Omega.subtype
      Subtype.coe_injective).isCyclic.mp hOmegaCenter
  letI : Omega.Characteristic :=
    omegaOneSubgroup_characteristic 2 C
  letI : A.Characteristic :=
    characteristicCenterImage_characteristic Omega
  rw [Subgroup.mem_center_iff]
  intro g
  have hxA : x ∈ A := hxCenterImage
  have hconjA : g * x * g⁻¹ ∈ A :=
    (inferInstance : A.Normal).conj_mem x hxA g
  have hconjSq : (g * x * g⁻¹) ^ 2 = 1 := by
    calc
      (g * x * g⁻¹) ^ 2 = g * x ^ 2 * g⁻¹ := by
        simp only [pow_two, mul_assoc, inv_mul_cancel_left]
      _ = 1 := by rw [hxSq]; simp
  have hconjNe : g * x * g⁻¹ ≠ 1 := by
    intro h
    apply hxNe
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [h]; simp
  let xA : A := ⟨x, hxA⟩
  let gxA : A := ⟨g * x * g⁻¹, hconjA⟩
  have hxASq : xA ^ 2 = 1 := by
    apply Subtype.ext
    exact hxSq
  have hgxASq : gxA ^ 2 = 1 := by
    apply Subtype.ext
    exact hconjSq
  have hxANe : xA ≠ 1 := by
    intro h
    exact hxNe (congrArg Subtype.val h)
  have hgxANe : gxA ≠ 1 := by
    intro h
    exact hconjNe (congrArg Subtype.val h)
  have hsame : xA = gxA :=
    eq_of_sq_eq_one_of_ne_one_of_isCyclic
      hAcyclic hxASq hgxASq hxANe hgxANe
  have hconj : g * x * g⁻¹ = x :=
    (congrArg Subtype.val hsame).symm
  calc
    g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [hconj]

/-- Under the exact BKN cyclic omega-one-center hypothesis, every
noncentral involution has a noncommuting involution partner. -/
theorem exists_noncommuting_involution_of_not_mem_center
    {C : Type u} [Group C] [Finite C]
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 C)))
    {x : C} (hxSq : x ^ 2 = 1)
    (hxNotCenter : x ∉ Subgroup.center C) :
    ∃ y : C, y ^ 2 = 1 ∧ ⁅x, y⁆ ≠ 1 := by
  have hxNe : x ≠ 1 := by
    intro hx
    subst x
    exact hxNotCenter (Subgroup.one_mem _)
  by_contra hExists
  push Not at hExists
  have hxOmega : x ∈ omegaOneSubgroup 2 C :=
    Subgroup.subset_closure hxSq
  have hxCentralizer :
      x ∈ Subgroup.centralizer
        (omegaOneSubgroup 2 C : Set C) := by
    change x ∈
      Subgroup.centralizer
        (Subgroup.closure {y : C | y ^ 2 = 1} : Set C)
    rw [Subgroup.centralizer_closure]
    intro y hy
    exact
      (commutatorElement_eq_one_iff_mul_comm.mp
        (hExists y hy)).symm
  have hxCenterImage :
      x ∈ characteristicCenterImage (omegaOneSubgroup 2 C) := by
    rw [characteristicCenterImage_eq_inf_centralizer]
    exact ⟨hxOmega, hxCentralizer⟩
  exact hxNotCenter
    (involution_mem_center_of_mem_omegaOne_centerImage
      hOmegaCenter hxSq hxNe hxCenterImage)

end LisiSabatini
