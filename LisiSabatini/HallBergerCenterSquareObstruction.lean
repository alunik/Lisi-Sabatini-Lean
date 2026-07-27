import LisiSabatini.HallBergerResidualCyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The square obstruction in the first Hall--Berger branch

The first branch of the Berger--Kovács--Newman Frattini dichotomy would
identify the Frattini subgroup with the center of its centralizer.  A
square generator of that center is impossible once the center has more
than two elements.

The key intrinsic fact proved here is slightly more precise.  In an
internal central product of an extraspecial `2`-group and a cyclic
residual factor, every ambient square which is central is already a
square *inside the center*.  Since the square subgroup of a nontrivial
finite cyclic `2`-group has index two, such a square cannot generate the
center.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The square subgroup of a nontrivial finite cyclic `2`-group is
proper. -/
theorem powMonoidHom_two_range_ne_top_of_cyclic_two_group
    {D : Type u} [CommGroup D] [Finite D]
    (hD2 : IsPGroup 2 D)
    (hDcyclic : IsCyclic D)
    (hDnontrivial : 1 < Nat.card D) :
    (powMonoidHom 2 : D →* D).range ≠ ⊤ := by
  letI : IsCyclic D := hDcyclic
  let R : Subgroup D :=
    (powMonoidHom 2 : D →* D).range
  have htwoDvdD : 2 ∣ Nat.card D := by
    rcases hD2.card_eq_or_dvd with hcard | hdvd
    · omega
    · exact hdvd
  have hgcd : (Nat.card D).gcd 2 = 2 :=
    Nat.gcd_eq_right_iff_dvd.mpr htwoDvdD
  have hRindex : R.index = 2 := by
    simpa only [R, hgcd] using
      (IsCyclic.index_powMonoidHom_range D 2)
  intro hR
  have hR' : R = ⊤ := by
    simpa only [R] using hR
  have hindexOne : R.index = 1 := by
    rw [hR', Subgroup.index_top]
  omega

/-- No square generates a nontrivial finite cyclic `2`-group. -/
theorem zpowers_square_ne_top_of_cyclic_two_group
    {D : Type u} [Group D] [Finite D]
    (hD2 : IsPGroup 2 D)
    (hDcyclic : IsCyclic D)
    (hDnontrivial : 1 < Nat.card D)
    (x : D) :
    Subgroup.zpowers (x ^ 2) ≠ ⊤ := by
  let groupD : Group D := inferInstance
  letI : CommGroup D :=
    { groupD with mul_comm := hDcyclic.commutative.comm }
  let R : Subgroup D :=
    (powMonoidHom 2 : D →* D).range
  have hRneTop : R ≠ ⊤ := by
    simpa only [R] using
      powMonoidHom_two_range_ne_top_of_cyclic_two_group
        hD2 hDcyclic hDnontrivial
  have hxR : x ^ 2 ∈ R :=
    MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hzpowersLe :
      Subgroup.zpowers (x ^ 2) ≤ R :=
    Subgroup.zpowers_le_of_mem hxR
  intro htop
  apply hRneTop
  exact top_unique (htop ▸ hzpowersLe)

/-- In a finite cyclic `2`-group of order greater than two, every
involution is a square.  The identity is included in the statement. -/
theorem mem_powMonoidHom_two_range_of_sq_eq_one_of_cyclic_two_group
    {D : Type u} [CommGroup D] [Finite D]
    (hD2 : IsPGroup 2 D)
    (hDcyclic : IsCyclic D)
    (hDlarge : 2 < Nat.card D)
    {z : D} (hzSq : z ^ 2 = 1) :
    z ∈ (powMonoidHom 2 : D →* D).range := by
  letI : IsCyclic D := hDcyclic
  let R : Subgroup D :=
    (powMonoidHom 2 : D →* D).range
  have htwoDvdD : 2 ∣ Nat.card D := by
    rcases hD2.card_eq_or_dvd with hcard | hdvd
    · omega
    · exact hdvd
  have hgcd : (Nat.card D).gcd 2 = 2 :=
    Nat.gcd_eq_right_iff_dvd.mpr htwoDvdD
  have hRindex : R.index = 2 := by
    simpa only [R, hgcd] using
      (IsCyclic.index_powMonoidHom_range D 2)
  have hRcardMul :
      Nat.card R * 2 = Nat.card D := by
    simpa only [hRindex] using R.card_mul_index
  have hRcardGt : 1 < Nat.card R := by
    omega
  have hR2 : IsPGroup 2 R :=
    hD2.to_subgroup R
  have htwoDvdR : 2 ∣ Nat.card R := by
    rcases hR2.card_eq_or_dvd with hcard | hdvd
    · omega
    · exact hdvd
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hrOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) 2 htwoDvdR
  have hrSqR : r ^ 2 = 1 := by
    rw [← hrOrder]
    exact pow_orderOf_eq_one r
  have hrSqD : (r : D) ^ 2 = 1 :=
    congrArg Subtype.val hrSqR
  have hrNeD : (r : D) ≠ 1 := by
    intro hr
    have hrR : r = 1 := Subtype.ext hr
    rw [hrR, orderOf_one] at hrOrder
    norm_num at hrOrder
  by_cases hzOne : z = 1
  · rw [hzOne]
    exact MonoidHom.mem_range.mpr ⟨1, by simp⟩
  · have hzr : z = (r : D) :=
      eq_of_sq_eq_one_of_ne_one_of_isCyclic
        hDcyclic hzSq hrSqD hzOne hrNeD
    rw [hzr]
    exact r.2

/-- The residual centralizer of an internal central factor is the ambient
center as soon as that residual is cyclic. -/
theorem centralizer_eq_center_of_isInternalCentralFactor_of_isCyclic
    {C : Type u} [Group C]
    (E : Subgroup C)
    (hFactor : IsInternalCentralFactor E)
    (hResidualCyclic :
      IsCyclic
        (Subgroup.centralizer (E : Set C))) :
    Subgroup.centralizer (E : Set C) =
      Subgroup.center C := by
  let D : Subgroup C :=
    Subgroup.centralizer (E : Set C)
  have hDcenterImage :
      characteristicCenterImage D = D := by
    rw [characteristicCenterImage_eq_inf_centralizer]
    apply le_antisymm inf_le_left
    intro d hd
    refine ⟨hd, ?_⟩
    intro d' hd'
    exact congrArg Subtype.val
      (hResidualCyclic.commutative.comm
        (⟨d', hd'⟩ : D) (⟨d, hd⟩ : D))
  calc
    D = characteristicCenterImage D :=
      hDcenterImage.symm
    _ = Subgroup.center C :=
      centralizer_centerImage_eq_center_of_isInternalCentralFactor
        hFactor

/-- In an internal central product of an extraspecial factor and a
cyclic residual factor, a central ambient square is a square in the
ambient center, provided that center has order greater than two. -/
theorem square_mem_centerSquareImage_of_internal_extraspecial_cyclic_factor
    {C : Type u} [Group C] [Finite C]
    (hC2 : IsPGroup 2 C)
    (hC : HasCentralCommutatorOfOrderTwo C)
    (E : Subgroup C)
    (hE : IsExtraspecial 2 E)
    (hFactor : IsInternalCentralFactor E)
    (hResidualCyclic :
      IsCyclic (Subgroup.centralizer (E : Set C)))
    (hCenterLarge : 2 < Nat.card (Subgroup.center C))
    {x : C} (hxCenter : x ^ 2 ∈ Subgroup.center C) :
    x ^ 2 ∈
      ((powMonoidHom 2 :
          Subgroup.center C →* Subgroup.center C).range).map
        (Subgroup.center C).subtype := by
  classical
  let D : Subgroup C :=
    Subgroup.centralizer (E : Set C)
  let Z : Subgroup C :=
    Subgroup.center C
  have hcommED :
      ∀ (e : E) (d : D),
        (e : C) * d = d * e := by
    intro e d
    exact d.2 e e.2
  have hDcenterImage :
      characteristicCenterImage D = D := by
    rw [characteristicCenterImage_eq_inf_centralizer]
    apply le_antisymm inf_le_left
    intro d hd
    refine ⟨hd, ?_⟩
    intro d' hd'
    exact congrArg Subtype.val
      (hResidualCyclic.commutative.comm
        (⟨d', hd'⟩ : D) (⟨d, hd⟩ : D))
  have hDeqZ : D = Z := by
    simpa only [D, Z] using
      centralizer_eq_center_of_isInternalCentralFactor_of_isCyclic
        E hFactor hResidualCyclic
  have hxTop : x ∈ E ⊔ D := by
    rw [hFactor.generate]
    exact Subgroup.mem_top x
  obtain ⟨e, heE, d, hdD, hed⟩ :=
    (mem_sup_iff_of_elementwise_commute
      E D hcommED).mp hxTop
  have hedComm : Commute e d :=
    hcommED ⟨e, heE⟩ ⟨d, hdD⟩
  have hxSqEq :
      x ^ 2 = e ^ 2 * d ^ 2 := by
    rw [← hed]
    exact hedComm.mul_pow 2
  have hdZ : d ∈ Z := by
    rw [← hDeqZ]
    exact hdD
  have heSqD : e ^ 2 ∈ D := by
    rw [hDeqZ]
    have hdSqZ : d ^ 2 ∈ Z :=
      Z.pow_mem hdZ 2
    have heSqEq :
        e ^ 2 = x ^ 2 * (d ^ 2)⁻¹ := by
      rw [hxSqEq]
      group
    rw [heSqEq]
    exact Z.mul_mem hxCenter (Z.inv_mem hdSqZ)
  have heSqCenterImage :
      e ^ 2 ∈ characteristicCenterImage E := by
    rw [← hFactor.overlap]
    exact ⟨E.pow_mem heE 2, heSqD⟩
  have heSqComm :
      e ^ 2 ∈ commutator C := by
    rw [←
      characteristicCenterImage_eq_commutator_of_extraspecial
        hC E hE]
    exact heSqCenterImage
  have heFourth : (e ^ 2) ^ 2 = 1 := by
    let eComm : commutator C :=
      ⟨e ^ 2, heSqComm⟩
    have hpow :
        eComm ^ Nat.card (commutator C) = 1 :=
      pow_card_eq_one'
    have hpowTwo : eComm ^ 2 = 1 := by
      simpa only [hC.card_commutator] using hpow
    exact congrArg Subtype.val hpowTwo
  have hDlarge : 2 < Nat.card D := by
    rw [hDeqZ]
    exact hCenterLarge
  have hD2 : IsPGroup 2 D :=
    hC2.to_subgroup D
  let groupD : Group D := inferInstance
  letI : CommGroup D :=
    { groupD with
      mul_comm := hResidualCyclic.commutative.comm }
  let eSqD : D := ⟨e ^ 2, heSqD⟩
  have heSqDSq : eSqD ^ 2 = 1 := by
    apply Subtype.ext
    exact heFourth
  have heSqRange :
      eSqD ∈ (powMonoidHom 2 : D →* D).range :=
    mem_powMonoidHom_two_range_of_sq_eq_one_of_cyclic_two_group
      hD2 hResidualCyclic hDlarge heSqDSq
  obtain ⟨w, hw⟩ :=
    MonoidHom.mem_range.mp heSqRange
  have hwSq : w ^ 2 = eSqD := by
    simpa only [powMonoidHom_apply] using hw
  let dD : D := ⟨d, hdD⟩
  let sD : D := w * dD
  have hsSq : (sD : C) ^ 2 = x ^ 2 := by
    change (((w * dD) ^ 2 : D) : C) = x ^ 2
    rw [mul_pow, hwSq]
    change e ^ 2 * d ^ 2 = x ^ 2
    exact hxSqEq.symm
  let sZ : Z :=
    ⟨(sD : C), by
      rw [← hDeqZ]
      exact sD.2⟩
  apply Subgroup.mem_map.mpr
  refine
    ⟨sZ ^ 2,
      MonoidHom.mem_range.mpr ⟨sZ, rfl⟩,
      ?_⟩
  change (sD : C) ^ 2 = x ^ 2
  exact hsSq

end LisiSabatini
