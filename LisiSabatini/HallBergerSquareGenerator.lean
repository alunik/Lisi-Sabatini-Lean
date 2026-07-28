module

public import LisiSabatini.HallBergerSquareFrattini
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Extracting a square generator

If the normal closure of all squares in an ambient group is a cyclic
`2`-subgroup `H`, then one ambient square generates `H`.  This is the
precise finite-cyclic step used in the first branch of the
Berger--Kovács--Newman Frattini dichotomy.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- In a commutative group, the normal closure of all squares is just
the range of the squaring homomorphism. -/
theorem primePowerNormalClosure_two_eq_powMonoidHom_range
    (H : Type u) [CommGroup H] :
    primePowerNormalClosure 2 H =
      (powMonoidHom 2 : H →* H).range := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro _ ⟨x, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  · intro z hz
    obtain ⟨x, rfl⟩ :=
      MonoidHom.mem_range.mp hz
    exact
      Subgroup.subset_normalClosure ⟨x, rfl⟩

/-- If a cyclic `2`-subgroup is the ambient normal closure of all
squares and has more than one element, one ambient square generates the
whole subgroup. -/
theorem exists_square_generator_of_primePowerNormalClosure_eq_cyclic
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G)
    (hH2 : IsPGroup 2 H)
    (hHcyclic : IsCyclic H)
    (hHnontrivial : 1 < Nat.card H)
    (hclosure :
      primePowerNormalClosure 2 G = H) :
    ∃ x : G, Subgroup.zpowers (x ^ 2) = H := by
  classical
  have hHnormal : H.Normal := by
    rw [← hclosure]
    infer_instance
  letI : H.Normal := hHnormal
  let groupH : Group H := inferInstance
  letI : CommGroup H :=
    { groupH with
      mul_comm := hHcyclic.commutative.comm }
  let R : Subgroup H :=
    (powMonoidHom 2 : H →* H).range
  let S : Subgroup G :=
    R.map H.subtype
  have htwoDvdH : 2 ∣ Nat.card H := by
    rcases hH2.card_eq_or_dvd with hcard | hdvd
    · omega
    · exact hdvd
  have hgcd : (Nat.card H).gcd 2 = 2 :=
    Nat.gcd_eq_right_iff_dvd.mpr htwoDvdH
  have hRindex : R.index = 2 := by
    simpa only [R, hgcd] using
      (IsCyclic.index_powMonoidHom_range H 2)
  have hRneTop : R ≠ ⊤ := by
    intro hR
    have hindexOne : R.index = 1 := by
      rw [hR, Subgroup.index_top]
    omega
  have hSneH : S ≠ H := by
    intro hSH
    have hmapTop :
        (⊤ : Subgroup H).map H.subtype = H := by
      calc
        (⊤ : Subgroup H).map H.subtype =
            H.subtype.range :=
          (MonoidHom.range_eq_map H.subtype).symm
        _ = H := Subgroup.range_subtype H
    have hmapEq :
        R.map H.subtype =
          (⊤ : Subgroup H).map H.subtype := by
      simpa only [S, hmapTop]
        using hSH
    exact hRneTop
      ((Subgroup.map_injective
        H.subtype_injective) hmapEq)
  have hSnormal : S.Normal := by
    refine
      { conj_mem := ?_ }
    intro s hs g
    obtain ⟨r, hrR, rfl⟩ :=
      Subgroup.mem_map.mp hs
    obtain ⟨w, rfl⟩ :=
      MonoidHom.mem_range.mp hrR
    let w' : H :=
      ⟨g * (w : G) * g⁻¹,
        (inferInstance : H.Normal).conj_mem
          (w : G) w.2 g⟩
    apply Subgroup.mem_map.mpr
    refine
      ⟨w' ^ 2,
        MonoidHom.mem_range.mpr ⟨w', rfl⟩,
        ?_⟩
    change (w' : G) ^ 2 =
      g * ((w : G) ^ 2) * g⁻¹
    dsimp only [w']
    simp only [pow_two]
    group
  have hexists :
      ∃ x : G, x ^ 2 ∉ S := by
    by_contra hall
    push Not at hall
    have hclosureLe : primePowerNormalClosure 2 G ≤ S := by
      apply Subgroup.normalClosure_le_normal
      rintro _ ⟨x, rfl⟩
      exact hall x
    apply hSneH
    apply le_antisymm
    · exact Subgroup.map_subtype_le R
    · rw [← hclosure]
      exact hclosureLe
  obtain ⟨x, hxNotS⟩ := hexists
  have hxSqH : x ^ 2 ∈ H := by
    rw [← hclosure]
    exact
      Subgroup.subset_normalClosure ⟨x, rfl⟩
  let z : H := ⟨x ^ 2, hxSqH⟩
  have hzNotR : z ∉ R := by
    intro hzR
    exact hxNotS
      (Subgroup.mem_map.mpr
        ⟨z, hzR, rfl⟩)
  have hPhiH : frattini H = R := by
    calc
      frattini H =
          primePowerNormalClosure 2 H :=
        frattini_eq_primePowerNormalClosure_two hH2
      _ = R := by
        simpa only [R] using
          primePowerNormalClosure_two_eq_powMonoidHom_range H
  let K : Subgroup H := Subgroup.zpowers z
  let L : Subgroup H := K ⊔ R
  have hRL : R < L := by
    refine lt_of_le_not_ge le_sup_right ?_
    intro hLR
    exact hzNotR
      (hLR
        ((show K ≤ L from le_sup_left)
          (Subgroup.mem_zpowers z)))
  have hRcardMul :
      Nat.card R * 2 = Nat.card H := by
    simpa only [hRindex] using R.card_mul_index
  have hRcardLtL :
      Nat.card R < Nat.card L := by
    have hle :
        Nat.card R ≤ Nat.card L :=
      Subgroup.card_le_of_le hRL.le
    have hne : Nat.card R ≠ Nat.card L := by
      intro hcard
      exact hRL.ne
        (Subgroup.eq_of_le_of_card_ge hRL.le
          (by omega))
    omega
  have hRcardDvdL :
      Nat.card R ∣ Nat.card L :=
    Subgroup.card_dvd_of_le hRL.le
  obtain ⟨k, hk⟩ := hRcardDvdL
  have hLcardLeH :
      Nat.card L ≤ Nat.card H := by
    calc
      Nat.card L ≤ Nat.card (⊤ : Subgroup H) :=
        Subgroup.card_le_of_le
          (show L ≤ (⊤ : Subgroup H) from le_top)
      _ = Nat.card H := Subgroup.card_top
  have hkEq : k = 2 := by
    have hRcardPos : 0 < Nat.card R :=
      Nat.card_pos
    nlinarith
  have hLtop : L = ⊤ := by
    apply Subgroup.eq_of_le_of_card_ge
      (show L ≤ (⊤ : Subgroup H) from le_top)
    rw [Subgroup.card_top, ← hRcardMul, hk, hkEq]
  have hKtop : K = ⊤ := by
    apply frattini_nongenerating
    rw [hPhiH]
    exact hLtop
  refine ⟨x, ?_⟩
  calc
    Subgroup.zpowers (x ^ 2) =
        K.map H.subtype := by
      simpa only [K, z] using
        (MonoidHom.map_zpowers H.subtype z).symm
    _ = (⊤ : Subgroup H).map H.subtype := by
      rw [hKtop]
    _ = H.subtype.range :=
      (MonoidHom.range_eq_map H.subtype).symm
    _ = H := Subgroup.range_subtype H

end LisiSabatini
