import LisiSabatini.HallBergerDihedralFactor
import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Enlarging the extraspecial factor in the Hall--Berger argument

The maximality step in Berger--Kovács--Newman repeatedly uses the
following elementary fact.  Inside a group whose derived subgroup is
central of order two, every extraspecial subgroup has the *same* central
involution: its center, mapped into the ambient group, is the full ambient
derived subgroup.  Consequently two commuting extraspecial factors have
an extraspecial central product.

This file proves those statements intrinsically for subgroups.  They are
the group-theoretic mechanism behind the contradiction to the maximal
choice of the product of dihedral factors in the published proof.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The two nonidentity elements selected from the ambient derived
subgroup coincide; equivalently, their product is one. -/
theorem mul_eq_one_of_mem_commutator_of_ne_one
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    {a b : D}
    (ha : a ∈ commutator D) (hb : b ∈ commutator D)
    (haNe : a ≠ 1) (hbNe : b ≠ 1) :
    a * b = 1 := by
  let a' : commutator D := ⟨a, ha⟩
  let b' : commutator D := ⟨b, hb⟩
  obtain ⟨z, hzNe, hzUnique⟩ :=
    (Nat.card_eq_two_iff' (1 : commutator D)).mp
      hD.card_commutator
  have ha'Ne : a' ≠ 1 := by
    intro ha'
    exact haNe (congrArg Subtype.val ha')
  have hb'Ne : b' ≠ 1 := by
    intro hb'
    exact hbNe (congrArg Subtype.val hb')
  have ha' : a' = z := hzUnique a' ha'Ne
  have hb' : b' = z := hzUnique b' hb'Ne
  have hzSq : z ^ 2 = 1 := by
    have hpow :
        z ^ Nat.card (commutator D) = 1 :=
      pow_card_eq_one'
    simpa [hD.card_commutator] using hpow
  change (a' : D) * (b' : D) = 1
  rw [ha', hb']
  simpa only [pow_two, Subgroup.coe_mul,
    Subgroup.coe_one] using congrArg Subtype.val hzSq

/-- In an ambient group with central derived subgroup of order two, the
center of every extraspecial subgroup maps onto that ambient derived
subgroup. -/
theorem characteristicCenterImage_eq_commutator_of_extraspecial
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    (E : Subgroup D) (hE : IsExtraspecial 2 E) :
    characteristicCenterImage E = commutator D := by
  have hle :
      characteristicCenterImage E ≤ commutator D := by
    unfold characteristicCenterImage
    rw [← hE.commutator_eq_center,
      Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hcardImage :
      Nat.card (characteristicCenterImage E) = 2 := by
    let e :
        Subgroup.center E ≃*
          characteristicCenterImage E :=
      Subgroup.equivMapOfInjective
        (Subgroup.center E) E.subtype
        Subtype.coe_injective
    calc
      Nat.card (characteristicCenterImage E) =
          Nat.card (Subgroup.center E) :=
        (Nat.card_congr e.toEquiv).symm
      _ = 2 := hE.card_center
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [hD.card_commutator, hcardImage]

/-- Every noncommutative subgroup of a group with central derived
subgroup of order two has the same intrinsic central-commutator
property. -/
theorem HasCentralCommutatorOfOrderTwo.of_noncommutative_subgroup
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    (H : Subgroup D)
    (hnoncomm : ¬ IsMulCommutative H) :
    HasCentralCommutatorOfOrderTwo H := by
  have hmapLe :
      (commutator H).map H.subtype ≤
        commutator D := by
    rw [Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hclass :
      commutator H ≤ Subgroup.center H := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subtype.ext
    have hcAmbient :
        (c : D) ∈ commutator D :=
      hmapLe (Subgroup.mem_map.mpr ⟨c, hc, rfl⟩)
    exact
      Subgroup.mem_center_iff.mp
        (hD.commutator_le_center hcAmbient) h
  have hcommNe : commutator H ≠ ⊥ := by
    intro hbot
    have hcenterTop :
        Subgroup.center H = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top H).mp
        hbot
    apply hnoncomm
    exact
      ⟨⟨fun x y =>
        Subgroup.mem_center_iff.mp
          (show y ∈ Subgroup.center H by
            rw [hcenterTop]
            exact Subgroup.mem_top y) x⟩⟩
  have hcardMap :
      Nat.card ((commutator H).map H.subtype) =
        Nat.card (commutator H) := by
    let e :
        commutator H ≃*
          (commutator H).map H.subtype :=
      Subgroup.equivMapOfInjective
        (commutator H) H.subtype
        Subtype.coe_injective
    exact (Nat.card_congr e.toEquiv).symm
  have hcardLe :
      Nat.card (commutator H) ≤ 2 := by
    have hle :=
      Subgroup.card_le_of_le hmapLe
    rw [hD.card_commutator, hcardMap] at hle
    exact hle
  have hcardGt :
      1 < Nat.card (commutator H) :=
    (commutator H).one_lt_card_iff_ne_bot.mpr
      hcommNe
  exact
    { commutator_le_center := hclass
      card_commutator := by omega }

/-- Squares are central in every group whose derived subgroup is central
of order two. -/
theorem HasCentralCommutatorOfOrderTwo.sq_mem_center
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    (x : D) :
    x ^ 2 ∈ Subgroup.center D := by
  apply pow_mem_center_of_commutator_le_center
    hD.commutator_le_center 2
  intro c
  have hpow :
      c ^ Nat.card (commutator D) = 1 :=
    pow_card_eq_one'
  simpa [hD.card_commutator] using
    congrArg Subtype.val hpow

/-- A finite `2`-group with central derived subgroup of order two and
center of order two is extraspecial. -/
theorem HasCentralCommutatorOfOrderTwo.isExtraspecial_of_card_center
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    (hD2 : IsPGroup 2 D)
    (hCenter : Nat.card (Subgroup.center D) = 2) :
    IsExtraspecial 2 D := by
  exact
    { prime := Nat.prime_two
      pGroup := hD2
      commutator_eq_center := by
        apply Subgroup.eq_of_le_of_card_ge
          hD.commutator_le_center
        rw [hCenter, hD.card_commutator]
      card_center := hCenter }

/-- Extraspeciality is invariant under a group isomorphism. -/
theorem IsExtraspecial.of_mulEquiv
    {p : ℕ} {G H : Type u}
    [Group G] [Finite G] [Group H] [Finite H]
    (hG : IsExtraspecial p G) (e : G ≃* H) :
    IsExtraspecial p H := by
  have hmapCommutator :
      (commutator G).map e.toMonoidHom =
        commutator H := by
    rw [map_commutator_eq,
      e.toMonoidHom.range_eq_top_of_surjective
        e.surjective]
    rfl
  have hclass :
      commutator H ≤ Subgroup.center H := by
    intro c hc
    have hcG :
        e.symm c ∈ commutator G := by
      have hm :
          e (e.symm c) ∈ commutator H := by
        simpa using hc
      rw [← hmapCommutator,
        Subgroup.mem_map_equiv] at hm
      simpa using hm
    have hcCenter :
        e.symm c ∈ Subgroup.center G := by
      rw [← hG.commutator_eq_center]
      exact hcG
    rw [Subgroup.mem_center_iff]
    intro y
    apply e.symm.injective
    simpa using
      (Subgroup.mem_center_iff.mp hcCenter
        (e.symm y))
  let eCommutator :
      commutator G ≃* commutator H :=
    (Subgroup.equivMapOfInjective
      (commutator G) e.toMonoidHom
      e.injective).trans
        (MulEquiv.subgroupCongr hmapCommutator)
  have hcardCommutator :
      Nat.card (commutator H) = p := by
    calc
      Nat.card (commutator H) =
          Nat.card (commutator G) :=
        (Nat.card_congr eCommutator.toEquiv).symm
      _ = Nat.card (Subgroup.center G) := by
        rw [hG.commutator_eq_center]
      _ = p := hG.card_center
  have hcardCenter :
      Nat.card (Subgroup.center H) = p := by
    calc
      Nat.card (Subgroup.center H) =
          Nat.card (Subgroup.center G) :=
        (Nat.card_congr
          (Subgroup.centerCongr e).toEquiv).symm
      _ = p := hG.card_center
  exact
    { prime := hG.prime
      pGroup := hG.pGroup.of_equiv e
      commutator_eq_center := by
        apply Subgroup.eq_of_le_of_card_ge hclass
        rw [hcardCenter, hcardCommutator]
      card_center := hcardCenter }

/-- A product normal form for the supremum of two elementwise commuting
subgroups. -/
theorem mem_sup_iff_of_elementwise_commute
    {D : Type u} [Group D]
    (E H : Subgroup D)
    (hcomm :
      ∀ (e : E) (h : H), (e : D) * h = h * e)
    {x : D} :
    x ∈ E ⊔ H ↔
      ∃ e ∈ E, ∃ h ∈ H, e * h = x := by
  constructor
  · rw [Subgroup.sup_eq_closure]
    intro hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro z (hz | hz)
      · exact ⟨z, hz, 1, H.one_mem, mul_one z⟩
      · exact ⟨1, E.one_mem, z, hz, one_mul z⟩
    · exact ⟨1, E.one_mem, 1, H.one_mem, mul_one 1⟩
    · rintro _ _ _ _ ⟨e₁, he₁, h₁, hh₁, rfl⟩
        ⟨e₂, he₂, h₂, hh₂, rfl⟩
      refine
        ⟨e₁ * e₂, E.mul_mem he₁ he₂,
          h₁ * h₂, H.mul_mem hh₁ hh₂, ?_⟩
      have hswap :
          e₂ * h₁ = h₁ * e₂ :=
        hcomm ⟨e₂, he₂⟩ ⟨h₁, hh₁⟩
      calc
        (e₁ * e₂) * (h₁ * h₂) =
            e₁ * (e₂ * h₁) * h₂ := by
          simp only [mul_assoc]
        _ = e₁ * (h₁ * e₂) * h₂ := by rw [hswap]
        _ = (e₁ * h₁) * (e₂ * h₂) := by
          simp only [mul_assoc]
    · rintro _ _ ⟨e, he, h, hh, rfl⟩
      refine
        ⟨e⁻¹, E.inv_mem he, h⁻¹, H.inv_mem hh, ?_⟩
      have hswap :
          e⁻¹ * h⁻¹ = h⁻¹ * e⁻¹ :=
        hcomm ⟨e⁻¹, E.inv_mem he⟩
          ⟨h⁻¹, H.inv_mem hh⟩
      rw [mul_inv_rev]
      exact hswap
  · rintro ⟨e, he, h, hh, rfl⟩
    exact Subgroup.mul_mem_sup he hh

/-- Two commuting extraspecial subgroups have an extraspecial central
product, provided the ambient derived subgroup is central of order two.

The ambient hypothesis forces the two factor centers to be the same
subgroup.  The proof then identifies both the center and the derived
subgroup of the join with that common subgroup. -/
theorem isExtraspecial_sup_of_elementwise_commute
    {D : Type u} [Group D] [Finite D]
    (hD2 : IsPGroup 2 D)
    (hD : HasCentralCommutatorOfOrderTwo D)
    (E H : Subgroup D)
    (hE : IsExtraspecial 2 E)
    (hH : IsExtraspecial 2 H)
    (hcomm :
      ∀ (e : E) (h : H), (e : D) * h = h * e) :
    IsExtraspecial 2 ↥(E ⊔ H) := by
  let K : Subgroup D := E ⊔ H
  let Z : Subgroup D := commutator D
  have hZE :
      characteristicCenterImage E = Z :=
    characteristicCenterImage_eq_commutator_of_extraspecial
      hD E hE
  have hZH :
      characteristicCenterImage H = Z :=
    characteristicCenterImage_eq_commutator_of_extraspecial
      hD H hH
  have hZleE : Z ≤ E := by
    rw [← hZE,
      characteristicCenterImage_eq_inf_centralizer]
    exact inf_le_left
  have hZleK : Z ≤ K :=
    hZleE.trans le_sup_left
  have hZcenter : Z ≤ Subgroup.center D :=
    hD.commutator_le_center
  have hcenterImageK :
      characteristicCenterImage K = Z := by
    rw [characteristicCenterImage_eq_inf_centralizer]
    apply le_antisymm
    · intro z hz
      obtain ⟨e, he, h, hh, hehz⟩ :=
        (mem_sup_iff_of_elementwise_commute
          E H hcomm).mp hz.1
      have heCenterImage :
          e ∈ characteristicCenterImage E := by
        rw [characteristicCenterImage_eq_inf_centralizer]
        refine ⟨he, ?_⟩
        change ∀ e' ∈ (E : Set D), e' * e = e * e'
        intro e' he'
        have hzComm :
            e' * z = z * e' :=
          hz.2 e' ((show E ≤ K from le_sup_left) he')
        have he'h :
            e' * h = h * e' :=
          hcomm ⟨e', he'⟩ ⟨h, hh⟩
        apply mul_right_cancel (b := h)
        calc
          (e' * e) * h = e' * (e * h) := by
            simp only [mul_assoc]
          _ = e' * z := by rw [hehz]
          _ = z * e' := hzComm
          _ = (e * h) * e' := by rw [hehz]
          _ = e * (h * e') := by
            simp only [mul_assoc]
          _ = e * (e' * h) := by rw [he'h]
          _ = (e * e') * h := by
            simp only [mul_assoc]
      have hhCenterImage :
          h ∈ characteristicCenterImage H := by
        rw [characteristicCenterImage_eq_inf_centralizer]
        refine ⟨hh, ?_⟩
        change ∀ h' ∈ (H : Set D), h' * h = h * h'
        intro h' hh'
        have hzComm :
            h' * z = z * h' :=
          hz.2 h' ((show H ≤ K from le_sup_right) hh')
        have heh' :
            e * h' = h' * e :=
          hcomm ⟨e, he⟩ ⟨h', hh'⟩
        apply mul_left_cancel (a := e)
        calc
          e * (h' * h) = (e * h') * h := by
            simp only [mul_assoc]
          _ = (h' * e) * h := by rw [heh']
          _ = h' * (e * h) := by
            simp only [mul_assoc]
          _ = h' * z := by rw [hehz]
          _ = z * h' := hzComm
          _ = (e * h) * h' := by rw [hehz]
          _ = e * (h * h') := by
            simp only [mul_assoc]
      rw [hZE] at heCenterImage
      rw [hZH] at hhCenterImage
      rw [← hehz]
      exact Z.mul_mem heCenterImage hhCenterImage
    · refine le_inf hZleK ?_
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact
        (Subgroup.mem_center_iff.mp
          (hZcenter hz) k)
  have hcommutatorImageK :
      (commutator K).map K.subtype = Z := by
    rw [Subgroup.map_subtype_commutator]
    apply le_antisymm
    · exact Subgroup.commutator_mono le_top le_top
    · have hEE :
          ⁅E, E⁆ = Z := by
        calc
          ⁅E, E⁆ =
              (commutator E).map E.subtype :=
            (Subgroup.map_subtype_commutator E).symm
          _ = (Subgroup.center E).map E.subtype := by
            rw [hE.commutator_eq_center]
          _ = characteristicCenterImage E := rfl
          _ = Z := hZE
      rw [← hEE]
      exact Subgroup.commutator_mono le_sup_left le_sup_left
  have hcommutatorEqCenter :
      commutator K = Subgroup.center K := by
    rw [← Subgroup.map_subtype_inj]
    calc
      (commutator K).map K.subtype = Z :=
        hcommutatorImageK
      _ = characteristicCenterImage K :=
        hcenterImageK.symm
      _ = (Subgroup.center K).map K.subtype := rfl
  have hcardCenterK :
      Nat.card (Subgroup.center K) = 2 := by
    let e :
        Subgroup.center K ≃*
          characteristicCenterImage K :=
      Subgroup.equivMapOfInjective
        (Subgroup.center K) K.subtype
        Subtype.coe_injective
    calc
      Nat.card (Subgroup.center K) =
          Nat.card (characteristicCenterImage K) :=
        Nat.card_congr e.toEquiv
      _ = Nat.card Z := by rw [hcenterImageK]
      _ = 2 := hD.card_commutator
  exact
    { prime := Nat.prime_two
      pGroup := hD2.to_subgroup K
      commutator_eq_center := hcommutatorEqCenter
      card_center := hcardCenterK }

end LisiSabatini
