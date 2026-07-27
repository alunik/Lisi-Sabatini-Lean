import LisiSabatini.HallBergerCenterSquareObstruction
import LisiSabatini.HallBergerSquareGenerator

/-!
# Eliminating the first large-Frattini Hall--Berger branch

Let `C = C_G(Φ(G))`.  If the first branch of the Hall--Berger
dichotomy held, then `Φ(G)` would be the ambient image of `Z(C)`.
Because `Φ(G)` is the normal closure of the squares, one ambient square
would generate this cyclic subgroup.  Its square root necessarily lies
in `C`, however, and the intrinsic square obstruction shows that such a
square cannot generate `Z(C)` when that center has order greater than
two.

Consequently the first branch is confined to `|Φ(G)| ≤ 2`; every
large-Frattini case lies in the square-image branch.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- In a Hall--Berger Frattini centralizer with center of order greater
than two, no square generates the center. -/
theorem frattiniCentralizer_zpowers_square_ne_center_of_center_card_gt_two
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hCenterLarge :
      2 < Nat.card
        (Subgroup.center (frattiniCentralizer G)))
    (x : frattiniCentralizer G) :
    Subgroup.zpowers (x ^ 2) ≠
      Subgroup.center (frattiniCentralizer G) := by
  classical
  let C : Subgroup G :=
    frattiniCentralizer G
  let Z : Subgroup C :=
    Subgroup.center C
  have hC2 : IsPGroup 2 C :=
    hG2.to_subgroup C
  have hZcyclic : IsCyclic Z :=
    frattiniCentralizer_center_isCyclic
      Nat.prime_two hG2 hBKN
  have hCenterLargeC :
      2 < Nat.card (Subgroup.center C) := by
    simpa only [C] using hCenterLarge
  by_cases hCcomm : IsMulCommutative C
  · let groupC : Group C := inferInstance
    letI : CommGroup C :=
      { groupC with mul_comm := hCcomm.1.1 }
    have hZtop : Subgroup.center C = ⊤ :=
      CommGroup.center_eq_top
    have hCcyclic : IsCyclic C := by
      have h : IsCyclic (Subgroup.center C) := by
        simpa only [Z] using hZcyclic
      rw [hZtop] at h
      exact Subgroup.topEquiv.isCyclic.mp h
    have hClarge : 2 < Nat.card C := by
      simpa only [hZtop, Subgroup.card_top] using hCenterLargeC
    have hne :
        Subgroup.zpowers (x ^ 2) ≠ ⊤ :=
      zpowers_square_ne_top_of_cyclic_two_group
        hC2 hCcyclic (by omega) x
    intro hgen
    apply hne
    exact hgen.trans hZtop
  · have hC :
        HasCentralCommutatorOfOrderTwo C :=
      frattiniCentralizer_hasCentralCommutatorOfOrderTwo
        hG2 hBKN hCcomm
    have hOmegaCenter :
        IsCyclic
          (Subgroup.center (omegaOneSubgroup 2 C)) := by
      simpa only [C] using hBKN
    obtain
      ⟨E, hE, hFactor, hResidualCyclic⟩ :=
        exists_internal_extraspecial_factor_with_cyclic_residual_of_centralCommutator
          hC2 hC hOmegaCenter
    intro hgen
    have hgenZ :
        Subgroup.zpowers (x ^ 2) = Z := by
      simpa only [Z, C] using hgen
    have hxCenter : x ^ 2 ∈ Z := by
      rw [← hgenZ]
      exact Subgroup.mem_zpowers (x ^ 2)
    have hxSquareImage :
        x ^ 2 ∈
          ((powMonoidHom 2 : Z →* Z).range).map
            Z.subtype :=
      square_mem_centerSquareImage_of_internal_extraspecial_cyclic_factor
        hC2 hC E hE hFactor hResidualCyclic
          hCenterLargeC hxCenter
    let R : Subgroup Z :=
      (powMonoidHom 2 : Z →* Z).range
    let S : Subgroup C :=
      R.map Z.subtype
    have hzpowersLe :
        Subgroup.zpowers (x ^ 2) ≤ S :=
      Subgroup.zpowers_le_of_mem hxSquareImage
    have hZleS : Z ≤ S := by
      rw [← hgenZ]
      exact hzpowersLe
    have hSleZ : S ≤ Z :=
      Subgroup.map_subtype_le R
    have hSeqZ : S = Z :=
      le_antisymm hSleZ hZleS
    have hRneTop : R ≠ ⊤ := by
      have hZlarge : 2 < Nat.card Z := by
        simpa only [Z] using hCenterLargeC
      simpa only [R] using
        powMonoidHom_two_range_ne_top_of_cyclic_two_group
          (hC2.to_subgroup Z) hZcyclic (by omega)
    have hmapTop :
        (⊤ : Subgroup Z).map Z.subtype = Z := by
      calc
        (⊤ : Subgroup Z).map Z.subtype =
            Z.subtype.range :=
          (MonoidHom.range_eq_map Z.subtype).symm
        _ = Z := Subgroup.range_subtype Z
    have hmapEq :
        R.map Z.subtype =
          (⊤ : Subgroup Z).map Z.subtype := by
      calc
        R.map Z.subtype = S := rfl
        _ = Z := hSeqZ
        _ = (⊤ : Subgroup Z).map Z.subtype :=
          hmapTop.symm
    exact hRneTop
      ((Subgroup.map_injective
        Z.subtype_injective) hmapEq)

/-- If the Frattini subgroup occupies the whole center-image branch,
then it has at most two elements. -/
theorem natCard_frattini_le_two_of_eq_frattiniCentralizer_centerImage
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hPhi :
      frattini G =
        characteristicCenterImage (frattiniCentralizer G)) :
    Nat.card (frattini G) ≤ 2 := by
  classical
  by_contra hPhiNotSmall
  have hPhiLarge : 2 < Nat.card (frattini G) := by
    omega
  have hPhiCyclic : IsCyclic (frattini G) :=
    frattini_isCyclic_of_omegaOne_frattiniCentralizer_center_isCyclic
      Nat.prime_two hG2 hBKN
  have hclosure :
      primePowerNormalClosure 2 G = frattini G :=
    (frattini_eq_primePowerNormalClosure_two hG2).symm
  obtain ⟨x, hxGenerator⟩ :=
    exists_square_generator_of_primePowerNormalClosure_eq_cyclic
      (frattini G)
      (hG2.to_subgroup (frattini G))
      hPhiCyclic (by omega) hclosure
  let C : Subgroup G :=
    frattiniCentralizer G
  have hxC : x ∈ C := by
    change x ∈
      Subgroup.centralizer (frattini G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hyPhi
    have hySquarePowers :
        y ∈ Subgroup.zpowers (x ^ 2) := by
      rw [hxGenerator]
      exact hyPhi
    have hSquarePowersLe :
        Subgroup.zpowers (x ^ 2) ≤
          Subgroup.zpowers x :=
      Subgroup.zpowers_le_of_mem
        (Subgroup.npow_mem_zpowers x 2)
    have hyPowers :
        y ∈ Subgroup.zpowers x :=
      hSquarePowersLe hySquarePowers
    exact congrArg Subtype.val
      ((inferInstance :
          IsMulCommutative (Subgroup.zpowers x)).1.1
        (⟨y, hyPowers⟩ : Subgroup.zpowers x)
        (⟨x, Subgroup.mem_zpowers x⟩ :
          Subgroup.zpowers x))
  let xC : C := ⟨x, hxC⟩
  have hxGeneratorC :
      Subgroup.zpowers (xC ^ 2) =
        Subgroup.center C := by
    apply
      (Subgroup.map_injective
        C.subtype_injective)
    calc
      (Subgroup.zpowers (xC ^ 2)).map C.subtype =
          Subgroup.zpowers (C.subtype (xC ^ 2)) :=
        MonoidHom.map_zpowers C.subtype (xC ^ 2)
      _ = Subgroup.zpowers (x ^ 2) := rfl
      _ = frattini G := hxGenerator
      _ = characteristicCenterImage C := hPhi
      _ = (Subgroup.center C).map C.subtype := rfl
  let eZ :
      Subgroup.center C ≃*
        characteristicCenterImage C :=
    Subgroup.equivMapOfInjective
      (Subgroup.center C) C.subtype
      Subtype.coe_injective
  have hcardCenterImage :
      Nat.card (characteristicCenterImage C) =
        Nat.card (Subgroup.center C) :=
    (Nat.card_congr eZ.toEquiv).symm
  have hCenterLarge :
      2 < Nat.card (Subgroup.center C) := by
    calc
      2 < Nat.card (characteristicCenterImage C) := by
        rw [← hPhi]
        exact hPhiLarge
      _ = Nat.card (Subgroup.center C) :=
        hcardCenterImage
  exact
    (frattiniCentralizer_zpowers_square_ne_center_of_center_card_gt_two
      hG2 hBKN hCenterLarge xC)
      hxGeneratorC

/-- Every Hall--Berger case with more than two Frattini elements lies
in the square-image branch of the dichotomy. -/
theorem frattini_eq_frattiniCentralizerCenterSquareImage_of_two_lt_natCard
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hPhiLarge : 2 < Nat.card (frattini G)) :
    frattini G =
      frattiniCentralizerCenterSquareImage G := by
  rcases
      frattini_eq_centerImage_or_centerSquareImage
        hG2 hBKN with hCenter | hSquare
  · have hsmall :=
      natCard_frattini_le_two_of_eq_frattiniCentralizer_centerImage
        hG2 hBKN hCenter
    omega
  · exact hSquare

end LisiSabatini
