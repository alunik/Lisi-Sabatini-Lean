module

public import LisiSabatini.HallBergerSquareImageGenerator

/-!
# The cyclic-head seed in the remaining Hall--Berger branch

Assume the Frattini subgroup is the square image of the cyclic center of
its centralizer and that the centralizer is proper.  A generator `g` of
that center and any element `h` outside the centralizer satisfy the exact
relations used by Berger--Kovács--Newman:

* `⟨g⟩` is a normal cyclic subgroup;
* `Φ(G) = ⟨g²⟩`;
* `h² ∈ ⟨g²⟩`;
* `h` does not commute with `g²`.

This file packages those relations independently of the later
classification of finite `2`-groups with a cyclic maximal subgroup.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The exact generator-and-coset data entering the cyclic maximal
subgroup classification in the large square-image branch. -/
structure HallBergerCyclicHeadSeed
    (G : Type u) [Group G] [Finite G] where
  rotation : G
  coset : G
  rotation_normal :
    (Subgroup.zpowers rotation).Normal
  rotation_order_ge_eight :
    8 ≤ orderOf rotation
  rotation_generates_centerImage :
    Subgroup.zpowers rotation =
      characteristicCenterImage
        (frattiniCentralizer G)
  frattini_eq_rotationSquare :
    frattini G =
      Subgroup.zpowers (rotation ^ 2)
  coset_not_mem_frattiniCentralizer :
    coset ∉ frattiniCentralizer G
  cosetSquare_mem_rotationSquare :
    coset ^ 2 ∈
      Subgroup.zpowers (rotation ^ 2)
  rotationSquare_not_commute :
    ¬ Commute (rotation ^ 2) coset

/-- A chosen generator of the intrinsic center maps to a generator of
the ambient center image. -/
theorem zpowers_centerGenerator_coe_eq_characteristicCenterImage
    {G : Type u} [Group G]
    (g :
      Subgroup.center (frattiniCentralizer G))
    (hg : Subgroup.zpowers g = ⊤) :
    Subgroup.zpowers
        (((g : frattiniCentralizer G) : G)) =
      characteristicCenterImage
        (frattiniCentralizer G) := by
  let C : Subgroup G :=
    frattiniCentralizer G
  let Z : Subgroup C :=
    Subgroup.center C
  let ι : Z →* G :=
    C.subtype.comp Z.subtype
  change Subgroup.zpowers (ι g) =
    (Subgroup.center C).map C.subtype
  calc
    Subgroup.zpowers (ι g) =
        (Subgroup.zpowers g).map ι :=
      (MonoidHom.map_zpowers ι g).symm
    _ = (⊤ : Subgroup Z).map ι := by
      rw [hg]
    _ = ι.range :=
      (MonoidHom.range_eq_map ι).symm
    _ = (Subgroup.center C).map C.subtype := by
      ext x
      constructor
      · rintro ⟨z, rfl⟩
        exact Subgroup.mem_map.mpr
          ⟨(z : C), z.2, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact
          ⟨(⟨z, hz⟩ : Z), rfl⟩

/-- In the proper-centralizer large square-image branch, the exact
cyclic-head seed exists. -/
theorem exists_hallBergerCyclicHeadSeed_of_squareImage_of_ne_top
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hSquare :
      frattini G =
        frattiniCentralizerCenterSquareImage G)
    (hPhiLarge : 2 < Nat.card (frattini G))
    (hCneTop :
      frattiniCentralizer G ≠ ⊤) :
    Nonempty (HallBergerCyclicHeadSeed G) := by
  classical
  obtain ⟨g, hgGenerator, hPhiGenerator⟩ :=
    exists_frattiniCentralizer_center_generator_with_frattini_eq_zpowers_sq
      hG2 hBKN hSquare
  let a : G :=
    ((g : frattiniCentralizer G) : G)
  have haCenterImage :
      Subgroup.zpowers a =
        characteristicCenterImage
          (frattiniCentralizer G) := by
    simpa only [a] using
      zpowers_centerGenerator_coe_eq_characteristicCenterImage
        g hgGenerator
  have hCenterImageCharacteristic :
      (characteristicCenterImage
        (frattiniCentralizer G)).Characteristic :=
    characteristicCenterImage_characteristic
      (frattiniCentralizer G)
  letI :
      (characteristicCenterImage
        (frattiniCentralizer G)).Characteristic :=
    hCenterImageCharacteristic
  have haNormal :
      (Subgroup.zpowers a).Normal := by
    rw [haCenterImage]
    infer_instance
  have hCenterCard :
      8 ≤ Nat.card
        (Subgroup.center
          (frattiniCentralizer G)) :=
    eight_le_natCard_frattiniCentralizer_center_of_two_lt_natCard_frattini
      hG2 hBKN hSquare hPhiLarge
  let eZ :
      Subgroup.center (frattiniCentralizer G) ≃*
        characteristicCenterImage
          (frattiniCentralizer G) :=
    Subgroup.equivMapOfInjective
      (Subgroup.center (frattiniCentralizer G))
      (frattiniCentralizer G).subtype
      Subtype.coe_injective
  have hcardCenterImage :
      Nat.card
          (characteristicCenterImage
            (frattiniCentralizer G)) =
        Nat.card
          (Subgroup.center
            (frattiniCentralizer G)) :=
    (Nat.card_congr eZ.toEquiv).symm
  have haOrder :
      orderOf a =
        Nat.card
          (Subgroup.center
            (frattiniCentralizer G)) := by
    calc
      orderOf a =
          Nat.card (Subgroup.zpowers a) :=
        by rw [Nat.card_zpowers]
      _ = Nat.card
            (characteristicCenterImage
              (frattiniCentralizer G)) := by
        rw [haCenterImage]
      _ = Nat.card
            (Subgroup.center
              (frattiniCentralizer G)) :=
        hcardCenterImage
  have haOrderLarge : 8 ≤ orderOf a := by
    rw [haOrder]
    exact hCenterCard
  have hexistsOutside :
      ∃ h : G,
        h ∉ frattiniCentralizer G := by
    by_contra hnone
    push Not at hnone
    apply hCneTop
    rw [Subgroup.eq_top_iff']
    exact hnone
  obtain ⟨h, hhOutside⟩ :=
    hexistsOutside
  have hhSqPhi : h ^ 2 ∈ frattini G :=
    pow_prime_mem_frattini_of_isPGroup
      Nat.prime_two hG2 h
  have hhSqRotation :
      h ^ 2 ∈ Subgroup.zpowers (a ^ 2) := by
    rw [← hPhiGenerator]
    exact hhSqPhi
  have hnoncommute :
      ¬ Commute (a ^ 2) h := by
    intro hcommute
    apply hhOutside
    change h ∈
      Subgroup.centralizer
        (frattini G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hyPhi
    have hyPowers :
        y ∈ Subgroup.zpowers (a ^ 2) := by
      rw [← hPhiGenerator]
      exact hyPhi
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.mp hyPowers
    rw [← hn]
    exact hcommute.zpow_left n
  exact
    ⟨{
      rotation := a
      coset := h
      rotation_normal := haNormal
      rotation_order_ge_eight := haOrderLarge
      rotation_generates_centerImage :=
        haCenterImage
      frattini_eq_rotationSquare := by
        simpa only [a] using hPhiGenerator
      coset_not_mem_frattiniCentralizer :=
        hhOutside
      cosetSquare_mem_rotationSquare :=
        hhSqRotation
      rotationSquare_not_commute :=
        hnoncommute
    }⟩

end LisiSabatini
