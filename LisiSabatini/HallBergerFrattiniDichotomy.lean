module

public import LisiSabatini.HallBergerFrattiniCentralizerDecomposition
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The two Frattini positions in the Hall--Berger proof

Let `C = C_G(Φ(G))`.  The published omega-one hypothesis makes `Z(C)`
cyclic.  The Frattini subgroup lies in `Z(C)`, while every square from
`Z(C)` lies in the Frattini subgroup.  Since the subgroup of squares in a
finite cyclic `2`-group has index at most two, there is no intermediate
possibility.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The ambient image of the subgroup of squares in the center of the
Frattini centralizer. -/
def frattiniCentralizerCenterSquareImage
    (G : Type u) [Group G] : Subgroup G :=
  let C : Subgroup G := frattiniCentralizer G
  let Z : Subgroup C := Subgroup.center C
  ((powMonoidHom 2 : Z →* Z).range).map
    (C.subtype.comp Z.subtype)

/-- Under the exact Hall--Berger source hypothesis, the Frattini subgroup
is either the whole ambient image of `Z(C_G(Φ(G)))` or exactly the
ambient image of its square subgroup. -/
theorem frattini_eq_centerImage_or_centerSquareImage
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G) :
    frattini G =
        characteristicCenterImage (frattiniCentralizer G) ∨
      frattini G =
        frattiniCentralizerCenterSquareImage G := by
  classical
  let C : Subgroup G := frattiniCentralizer G
  let Z : Subgroup C := Subgroup.center C
  let ι : Z →* G := C.subtype.comp Z.subtype
  let R : Subgroup Z :=
    (powMonoidHom 2 : Z →* Z).range
  let A : Subgroup Z :=
    (frattini G).comap ι
  have hZcyclic : IsCyclic Z :=
    frattiniCentralizer_center_isCyclic
      Nat.prime_two hG2 hBKN
  letI : IsCyclic Z := hZcyclic
  have hRA : R ≤ A := by
    intro z hz
    obtain ⟨w, rfl⟩ :=
      MonoidHom.mem_range.mp hz
    change ι (w ^ 2) ∈ frattini G
    rw [map_pow]
    exact
      pow_prime_mem_frattini_of_isPGroup
        Nat.prime_two hG2 (ι w)
  have hRindex : R.index ≤ 2 := by
    calc
      R.index = (Nat.card Z).gcd 2 := by
        simpa only [R] using
          (IsCyclic.index_powMonoidHom_range Z 2)
      _ ≤ 2 :=
        Nat.gcd_le_right (Nat.card Z) (by norm_num)
  have hRcardPos : 0 < Nat.card R :=
    Nat.card_pos
  have hZcardLe :
      Nat.card Z ≤ 2 * Nat.card R := by
    have hcard :=
      R.card_mul_index
    nlinarith
  have hRcardDvdA :
      Nat.card R ∣ Nat.card A :=
    Subgroup.card_dvd_of_le hRA
  obtain ⟨k, hk⟩ := hRcardDvdA
  have hkPos : 0 < k := by
    have hAcardPos : 0 < Nat.card A :=
      Nat.card_pos
    nlinarith
  have hAcardLeZ :
      Nat.card A ≤ Nat.card Z :=
    calc
      Nat.card A ≤ Nat.card (⊤ : Subgroup Z) :=
        Subgroup.card_le_of_le
          (show A ≤ (⊤ : Subgroup Z) from le_top)
      _ = Nat.card Z := Subgroup.card_top
  have hkLe : k ≤ 2 := by
    nlinarith
  have hAeqRorTop : A = R ∨ A = ⊤ := by
    interval_cases k
    · left
      exact
        (Subgroup.eq_of_le_of_card_ge hRA
          (by omega)).symm
    · right
      apply Subgroup.eq_of_le_of_card_ge
        (show A ≤ (⊤ : Subgroup Z) from le_top)
      rw [Subgroup.card_top]
      nlinarith
  have hPhiLeCenterImage :
      frattini G ≤ characteristicCenterImage C :=
    frattini_le_frattiniCentralizer_centerImage
      Nat.prime_two hG2 hBKN
  rcases hAeqRorTop with hAR | hAtop
  · right
    apply le_antisymm
    · intro x hx
      obtain ⟨zC, hzCenter, hzEq⟩ :=
        Subgroup.mem_map.mp
          (hPhiLeCenterImage hx)
      change (zC : G) = x at hzEq
      let z : Z := ⟨zC, hzCenter⟩
      have hzA : z ∈ A := by
        change ι z ∈ frattini G
        change ((zC : C) : G) ∈ frattini G
        rw [hzEq]
        exact hx
      have hzR : z ∈ R := by
        rw [← hAR]
        exact hzA
      change x ∈ R.map ι
      exact Subgroup.mem_map.mpr
        ⟨z, hzR, by simpa only [ι, z] using hzEq⟩
    · intro x hx
      change x ∈ R.map ι at hx
      obtain ⟨z, hzR, rfl⟩ :=
        Subgroup.mem_map.mp hx
      exact hRA hzR
  · left
    apply le_antisymm hPhiLeCenterImage
    intro x hx
    obtain ⟨zC, hzCenter, hzEq⟩ :=
      Subgroup.mem_map.mp hx
    change (zC : G) = x at hzEq
    let z : Z := ⟨zC, hzCenter⟩
    have hzA : z ∈ A := by
      rw [hAtop]
      exact Subgroup.mem_top z
    change ι z ∈ frattini G at hzA
    change ((zC : C) : G) ∈ frattini G at hzA
    rw [hzEq] at hzA
    exact hzA

end LisiSabatini
