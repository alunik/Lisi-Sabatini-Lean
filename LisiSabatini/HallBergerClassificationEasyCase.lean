module

public import LisiSabatini.HallBergerSourcePreliminaries

/-!
# The small-Frattini case of Hall--Berger

The Berger--Kovács--Newman proof first disposes of the case in which the
Frattini subgroup has order at most two.  In that case the Frattini
subgroup is central, so its centralizer is the whole group.  The group is
then either cyclic or already has the central-commutator structure used by
the affine counting argument.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- Central commutator of order two is invariant under a group
isomorphism. -/
theorem HasCentralCommutatorOfOrderTwo.of_mulEquiv
    {G H : Type u}
    [Group G] [Finite G] [Group H] [Finite H]
    (hG : HasCentralCommutatorOfOrderTwo G)
    (e : G ≃* H) :
    HasCentralCommutatorOfOrderTwo H := by
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
        e.symm c ∈ Subgroup.center G :=
      hG.commutator_le_center hcG
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
  exact
    { commutator_le_center := hclass
      card_commutator := by
        calc
          Nat.card (commutator H) =
              Nat.card (commutator G) :=
            (Nat.card_congr eCommutator.toEquiv).symm
          _ = 2 := hG.card_commutator }

/-- A normal subgroup of order at most two is central, specialized to the
characteristic Frattini subgroup. -/
theorem frattini_le_center_of_natCard_le_two
    {G : Type u} [Group G] [Finite G]
    (hcard : Nat.card (frattini G) ≤ 2) :
    frattini G ≤ Subgroup.center G := by
  classical
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro g
  by_cases hxOne : x = 1
  · simp [hxOne]
  have hPhiNeBot : frattini G ≠ ⊥ := by
    intro hbot
    have hxBot : x ∈ (⊥ : Subgroup G) := by
      simpa [hbot] using hx
    exact hxOne (by simpa using hxBot)
  have hcardEq : Nat.card (frattini G) = 2 := by
    have honeLt :
        1 < Nat.card (frattini G) :=
      (frattini G).one_lt_card_iff_ne_bot.mpr
        hPhiNeBot
    omega
  obtain ⟨z, hzNe, hzUnique⟩ :=
    (Nat.card_eq_two_iff'
      (1 : frattini G)).mp hcardEq
  let xPhi : frattini G := ⟨x, hx⟩
  have hxPhiNe : xPhi ≠ 1 := by
    intro h
    exact hxOne (congrArg Subtype.val h)
  have hconjMem :
      g * x * g⁻¹ ∈ frattini G :=
    (inferInstance : (frattini G).Normal).conj_mem
      x hx g
  let yPhi : frattini G :=
    ⟨g * x * g⁻¹, hconjMem⟩
  have hyPhiNe : yPhi ≠ 1 := by
    intro h
    have hconj : g * x * g⁻¹ = 1 :=
      congrArg Subtype.val h
    apply hxOne
    calc
      x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [hconj]; simp
  have hxy : xPhi = yPhi :=
    (hzUnique xPhi hxPhiNe).trans
      (hzUnique yPhi hyPhiNe).symm
  have hconj : g * x * g⁻¹ = x := by
    exact (congrArg Subtype.val hxy).symm
  calc
    g * x = (g * x * g⁻¹) * g := by group
    _ = x * g := by rw [hconj]

/-- If the Frattini subgroup has order at most two, its centralizer is
the whole group. -/
theorem frattiniCentralizer_eq_top_of_natCard_frattini_le_two
    {G : Type u} [Group G] [Finite G]
    (hcard : Nat.card (frattini G) ≤ 2) :
    frattiniCentralizer G = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  change g ∈ Subgroup.centralizer (frattini G : Set G)
  intro x hx
  exact
    (Subgroup.mem_center_iff.mp
      (frattini_le_center_of_natCard_le_two hcard hx) g).symm

/-- When the Frattini centralizer is the whole `2`-group, the corrected
Hall--Berger shape is already available: the commutative case is cyclic,
and the noncommutative case has central derived subgroup of order two. -/
theorem hallBergerTwoCoreShape_of_frattiniCentralizer_eq_top
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hCtop : frattiniCentralizer G = ⊤) :
    Nonempty (HallBergerTwoCoreShape G) := by
  let C : Subgroup G := frattiniCentralizer G
  let eC : C ≃* G :=
    (MulEquiv.subgroupCongr hCtop).trans
      Subgroup.topEquiv
  have hCenterC :
      IsCyclic (Subgroup.center C) :=
    frattiniCentralizer_center_isCyclic
      Nat.prime_two hG2 hBKN
  have hCenterG :
      IsCyclic (Subgroup.center G) :=
    (Subgroup.centerCongr eC).isCyclic.mp
      hCenterC
  by_cases hcomm : IsMulCommutative G
  · let groupG : Group G := inferInstance
    letI : CommGroup G :=
      { groupG with mul_comm := hcomm.1.1 }
    rw [CommGroup.center_eq_top] at hCenterG
    exact ⟨.cyclic
      (Subgroup.topEquiv.isCyclic.mp hCenterG)⟩
  · have hnoncommC : ¬ IsMulCommutative C := by
      intro hcommC
      apply hcomm
      refine ⟨⟨fun x y ↦ eC.symm.injective ?_⟩⟩
      simpa using
        hcommC.1.1 (eC.symm x) (eC.symm y)
    have hC :
        HasCentralCommutatorOfOrderTwo C :=
      frattiniCentralizer_hasCentralCommutatorOfOrderTwo
        hG2 hBKN hnoncommC
    exact ⟨.extraspecialCyclicProduct
      (hC.of_mulEquiv eC)⟩

/-- The small-Frattini branch of the corrected Hall--Berger
classification. -/
theorem hallBergerTwoCoreShape_of_natCard_frattini_le_two
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hcard : Nat.card (frattini G) ≤ 2) :
    Nonempty (HallBergerTwoCoreShape G) :=
  hallBergerTwoCoreShape_of_frattiniCentralizer_eq_top
    hG2 hBKN
      (frattiniCentralizer_eq_top_of_natCard_frattini_le_two
        hcard)

end LisiSabatini
