import LisiSabatini.HallBergerResidualCyclic

/-!
# Decomposing the Hall--Berger Frattini centralizer

This packages the intrinsic centralizer part of the
Berger--Kovács--Newman proof.  Under the exact published omega-one
hypothesis, the Frattini centralizer is either cyclic or is the internal
central product of an extraspecial factor and a cyclic residual
centralizer.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The complete intrinsic decomposition of
`C_G(Φ(G))` needed in the `2`-group Hall--Berger argument. -/
theorem frattiniCentralizer_cyclic_or_exists_internal_extraspecial_factor_with_cyclic_residual
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G) :
    IsCyclic (frattiniCentralizer G) ∨
      ∃ E : Subgroup (frattiniCentralizer G),
        IsExtraspecial 2 E ∧
        IsInternalCentralFactor E ∧
        IsCyclic
          (Subgroup.centralizer
            (E : Set (frattiniCentralizer G))) := by
  let C : Subgroup G := frattiniCentralizer G
  have hCenterC :
      IsCyclic (Subgroup.center C) :=
    frattiniCentralizer_center_isCyclic
      Nat.prime_two hG2 hBKN
  by_cases hcomm : IsMulCommutative C
  · left
    let groupC : Group C := inferInstance
    letI : CommGroup C :=
      { groupC with mul_comm := hcomm.1.1 }
    rw [CommGroup.center_eq_top] at hCenterC
    exact Subgroup.topEquiv.isCyclic.mp hCenterC
  · right
    have hC :
        HasCentralCommutatorOfOrderTwo C :=
      frattiniCentralizer_hasCentralCommutatorOfOrderTwo
        hG2 hBKN hcomm
    have hOmegaCenter :
        IsCyclic
          (Subgroup.center (omegaOneSubgroup 2 C)) := by
      simpa only [C] using hBKN
    exact
      exists_internal_extraspecial_factor_with_cyclic_residual_of_centralCommutator
        (hG2.to_subgroup C) hC hOmegaCenter

end LisiSabatini
