module

public import LisiSabatini.CyclicMaximalTwoGroupClassification
public import LisiSabatini.HallBergerCyclicCentralizerAssembly

/-!
# Applying cyclic-maximal classification uniformly outside the centralizer

The distinguished relation retained by the cyclic-maximal classification
says that the chosen coset representative inverts the square of the
rotation.  Replacing that representative by each element outside
`C_G(Φ(G))` therefore supplies the uniform inversion hypothesis of the
index-two theorem.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

namespace HallBergerCyclicHeadSeed

variable {G : Type u} [Group G] [Finite G]

/-- Every element outside the Frattini centralizer inverts the distinguished
square generator. -/
theorem outside_conj_rotationSquare_eq_inv
    (hG2 : IsPGroup 2 G)
    (seed : HallBergerCyclicHeadSeed G)
    (x : G)
    (hx : x ∉ frattiniCentralizer G) :
    x * (seed.rotation ^ 2) * x⁻¹ =
      (seed.rotation ^ 2)⁻¹ := by
  let seedX : HallBergerCyclicHeadSeed G :=
    seed.replaceCoset hG2 x hx
  let data :
      CyclicMaximalTwoGroupData seedX.headSubgroup :=
    seedX.cyclicMaximalTwoGroupData
  have hhead2 :
      IsPGroup 2 seedX.headSubgroup :=
    seedX.headSubgroup_isPGroup hG2
  have hinvert :
      data.coset * (data.rotation ^ 2) *
          data.coset⁻¹ =
        (data.rotation ^ 2)⁻¹ :=
    data.coset_conj_rotation_sq_inv hhead2
  exact congrArg Subtype.val hinvert

/-- The cyclic-maximal classification closes the index calculation for the
large square-image Hall--Berger seed. -/
theorem frattiniCentralizer_index_eq_two
    (hG2 : IsPGroup 2 G)
    (seed : HallBergerCyclicHeadSeed G) :
    (frattiniCentralizer G).index = 2 :=
  seed.frattiniCentralizer_index_eq_two_of_outside_inverts_rotationSquare
    (fun x hx =>
      seed.outside_conj_rotationSquare_eq_inv
        hG2 x hx)

/-- In the cyclic-centralizer branch, cyclic-maximal classification gives
the maximal-class head directly on the ambient group. -/
def ambientMaximalClassHeadOfCyclicFrattiniCentralizer
    (hG2 : IsPGroup 2 G)
    (seed : HallBergerCyclicHeadSeed G)
    (hCcyclic : IsCyclic (frattiniCentralizer G)) :
    BergerMaximalClassHead G := by
  let head :
      BergerMaximalClassHead seed.headSubgroup :=
    Classical.choice
      (seed.cyclicMaximalTwoGroupData.maximalClassHead
        (seed.headSubgroup_isPGroup hG2))
  exact
    seed.ambientMaximalClassHeadOfHeadSubgroupEqTop
      head
      (seed.headSubgroup_eq_top_of_frattiniCentralizer_isCyclic_of_index_two
        hCcyclic
        (seed.frattiniCentralizer_index_eq_two hG2))

end HallBergerCyclicHeadSeed

end LisiSabatini
