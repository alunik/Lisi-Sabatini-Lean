module

public import LisiSabatini.HallBergerCyclicHeadUniformCoset
public import LisiSabatini.HallBergerHeadTransport

/-!
# Assembly when the Hall--Berger Frattini centralizer is cyclic

In the large square-image branch the cyclic-head seed has
`⟨rotation⟩ = Z(C_G(Φ(G)))`.  If the whole Frattini centralizer is cyclic,
this is simply the entire centralizer.  Once the uniform outside action has
shown that the centralizer has index two, the seed head is therefore the
whole ambient group.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

namespace HallBergerCyclicHeadSeed

variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
/-- A cyclic subgroup equals the ambient image of its own center. -/
theorem characteristicCenterImage_eq_self_of_isCyclic
    (C : Subgroup G)
    (hCcyclic : IsCyclic C) :
    characteristicCenterImage C = C := by
  rw [characteristicCenterImage_eq_inf_centralizer]
  apply le_antisymm inf_le_left
  intro c hc
  refine ⟨hc, ?_⟩
  intro c' hc'
  exact congrArg Subtype.val
    (hCcyclic.commutative.comm
      (⟨c', hc'⟩ : C) (⟨c, hc⟩ : C))

/-- In the cyclic-centralizer branch, an index-two seed head is the whole
ambient group. -/
theorem headSubgroup_eq_top_of_frattiniCentralizer_isCyclic_of_index_two
    (seed : HallBergerCyclicHeadSeed G)
    (hCcyclic : IsCyclic (frattiniCentralizer G))
    (hindex :
      (frattiniCentralizer G).index = 2) :
    seed.headSubgroup = ⊤ := by
  rw [headSubgroup,
    seed.rotation_generates_centerImage,
    characteristicCenterImage_eq_self_of_isCyclic
      (frattiniCentralizer G) hCcyclic]
  exact
    seed.frattiniCentralizer_sup_zpowers_eq_top_of_index_two
      hindex

/-- Transport a classified seed head to the ambient group once the head
subgroup has been identified with `⊤`. -/
def ambientMaximalClassHeadOfHeadSubgroupEqTop
    (seed : HallBergerCyclicHeadSeed G)
    (head :
      BergerMaximalClassHead seed.headSubgroup)
    (hhead : seed.headSubgroup = ⊤) :
    BergerMaximalClassHead G :=
  BergerMaximalClassHead.ofMulEquiv head
    ((MulEquiv.subgroupCongr hhead).trans
      Subgroup.topEquiv)

end HallBergerCyclicHeadSeed

end LisiSabatini
