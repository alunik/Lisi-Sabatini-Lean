module

public import LisiSabatini.CyclicCenterClassTwo

/-!
# Hall's cyclic-center class-two endpoint under central Frattini control

This is the group-theoretic endpoint used by the publication proof.  It is
independent of the later whole-core centralizer dichotomy and Hall-index
descent infrastructure.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

/-- Hall's hypothesis, noncommutativity, and central Frattini control give
the intrinsic cyclic-center class-two structure on the whole group. -/
def oddCyclicCenterClassTwo_of_hall_of_frattini_le_center
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hHall : HasCyclicCharacteristicAbelianSubgroups P)
    (hnoncomm : ¬ IsMulCommutative P)
    (hPhi : frattini P ≤ Subgroup.center P) :
    IsOddCyclicCenterClassTwo p P := by
  let hIntermediate : IsHallClassTwoIntermediate p P :=
    { prime := hp
      odd := hpOdd
      pGroup := hPp
      hall := hHall
      noncommutative := hnoncomm
      commutator_le_center :=
        (commutator_le_frattini_of_isPGroup hp hPp).trans hPhi
      centerPrimeKernel_le_commutator := by
        exact centerPrimeKernel_le_commutator_of_classTwo_of_center_isCyclic
          hp hPp
            ((commutator_le_frattini_of_isPGroup hp hPp).trans hPhi)
            hHall.center_isCyclic hnoncomm }
  exact hIntermediate.toOddCyclicCenterClassTwo hPhi

end LisiSabatini
