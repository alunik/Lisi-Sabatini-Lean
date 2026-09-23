module

public import LisiSabatini.A8DoubleCosetVerified
public import LisiSabatini.SymmetricEightFromAlternating

/-!
# The degree-eight symmetric group

The verified alternating-group Sylow-two witness supplies the exact input
to the index-two dichotomy. The conclusion is simultaneous inclusion-minimal
intersections for every finite family of prescribed Sylow subgroups.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI

open FiniteCertificates

/-- Every finite prime-labelled Sylow family in S8 admits one conjugator
making all its intersections inclusion-minimal. The index universe is arbitrary. -/
theorem hasLisiSabatini_symmetricGroup_eight :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin 8)) :=
  hasLisiSabatini_symmetricEight_of_A8_one_pair
    A8Rows.sylow2 A8SylowTwoWitness.card_sylow2
    ⟨A8SylowTwoWitness.witness, A8SylowTwoWitness.sylow2_inter_witness_eq_bot⟩

end LisiSabatini
