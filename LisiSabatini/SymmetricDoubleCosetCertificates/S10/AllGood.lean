module

public import LisiSabatini.SymmetricDoubleCosetCertificateAssembly
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Good00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Good01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Good02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Good03
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Good04
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Good05

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def goodCertificates : List (DoubleCosetInvolutionGoodCertificate row10 involutionIndices tests
  reps) :=
  [⟨0, goodWitness_0, good_0⟩,
   ⟨1, goodWitness_1, good_1⟩,
   ⟨2, goodWitness_2, good_2⟩,
   ⟨3, goodWitness_3, good_3⟩,
   ⟨4, goodWitness_4, good_4⟩,
   ⟨5, goodWitness_5, good_5⟩]

theorem goodCertificates_indices :
    goodCertificates.map (fun c ↦ c.index) = List.finRange 6 := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
