module

public import LisiSabatini.SymmetricDoubleCosetCertificateAssembly
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Good00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Good01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Good02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Good03
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Good04
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Good05
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Good06

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def goodCertificates : List (DoubleCosetInvolutionGoodCertificate row9 involutionIndices tests
  reps) :=
  [⟨0, goodWitness_0, good_0⟩,
   ⟨1, goodWitness_1, good_1⟩,
   ⟨2, goodWitness_2, good_2⟩,
   ⟨3, goodWitness_3, good_3⟩,
   ⟨4, goodWitness_4, good_4⟩,
   ⟨5, goodWitness_5, good_5⟩,
   ⟨6, goodWitness_6, good_6⟩]

theorem goodCertificates_indices :
    goodCertificates.map (fun c ↦ c.index) = List.finRange 7 := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
