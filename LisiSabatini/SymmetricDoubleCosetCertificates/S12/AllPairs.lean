module

public import LisiSabatini.SymmetricDoubleCosetFallbackAssembly
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Signatures
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def pairCertificates : List (DoubleCosetPairCertificate row12 tests reps) :=
  [⟨(10, 40), sepWitness_10_40, separation_10_40⟩]

theorem pairCertificates_indices :
    doubleCosetPairCertificateIndices [pairCertificates] =
      (doubleCosetOrderedPairs 41).filter (fun ij ↦ !(shortcut ij.1 ij.2)) := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
