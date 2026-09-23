module

public import LisiSabatini.SymmetricDoubleCosetFallbackAssembly
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Signatures

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def pairCertificates : List (DoubleCosetPairCertificate row10 tests reps) :=
  []

theorem pairCertificates_indices :
    doubleCosetPairCertificateIndices [pairCertificates] =
      (doubleCosetOrderedPairs 6).filter (fun ij ↦ !(shortcut ij.1 ij.2)) := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
