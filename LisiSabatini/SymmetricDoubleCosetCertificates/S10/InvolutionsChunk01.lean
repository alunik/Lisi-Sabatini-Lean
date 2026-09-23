module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicateChunk01Indices : List (Fin 256) :=
  [32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55,
    56, 57, 58, 59, 60, 61, 62, 63]

theorem involutionPredicateChunk01Checked : involutionPredicateChunk01Indices.all
  involutionPredicate = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
