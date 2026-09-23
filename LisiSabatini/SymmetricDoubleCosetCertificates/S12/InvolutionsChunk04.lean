module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicateChunk04Indices : List (Fin 1024) :=
  [128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146,
    147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159]

theorem involutionPredicateChunk04Checked : involutionPredicateChunk04Indices.all
  involutionPredicate = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
