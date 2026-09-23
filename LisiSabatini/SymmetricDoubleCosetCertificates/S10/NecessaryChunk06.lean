module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunk06Indices : List (Fin 256) :=
  [192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210,
    211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223]

theorem necessaryPredicateChunk06Checked : necessaryPredicateChunk06Indices.all necessaryPredicate
  = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
