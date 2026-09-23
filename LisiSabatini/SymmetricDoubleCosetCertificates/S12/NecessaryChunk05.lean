module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.NecessaryData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunk05Indices : List (Fin 1024) :=
  [160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178,
    179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191]

theorem necessaryPredicateChunk05Checked : necessaryPredicateChunk05Indices.all necessaryPredicate
  = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
