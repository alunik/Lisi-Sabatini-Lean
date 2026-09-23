module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.NecessaryData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunk19Indices : List (Fin 1024) :=
  [608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626,
    627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639]

theorem necessaryPredicateChunk19Checked : necessaryPredicateChunk19Indices.all necessaryPredicate
  = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
