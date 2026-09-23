module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.NecessaryData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunk31Indices : List (Fin 1024) :=
  [992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008,
    1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023]

theorem necessaryPredicateChunk31Checked : necessaryPredicateChunk31Indices.all necessaryPredicate
  = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
