module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.NecessaryData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunk27Indices : List (Fin 1024) :=
  [864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882,
    883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895]

theorem necessaryPredicateChunk27Checked : necessaryPredicateChunk27Indices.all necessaryPredicate
  = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
