module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.NecessaryData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunk29Indices : List (Fin 1024) :=
  [928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946,
    947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959]

theorem necessaryPredicateChunk29Checked : necessaryPredicateChunk29Indices.all necessaryPredicate
  = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
