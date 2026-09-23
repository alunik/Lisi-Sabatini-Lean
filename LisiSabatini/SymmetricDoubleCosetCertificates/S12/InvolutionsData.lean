module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Data
public import LisiSabatini.SymmetricDoubleCosetChunkCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicate (i : Fin 1024) : Bool :=
  if i = 0 then true else if row12 i * row12 i = 1 then decide (i ∈ involutionIndices) else true

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
