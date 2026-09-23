module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Data
public import LisiSabatini.SymmetricDoubleCosetChunkCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicate (i : Fin 256) : Bool :=
  if i = 0 then true else if row10 i * row10 i = 1 then decide (i ∈ involutionIndices) else true

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
