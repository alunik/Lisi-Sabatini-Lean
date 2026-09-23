module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Data
public import LisiSabatini.SymmetricDoubleCosetChunkCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicate (i : Fin 128) : Bool :=
  if i = 0 then true else if row9 i * row9 i = 1 then decide (i ∈ involutionIndices) else true

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
