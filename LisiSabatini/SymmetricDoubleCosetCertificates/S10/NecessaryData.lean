module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Data
public import LisiSabatini.SymmetricDoubleCosetChunkCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicate (i : Fin 256) : Bool :=
  (List.finRange 8).all (fun j ↦ tests j (row10 i))

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
