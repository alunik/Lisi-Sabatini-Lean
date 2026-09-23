module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Data
public import LisiSabatini.SymmetricDoubleCosetChunkCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicate (i : Fin 1024) : Bool :=
  (List.finRange 10).all (fun j ↦ tests j (row12 i))

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
