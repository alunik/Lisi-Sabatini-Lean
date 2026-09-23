module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Data
public import LisiSabatini.SymmetricDoubleCosetChunkCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicate (i : Fin 128) : Bool :=
  (List.finRange 7).all (fun j ↦ tests j (row9 i))

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
