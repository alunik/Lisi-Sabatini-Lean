module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Data

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def sepWitness_2_4Array : Array (Fin 7) :=
  #[0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 1, 0]

def sepWitness_2_4 (i : Fin 128) : Fin 7 :=
  sepWitness_2_4Array[i.val]'(by change i.val < 128; exact i.isLt)

theorem separation_2_4 :
    doubleCosetSeparationCheck row9 tests sepWitness_2_4 (reps 2) (reps 4) = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
