module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Data

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def sepWitness_1_6Array : Array (Fin 7) :=
  #[0, 1, 0, 0, 0, 0, 3, 0, 0, 1, 0, 0, 0, 0, 4, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1,
    0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0,
    1, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 2, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0,
    0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0,
    0, 0, 1, 0]

def sepWitness_1_6 (i : Fin 128) : Fin 7 :=
  sepWitness_1_6Array[i.val]'(by change i.val < 128; exact i.isLt)

theorem separation_1_6 :
    doubleCosetSeparationCheck row9 tests sepWitness_1_6 (reps 1) (reps 6) = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
