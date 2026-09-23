module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Data

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def goodWitness_4Array : Array (Fin 7) :=
  #[0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 3, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1,
    0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0,
    0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 0, 1, 0]

def goodWitness_4 (i : Fin 128) : Fin 7 :=
  goodWitness_4Array[i.val]'(by change i.val < 128; exact i.isLt)

theorem good_4 :
    doubleCosetInvolutionGoodCheck row9 involutionIndices tests goodWitness_4 (reps 4) = true :=
      by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
