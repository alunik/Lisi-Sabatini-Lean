module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Data

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def goodWitness_1Array : Array (Fin 7) :=
  #[0, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0,
    1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 3, 0, 0, 0, 0, 0,
    0, 2, 2, 0, 0, 0, 0, 0, 0, 2, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0,
    0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0,
    0, 0, 0, 2]

def goodWitness_1 (i : Fin 128) : Fin 7 :=
  goodWitness_1Array[i.val]'(by change i.val < 128; exact i.isLt)

theorem good_1 :
    doubleCosetInvolutionGoodCheck row9 involutionIndices tests goodWitness_1 (reps 1) = true :=
      by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
