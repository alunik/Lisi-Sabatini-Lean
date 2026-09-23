module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicateChunk20Indices : List (Fin 1024) :=
  [640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658,
    659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671]

theorem involutionPredicateChunk20Checked : involutionPredicateChunk20Indices.all
  involutionPredicate = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
