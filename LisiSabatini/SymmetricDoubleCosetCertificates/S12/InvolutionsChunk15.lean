module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicateChunk15Indices : List (Fin 1024) :=
  [480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498,
    499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511]

theorem involutionPredicateChunk15Checked : involutionPredicateChunk15Indices.all
  involutionPredicate = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
