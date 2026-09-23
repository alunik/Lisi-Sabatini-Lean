module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsData

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicateChunk26Indices : List (Fin 1024) :=
  [832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850,
    851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863]

theorem involutionPredicateChunk26Checked : involutionPredicateChunk26Indices.all
  involutionPredicate = true := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
