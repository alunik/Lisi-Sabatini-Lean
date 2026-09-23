module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.InvolutionsChunk00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.InvolutionsChunk01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.InvolutionsChunk02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.InvolutionsChunk03

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicateChunks : List (IndexedBooleanCheckChunk involutionPredicate) :=
  [⟨involutionPredicateChunk00Indices, involutionPredicateChunk00Checked⟩,
   ⟨involutionPredicateChunk01Indices, involutionPredicateChunk01Checked⟩,
   ⟨involutionPredicateChunk02Indices, involutionPredicateChunk02Checked⟩,
   ⟨involutionPredicateChunk03Indices, involutionPredicateChunk03Checked⟩]

theorem involutions_complete : doubleCosetInvolutionIndicesCheck row9 0 involutionIndices = true
  := by
  exact all_finRange_of_checked_chunks
    involutionPredicate involutionPredicateChunks (by decide +kernel)

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
