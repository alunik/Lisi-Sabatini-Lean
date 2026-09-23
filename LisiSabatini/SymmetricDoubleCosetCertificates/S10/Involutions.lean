module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk03
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk04
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk05
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk06
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.InvolutionsChunk07

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def involutionPredicateChunks : List (IndexedBooleanCheckChunk involutionPredicate) :=
  [⟨involutionPredicateChunk00Indices, involutionPredicateChunk00Checked⟩,
   ⟨involutionPredicateChunk01Indices, involutionPredicateChunk01Checked⟩,
   ⟨involutionPredicateChunk02Indices, involutionPredicateChunk02Checked⟩,
   ⟨involutionPredicateChunk03Indices, involutionPredicateChunk03Checked⟩,
   ⟨involutionPredicateChunk04Indices, involutionPredicateChunk04Checked⟩,
   ⟨involutionPredicateChunk05Indices, involutionPredicateChunk05Checked⟩,
   ⟨involutionPredicateChunk06Indices, involutionPredicateChunk06Checked⟩,
   ⟨involutionPredicateChunk07Indices, involutionPredicateChunk07Checked⟩]

theorem involutions_complete : doubleCosetInvolutionIndicesCheck row10 0 involutionIndices = true
  := by
  exact all_finRange_of_checked_chunks
    involutionPredicate involutionPredicateChunks (by decide +kernel)

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
