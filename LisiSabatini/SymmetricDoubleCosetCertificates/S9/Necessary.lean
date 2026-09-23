module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.NecessaryChunk00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.NecessaryChunk01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.NecessaryChunk02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.NecessaryChunk03

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunks : List (IndexedBooleanCheckChunk necessaryPredicate) :=
  [⟨necessaryPredicateChunk00Indices, necessaryPredicateChunk00Checked⟩,
   ⟨necessaryPredicateChunk01Indices, necessaryPredicateChunk01Checked⟩,
   ⟨necessaryPredicateChunk02Indices, necessaryPredicateChunk02Checked⟩,
   ⟨necessaryPredicateChunk03Indices, necessaryPredicateChunk03Checked⟩]

theorem necessary : doubleCosetNecessaryCheck row9 tests = true := by
  exact all_finRange_of_checked_chunks
    necessaryPredicate necessaryPredicateChunks (by decide +kernel)

theorem row_zero : row9 0 = 1 := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
