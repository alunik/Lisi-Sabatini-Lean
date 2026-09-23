module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk03
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk04
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk05
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk06
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.NecessaryChunk07

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def necessaryPredicateChunks : List (IndexedBooleanCheckChunk necessaryPredicate) :=
  [⟨necessaryPredicateChunk00Indices, necessaryPredicateChunk00Checked⟩,
   ⟨necessaryPredicateChunk01Indices, necessaryPredicateChunk01Checked⟩,
   ⟨necessaryPredicateChunk02Indices, necessaryPredicateChunk02Checked⟩,
   ⟨necessaryPredicateChunk03Indices, necessaryPredicateChunk03Checked⟩,
   ⟨necessaryPredicateChunk04Indices, necessaryPredicateChunk04Checked⟩,
   ⟨necessaryPredicateChunk05Indices, necessaryPredicateChunk05Checked⟩,
   ⟨necessaryPredicateChunk06Indices, necessaryPredicateChunk06Checked⟩,
   ⟨necessaryPredicateChunk07Indices, necessaryPredicateChunk07Checked⟩]

theorem necessary : doubleCosetNecessaryCheck row10 tests = true := by
  exact all_finRange_of_checked_chunks
    necessaryPredicate necessaryPredicateChunks (by decide +kernel)

theorem row_zero : row10 0 = 1 := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
