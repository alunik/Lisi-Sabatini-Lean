module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk03
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk04
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk05
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk06
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Sep000Chunk07

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def sepPredicate_10_40Chunks : List (IndexedBooleanCheckChunk sepPredicate_10_40) :=
  [⟨sepPredicate_10_40Chunk00Indices, sepPredicate_10_40Chunk00Checked⟩,
   ⟨sepPredicate_10_40Chunk01Indices, sepPredicate_10_40Chunk01Checked⟩,
   ⟨sepPredicate_10_40Chunk02Indices, sepPredicate_10_40Chunk02Checked⟩,
   ⟨sepPredicate_10_40Chunk03Indices, sepPredicate_10_40Chunk03Checked⟩,
   ⟨sepPredicate_10_40Chunk04Indices, sepPredicate_10_40Chunk04Checked⟩,
   ⟨sepPredicate_10_40Chunk05Indices, sepPredicate_10_40Chunk05Checked⟩,
   ⟨sepPredicate_10_40Chunk06Indices, sepPredicate_10_40Chunk06Checked⟩,
   ⟨sepPredicate_10_40Chunk07Indices, sepPredicate_10_40Chunk07Checked⟩]

theorem separation_10_40 : doubleCosetSeparationCheck row12 tests sepWitness_10_40 (reps 10) (reps
  40) = true := by
  exact all_finRange_of_checked_chunks
    sepPredicate_10_40 sepPredicate_10_40Chunks (by decide +kernel)

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
