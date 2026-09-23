module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk00
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk01
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk02
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk03
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk04
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk05
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk06
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk07
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk08
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk09
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk10
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk11
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk12
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk13
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk14
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk15
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk16
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk17
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk18
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk19
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk20
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk21
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk22
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk23
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk24
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk25
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk26
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk27
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk28
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk29
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk30
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.InvolutionsChunk31

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

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
   ⟨involutionPredicateChunk07Indices, involutionPredicateChunk07Checked⟩,
   ⟨involutionPredicateChunk08Indices, involutionPredicateChunk08Checked⟩,
   ⟨involutionPredicateChunk09Indices, involutionPredicateChunk09Checked⟩,
   ⟨involutionPredicateChunk10Indices, involutionPredicateChunk10Checked⟩,
   ⟨involutionPredicateChunk11Indices, involutionPredicateChunk11Checked⟩,
   ⟨involutionPredicateChunk12Indices, involutionPredicateChunk12Checked⟩,
   ⟨involutionPredicateChunk13Indices, involutionPredicateChunk13Checked⟩,
   ⟨involutionPredicateChunk14Indices, involutionPredicateChunk14Checked⟩,
   ⟨involutionPredicateChunk15Indices, involutionPredicateChunk15Checked⟩,
   ⟨involutionPredicateChunk16Indices, involutionPredicateChunk16Checked⟩,
   ⟨involutionPredicateChunk17Indices, involutionPredicateChunk17Checked⟩,
   ⟨involutionPredicateChunk18Indices, involutionPredicateChunk18Checked⟩,
   ⟨involutionPredicateChunk19Indices, involutionPredicateChunk19Checked⟩,
   ⟨involutionPredicateChunk20Indices, involutionPredicateChunk20Checked⟩,
   ⟨involutionPredicateChunk21Indices, involutionPredicateChunk21Checked⟩,
   ⟨involutionPredicateChunk22Indices, involutionPredicateChunk22Checked⟩,
   ⟨involutionPredicateChunk23Indices, involutionPredicateChunk23Checked⟩,
   ⟨involutionPredicateChunk24Indices, involutionPredicateChunk24Checked⟩,
   ⟨involutionPredicateChunk25Indices, involutionPredicateChunk25Checked⟩,
   ⟨involutionPredicateChunk26Indices, involutionPredicateChunk26Checked⟩,
   ⟨involutionPredicateChunk27Indices, involutionPredicateChunk27Checked⟩,
   ⟨involutionPredicateChunk28Indices, involutionPredicateChunk28Checked⟩,
   ⟨involutionPredicateChunk29Indices, involutionPredicateChunk29Checked⟩,
   ⟨involutionPredicateChunk30Indices, involutionPredicateChunk30Checked⟩,
   ⟨involutionPredicateChunk31Indices, involutionPredicateChunk31Checked⟩]

theorem involutions_complete : doubleCosetInvolutionIndicesCheck row12 0 involutionIndices = true
  := by
  exact all_finRange_of_checked_chunks
    involutionPredicate involutionPredicateChunks (by decide +kernel)

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
