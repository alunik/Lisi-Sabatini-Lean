module

public import LisiSabatini.SymmetricDoubleCosetFallbackAssembly
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Signatures
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep000
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep001
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep002
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep003
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep004
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep005
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep006
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep007
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep008
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Sep009

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def pairCertificates : List (DoubleCosetPairCertificate row9 tests reps) :=
  [⟨(0, 1), sepWitness_0_1, separation_0_1⟩,
   ⟨(0, 2), sepWitness_0_2, separation_0_2⟩,
   ⟨(0, 4), sepWitness_0_4, separation_0_4⟩,
   ⟨(0, 6), sepWitness_0_6, separation_0_6⟩,
   ⟨(1, 2), sepWitness_1_2, separation_1_2⟩,
   ⟨(1, 4), sepWitness_1_4, separation_1_4⟩,
   ⟨(1, 6), sepWitness_1_6, separation_1_6⟩,
   ⟨(2, 4), sepWitness_2_4, separation_2_4⟩,
   ⟨(2, 6), sepWitness_2_6, separation_2_6⟩,
   ⟨(4, 6), sepWitness_4_6, separation_4_6⟩]

theorem pairCertificates_indices :
    doubleCosetPairCertificateIndices [pairCertificates] =
      (doubleCosetOrderedPairs 7).filter (fun ij ↦ !(shortcut ij.1 ij.2)) := by
  decide +kernel

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
