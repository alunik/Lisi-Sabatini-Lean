module

public import LisiSabatini.SymmetricDoubleCosetRows
public import LisiSabatini.SymmetricEightTreeCheck
public import LisiSabatini.SymmetricDoubleCosetInvolutionCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def rep0 : Equiv.Perm (Fin 10) where
  toFun := ![1, 2, 9, 4, 8, 6, 3, 5, 0, 7]
  invFun := ![8, 0, 1, 6, 3, 7, 5, 9, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep1 : Equiv.Perm (Fin 10) where
  toFun := ![7, 0, 4, 9, 6, 5, 2, 1, 8, 3]
  invFun := ![1, 7, 6, 9, 2, 5, 4, 0, 8, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep2 : Equiv.Perm (Fin 10) where
  toFun := ![1, 7, 8, 5, 3, 0, 6, 2, 4, 9]
  invFun := ![5, 0, 7, 4, 8, 3, 6, 1, 2, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep3 : Equiv.Perm (Fin 10) where
  toFun := ![1, 4, 2, 9, 8, 6, 7, 3, 5, 0]
  invFun := ![9, 0, 2, 7, 1, 8, 5, 6, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep4 : Equiv.Perm (Fin 10) where
  toFun := ![0, 4, 2, 7, 8, 1, 6, 3, 5, 9]
  invFun := ![0, 5, 2, 7, 1, 8, 6, 3, 4, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep5 : Equiv.Perm (Fin 10) where
  toFun := ![3, 1, 8, 4, 9, 5, 0, 7, 2, 6]
  invFun := ![6, 1, 8, 0, 3, 5, 9, 7, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repsArray : Array (Equiv.Perm (Fin 10)) :=
  #[rep0, rep1, rep2, rep3, rep4, rep5]

def reps (i : Fin 6) : Equiv.Perm (Fin 10) :=
  repsArray[i.val]'(by change i.val < 6; exact i.isLt)

def comparisons : Array (PermutationBlockComparison 10) :=
  #[⟨0, 1, 2⟩, ⟨2, 3, 2⟩, ⟨4, 5, 2⟩, ⟨6, 7, 2⟩, ⟨8, 9, 2⟩, ⟨0, 2, 4⟩, ⟨4, 6, 4⟩, ⟨0, 4, 8⟩]

def tests (i : Fin 8) (g : Equiv.Perm (Fin 10)) : Bool :=
  blockComparisonCheck (comparisons[i.val]'(by exact i.isLt)) g

def involutionIndices : List (Fin 256) :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 30, 31, 32, 33, 34,
    35, 36, 37, 38, 39, 40, 41, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 62, 63, 64, 65,
    66, 67, 68, 69, 70, 71, 72, 73, 78, 79, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 126,
    127, 128, 129, 146, 147, 164, 165, 182, 183, 200, 201, 220, 221, 234, 235, 254, 255]

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
