module

public import LisiSabatini.SymmetricDoubleCosetRows
public import LisiSabatini.SymmetricEightTreeCheck
public import LisiSabatini.SymmetricDoubleCosetInvolutionCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def rep0 : Equiv.Perm (Fin 9) where
  toFun := ![4, 8, 6, 2, 5, 3, 1, 7, 0]
  invFun := ![8, 6, 3, 5, 0, 4, 2, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep1 : Equiv.Perm (Fin 9) where
  toFun := ![4, 7, 3, 0, 6, 8, 1, 5, 2]
  invFun := ![3, 6, 8, 2, 0, 7, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep2 : Equiv.Perm (Fin 9) where
  toFun := ![1, 4, 2, 8, 5, 7, 3, 6, 0]
  invFun := ![8, 0, 2, 6, 1, 4, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep3 : Equiv.Perm (Fin 9) where
  toFun := ![2, 5, 6, 4, 8, 1, 7, 3, 0]
  invFun := ![8, 5, 0, 7, 3, 1, 2, 6, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep4 : Equiv.Perm (Fin 9) where
  toFun := ![3, 7, 6, 8, 5, 2, 4, 1, 0]
  invFun := ![8, 7, 5, 0, 6, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep5 : Equiv.Perm (Fin 9) where
  toFun := ![6, 3, 0, 5, 7, 2, 1, 8, 4]
  invFun := ![2, 6, 5, 1, 8, 3, 0, 4, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep6 : Equiv.Perm (Fin 9) where
  toFun := ![4, 6, 7, 1, 8, 5, 2, 0, 3]
  invFun := ![7, 3, 6, 8, 0, 5, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repsArray : Array (Equiv.Perm (Fin 9)) :=
  #[rep0, rep1, rep2, rep3, rep4, rep5, rep6]

def reps (i : Fin 7) : Equiv.Perm (Fin 9) :=
  repsArray[i.val]'(by change i.val < 7; exact i.isLt)

def comparisons : Array (PermutationBlockComparison 9) :=
  #[⟨0, 1, 2⟩, ⟨2, 3, 2⟩, ⟨4, 5, 2⟩, ⟨6, 7, 2⟩, ⟨0, 2, 4⟩, ⟨4, 6, 4⟩, ⟨0, 4, 8⟩]

def tests (i : Fin 7) (g : Equiv.Perm (Fin 9)) : Bool :=
  blockComparisonCheck (comparisons[i.val]'(by exact i.isLt)) g

def involutionIndices : List (Fin 128) :=
  [1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 23, 24, 25, 26, 27, 28, 31, 32, 33,
    34, 35, 36, 39, 56, 57, 58, 59, 60, 63, 64, 73, 82, 91, 100, 110, 117, 127]

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
