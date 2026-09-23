module

public import LisiSabatini.SymmetricDoubleCosetRows
public import LisiSabatini.SymmetricEightTreeCheck
public import LisiSabatini.SymmetricDoubleCosetInvolutionCheck

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

def rep0 : Equiv.Perm (Fin 12) where
  toFun := ![4, 8, 7, 9, 1, 3, 5, 10, 6, 0, 2, 11]
  invFun := ![9, 4, 10, 5, 0, 6, 8, 2, 1, 3, 7, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep1 : Equiv.Perm (Fin 12) where
  toFun := ![3, 1, 2, 6, 0, 8, 5, 10, 7, 11, 4, 9]
  invFun := ![4, 1, 2, 0, 10, 6, 3, 8, 5, 11, 7, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep2 : Equiv.Perm (Fin 12) where
  toFun := ![8, 5, 4, 3, 9, 1, 2, 7, 10, 6, 11, 0]
  invFun := ![11, 5, 6, 3, 2, 1, 9, 7, 0, 4, 8, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep3 : Equiv.Perm (Fin 12) where
  toFun := ![5, 11, 6, 4, 1, 9, 0, 10, 2, 8, 3, 7]
  invFun := ![6, 4, 8, 10, 3, 0, 2, 11, 9, 5, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep4 : Equiv.Perm (Fin 12) where
  toFun := ![3, 6, 10, 7, 9, 4, 11, 2, 5, 0, 1, 8]
  invFun := ![9, 10, 7, 0, 5, 8, 1, 3, 11, 4, 2, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep5 : Equiv.Perm (Fin 12) where
  toFun := ![4, 11, 6, 8, 9, 1, 2, 7, 0, 5, 3, 10]
  invFun := ![8, 5, 6, 10, 0, 9, 2, 7, 3, 4, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep6 : Equiv.Perm (Fin 12) where
  toFun := ![10, 6, 3, 8, 5, 11, 2, 1, 4, 9, 0, 7]
  invFun := ![10, 7, 6, 2, 8, 4, 1, 11, 3, 9, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep7 : Equiv.Perm (Fin 12) where
  toFun := ![4, 1, 8, 5, 11, 7, 3, 9, 10, 2, 0, 6]
  invFun := ![10, 1, 9, 6, 0, 3, 11, 5, 2, 7, 8, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep8 : Equiv.Perm (Fin 12) where
  toFun := ![11, 1, 4, 7, 2, 8, 0, 6, 5, 10, 3, 9]
  invFun := ![6, 1, 4, 10, 2, 8, 7, 3, 5, 11, 9, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep9 : Equiv.Perm (Fin 12) where
  toFun := ![9, 10, 11, 0, 2, 4, 1, 3, 8, 7, 5, 6]
  invFun := ![3, 6, 4, 7, 5, 10, 11, 9, 8, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep10 : Equiv.Perm (Fin 12) where
  toFun := ![8, 11, 9, 4, 7, 3, 1, 5, 0, 2, 6, 10]
  invFun := ![8, 6, 9, 5, 3, 7, 10, 4, 0, 2, 11, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep11 : Equiv.Perm (Fin 12) where
  toFun := ![10, 8, 0, 9, 2, 1, 11, 7, 4, 3, 6, 5]
  invFun := ![2, 5, 4, 9, 8, 11, 10, 7, 1, 3, 0, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep12 : Equiv.Perm (Fin 12) where
  toFun := ![8, 11, 7, 4, 10, 1, 6, 2, 3, 0, 5, 9]
  invFun := ![9, 5, 7, 8, 3, 10, 6, 2, 0, 11, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep13 : Equiv.Perm (Fin 12) where
  toFun := ![1, 6, 10, 0, 9, 4, 11, 3, 8, 5, 2, 7]
  invFun := ![3, 0, 10, 7, 5, 9, 1, 11, 8, 4, 2, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep14 : Equiv.Perm (Fin 12) where
  toFun := ![4, 0, 2, 7, 11, 1, 5, 3, 8, 10, 6, 9]
  invFun := ![1, 5, 2, 7, 0, 6, 10, 3, 8, 11, 9, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep15 : Equiv.Perm (Fin 12) where
  toFun := ![11, 5, 6, 9, 7, 2, 3, 1, 10, 8, 4, 0]
  invFun := ![11, 7, 5, 6, 10, 1, 2, 4, 9, 3, 8, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep16 : Equiv.Perm (Fin 12) where
  toFun := ![2, 1, 10, 6, 9, 11, 5, 0, 7, 8, 3, 4]
  invFun := ![7, 1, 0, 10, 11, 6, 3, 8, 9, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep17 : Equiv.Perm (Fin 12) where
  toFun := ![11, 1, 0, 7, 5, 2, 8, 6, 9, 10, 3, 4]
  invFun := ![2, 1, 5, 10, 11, 4, 7, 3, 6, 8, 9, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep18 : Equiv.Perm (Fin 12) where
  toFun := ![8, 10, 5, 6, 3, 4, 1, 2, 11, 7, 0, 9]
  invFun := ![10, 6, 7, 4, 5, 2, 3, 9, 0, 11, 1, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep19 : Equiv.Perm (Fin 12) where
  toFun := ![1, 7, 6, 4, 8, 3, 10, 2, 5, 11, 0, 9]
  invFun := ![10, 0, 7, 5, 3, 8, 2, 1, 4, 11, 6, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep20 : Equiv.Perm (Fin 12) where
  toFun := ![9, 0, 6, 3, 10, 8, 11, 4, 1, 2, 7, 5]
  invFun := ![1, 8, 9, 3, 7, 11, 2, 10, 5, 0, 4, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep21 : Equiv.Perm (Fin 12) where
  toFun := ![10, 1, 7, 9, 8, 6, 5, 2, 4, 0, 3, 11]
  invFun := ![9, 1, 7, 10, 8, 6, 5, 2, 4, 3, 0, 11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep22 : Equiv.Perm (Fin 12) where
  toFun := ![3, 4, 0, 10, 9, 5, 6, 11, 7, 1, 2, 8]
  invFun := ![2, 9, 10, 0, 1, 5, 6, 8, 11, 4, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep23 : Equiv.Perm (Fin 12) where
  toFun := ![4, 10, 6, 11, 0, 9, 7, 8, 5, 2, 3, 1]
  invFun := ![4, 11, 9, 10, 0, 8, 2, 6, 7, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep24 : Equiv.Perm (Fin 12) where
  toFun := ![10, 4, 0, 7, 6, 9, 11, 1, 2, 8, 5, 3]
  invFun := ![2, 7, 8, 11, 1, 10, 4, 3, 9, 5, 0, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep25 : Equiv.Perm (Fin 12) where
  toFun := ![0, 7, 1, 2, 6, 11, 3, 9, 4, 10, 8, 5]
  invFun := ![0, 2, 3, 6, 8, 11, 4, 1, 10, 7, 9, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep26 : Equiv.Perm (Fin 12) where
  toFun := ![5, 3, 10, 6, 2, 4, 11, 9, 7, 1, 8, 0]
  invFun := ![11, 9, 4, 1, 5, 0, 3, 8, 10, 7, 2, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep27 : Equiv.Perm (Fin 12) where
  toFun := ![8, 2, 4, 0, 6, 10, 9, 7, 3, 11, 5, 1]
  invFun := ![3, 11, 1, 8, 2, 10, 4, 7, 0, 6, 5, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep28 : Equiv.Perm (Fin 12) where
  toFun := ![7, 2, 10, 3, 9, 11, 0, 4, 6, 8, 5, 1]
  invFun := ![6, 11, 1, 3, 7, 10, 8, 0, 9, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep29 : Equiv.Perm (Fin 12) where
  toFun := ![6, 2, 0, 4, 5, 1, 10, 3, 11, 8, 9, 7]
  invFun := ![2, 5, 1, 7, 3, 4, 0, 11, 9, 10, 6, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep30 : Equiv.Perm (Fin 12) where
  toFun := ![7, 5, 3, 10, 1, 6, 2, 11, 8, 4, 9, 0]
  invFun := ![11, 4, 6, 2, 9, 1, 5, 0, 8, 10, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep31 : Equiv.Perm (Fin 12) where
  toFun := ![10, 9, 8, 4, 7, 0, 11, 5, 1, 3, 6, 2]
  invFun := ![5, 8, 11, 9, 3, 7, 10, 4, 2, 1, 0, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep32 : Equiv.Perm (Fin 12) where
  toFun := ![8, 7, 6, 1, 2, 4, 11, 0, 9, 5, 10, 3]
  invFun := ![7, 3, 4, 11, 5, 9, 2, 1, 0, 8, 10, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep33 : Equiv.Perm (Fin 12) where
  toFun := ![3, 4, 9, 1, 0, 7, 8, 6, 5, 10, 11, 2]
  invFun := ![4, 3, 11, 0, 1, 8, 7, 5, 6, 2, 9, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep34 : Equiv.Perm (Fin 12) where
  toFun := ![5, 10, 6, 9, 8, 7, 4, 2, 1, 3, 11, 0]
  invFun := ![11, 8, 7, 9, 6, 0, 2, 5, 4, 3, 1, 10]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep35 : Equiv.Perm (Fin 12) where
  toFun := ![4, 0, 3, 9, 11, 2, 5, 6, 8, 10, 7, 1]
  invFun := ![1, 11, 5, 2, 0, 6, 7, 10, 8, 3, 9, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep36 : Equiv.Perm (Fin 12) where
  toFun := ![0, 10, 3, 5, 9, 11, 8, 6, 2, 4, 1, 7]
  invFun := ![0, 10, 8, 2, 9, 3, 7, 11, 6, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep37 : Equiv.Perm (Fin 12) where
  toFun := ![4, 3, 2, 0, 7, 10, 5, 1, 8, 11, 6, 9]
  invFun := ![3, 7, 2, 1, 0, 6, 10, 4, 8, 11, 5, 9]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep38 : Equiv.Perm (Fin 12) where
  toFun := ![9, 1, 11, 4, 0, 8, 10, 2, 7, 3, 5, 6]
  invFun := ![4, 1, 7, 9, 3, 10, 11, 8, 5, 0, 6, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep39 : Equiv.Perm (Fin 12) where
  toFun := ![0, 11, 9, 6, 7, 8, 4, 3, 1, 10, 5, 2]
  invFun := ![0, 8, 11, 7, 6, 10, 3, 4, 5, 2, 9, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rep40 : Equiv.Perm (Fin 12) where
  toFun := ![2, 0, 10, 9, 3, 8, 6, 5, 11, 4, 7, 1]
  invFun := ![1, 11, 0, 4, 9, 7, 6, 10, 5, 3, 2, 8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def repsArray : Array (Equiv.Perm (Fin 12)) :=
  #[rep0, rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8, rep9, rep10, rep11, rep12, rep13, rep14,
    rep15, rep16, rep17, rep18, rep19, rep20, rep21, rep22, rep23, rep24, rep25, rep26, rep27,
    rep28, rep29, rep30, rep31, rep32, rep33, rep34, rep35, rep36, rep37, rep38, rep39, rep40]

def reps (i : Fin 41) : Equiv.Perm (Fin 12) :=
  repsArray[i.val]'(by change i.val < 41; exact i.isLt)

def comparisons : Array (PermutationBlockComparison 12) :=
  #[⟨0, 1, 2⟩, ⟨2, 3, 2⟩, ⟨4, 5, 2⟩, ⟨6, 7, 2⟩, ⟨8, 9, 2⟩, ⟨10, 11, 2⟩, ⟨0, 2, 4⟩, ⟨4, 6, 4⟩, ⟨8,
    10, 4⟩, ⟨0, 4, 8⟩]

def tests (i : Fin 10) (g : Equiv.Perm (Fin 12)) : Bool :=
  blockComparisonCheck (comparisons[i.val]'(by exact i.isLt)) g

def involutionIndices : List (Fin 1024) :=
  [1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 23, 24, 25, 26, 27, 28, 31, 32, 33,
    34, 35, 36, 39, 56, 57, 58, 59, 60, 63, 64, 65, 66, 67, 68, 71, 72, 73, 74, 75, 76, 79, 80,
    81, 82, 83, 84, 87, 88, 89, 90, 91, 92, 95, 96, 97, 98, 99, 100, 103, 120, 121, 122, 123, 124,
    127, 128, 129, 130, 131, 132, 135, 136, 137, 138, 139, 140, 143, 144, 145, 146, 147, 148, 151,
    152, 153, 154, 155, 156, 159, 160, 161, 162, 163, 164, 167, 184, 185, 186, 187, 188, 191, 192,
    193, 194, 195, 196, 199, 200, 201, 202, 203, 204, 207, 208, 209, 210, 211, 212, 215, 216, 217,
    218, 219, 220, 223, 224, 225, 226, 227, 228, 231, 248, 249, 250, 251, 252, 255, 256, 257, 258,
    259, 260, 263, 264, 265, 266, 267, 268, 271, 272, 273, 274, 275, 276, 279, 280, 281, 282, 283,
    284, 287, 288, 289, 290, 291, 292, 295, 312, 313, 314, 315, 316, 319, 448, 449, 450, 451, 452,
    455, 456, 457, 458, 459, 460, 463, 464, 465, 466, 467, 468, 471, 472, 473, 474, 475, 476, 479,
    480, 481, 482, 483, 484, 487, 504, 505, 506, 507, 508, 511, 512, 513, 514, 515, 516, 519, 584,
    585, 586, 587, 588, 591, 656, 657, 658, 659, 660, 663, 728, 729, 730, 731, 732, 735, 800, 801,
    802, 803, 804, 807, 880, 881, 882, 883, 884, 887, 936, 937, 938, 939, 940, 943, 1016, 1017,
    1018, 1019, 1020, 1023]

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
