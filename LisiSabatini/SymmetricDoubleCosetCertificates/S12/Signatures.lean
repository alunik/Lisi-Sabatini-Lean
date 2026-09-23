module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Data
public import LisiSabatini.SymmetricDoubleCosetCentralRows
public import LisiSabatini.SymmetricDoubleCosetCentralInvariant

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

open LisiSabatini.SymmetricDoubleCosetCentralRows

def features : List (CentralFixedPowerFeature 12) :=
  [(z12Left, z12Left, 3), (z12Left, z12Both, 4), (z12Both, z12Left, 4), (z12Both, z12Both, 2),
    (z12Left, z12Left, 1)]

def signatureArray : Array (List ℕ) :=
  #[[4, 4, 4, 0, 1], [5, 4, 4, 0, 2], [5, 4, 2, 0, 2], [1, 4, 2, 0, 1], [4, 0, 6, 0, 1], [7, 0, 4,
    0, 1], [7, 4, 0, 0, 1], [7, 4, 4, 0, 1], [5, 4, 4, 4, 2], [1, 2, 2, 0, 1], [1, 2, 4, 0, 1],
    [3, 2, 2, 0, 0], [4, 2, 0, 0, 1], [7, 4, 4, 4, 1], [3, 2, 2, 0, 3], [5, 2, 4, 0, 2], [4, 6, 0,
    0, 1], [2, 6, 4, 4, 2], [2, 2, 4, 0, 2], [2, 4, 0, 0, 2], [6, 2, 4, 0, 0], [4, 4, 12, 4, 1],
    [7, 0, 0, 0, 1], [6, 4, 2, 0, 0], [4, 0, 2, 0, 1], [2, 4, 2, 0, 2], [4, 6, 6, 4, 1], [4, 12,
    4, 4, 1], [1, 6, 4, 4, 1], [3, 6, 6, 4, 3], [2, 4, 6, 4, 2], [0, 6, 6, 0, 0], [2, 0, 4, 0, 2],
    [2, 0, 6, 0, 2], [1, 4, 6, 4, 1], [2, 6, 0, 0, 2], [6, 6, 4, 4, 0], [12, 6, 6, 0, 3], [6, 4,
    6, 4, 0], [4, 12, 12, 12, 1], [1, 2, 4, 0, 1]]

def signatureAt (i : Fin 41) : List ℕ :=
  signatureArray[i.val]'(by change i.val < 41; exact i.isLt)

theorem signatures_checked :
    (List.finRange 41).all (fun i ↦
      decide (centralFixedPowerSignature features (reps i) = signatureAt i)) = true := by
  decide +kernel

theorem signature_eq (i : Fin 41) :
    centralFixedPowerSignature features (reps i) = signatureAt i := by
  exact of_decide_eq_true (List.all_eq_true.mp signatures_checked i (by simp))

def shortcut (i j : Fin 41) : Bool := decide (signatureAt i ≠ signatureAt j)

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
