module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Data
public import LisiSabatini.SymmetricDoubleCosetCentralRows
public import LisiSabatini.SymmetricDoubleCosetCentralInvariant

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

open LisiSabatini.SymmetricDoubleCosetCentralRows

def features : List (CentralFixedPowerFeature 10) :=
  [(z10Left, z10Left, 6), (z10Left, z10Both, 2)]

def signatureArray : Array (List ℕ) :=
  #[[3, 0], [1, 0], [10, 0], [6, 4], [5, 4], [6, 0]]

def signatureAt (i : Fin 6) : List ℕ :=
  signatureArray[i.val]'(by change i.val < 6; exact i.isLt)

theorem signatures_checked :
    (List.finRange 6).all (fun i ↦
      decide (centralFixedPowerSignature features (reps i) = signatureAt i)) = true := by
  decide +kernel

theorem signature_eq (i : Fin 6) :
    centralFixedPowerSignature features (reps i) = signatureAt i := by
  exact of_decide_eq_true (List.all_eq_true.mp signatures_checked i (by simp))

def shortcut (i j : Fin 6) : Bool := decide (signatureAt i ≠ signatureAt j)

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
