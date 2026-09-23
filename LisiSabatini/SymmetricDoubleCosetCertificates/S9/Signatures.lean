module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Data
public import LisiSabatini.SymmetricDoubleCosetCentralRows
public import LisiSabatini.SymmetricDoubleCosetCentralInvariant

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

open LisiSabatini.SymmetricDoubleCosetCentralRows

def features : List (CentralFixedPowerFeature 9) :=
  [(z9, z9, 6)]

def signatureArray : Array (List ℕ) :=
  #[[0], [0], [0], [9], [0], [4], [0]]

def signatureAt (i : Fin 7) : List ℕ :=
  signatureArray[i.val]'(by change i.val < 7; exact i.isLt)

theorem signatures_checked :
    (List.finRange 7).all (fun i ↦
      decide (centralFixedPowerSignature features (reps i) = signatureAt i)) = true := by
  decide +kernel

theorem signature_eq (i : Fin 7) :
    centralFixedPowerSignature features (reps i) = signatureAt i := by
  exact of_decide_eq_true (List.all_eq_true.mp signatures_checked i (by simp))

def shortcut (i j : Fin 7) : Bool := decide (signatureAt i ≠ signatureAt j)

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
