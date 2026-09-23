module

public import LisiSabatini.SymmetricDoubleCosetProductRows
public import LisiSabatini.SymmetricDoubleCosetTailRows
public import LisiSabatini.SymmetricEightCertificates.Table

/-!
# Computational product rows in degrees nine, ten, and twelve

The eight-point row is the outer index; the tail row is the inner index.
Thus a combined row has index `tailIndex + tailSize * eightPointIndex`.
These definitions are shared by the computational certificate checks and the
actual subgroup constructions.
-/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetRows

open Equiv

/-- Combine the shared eight-point row with an independently indexed tail. -/
def rowFromTail {b k : ℕ} (tail : Fin k → Perm (Fin b))
    (i : Fin (128 * k)) : Perm (Fin (8 + b)) :=
  finBlockSumPermHom 8 b
    (SymmetricEightCertificates.rowAt (finProdFinEquiv.symm i).1,
      tail (finProdFinEquiv.symm i).2)

/-- Degree-nine product row, with its final point fixed. -/
def row9 : Fin 128 → Perm (Fin 9) := rowFromTail tailRow1

/-- Degree-ten product row, with an independent two-point tail. -/
def row10 : Fin 256 → Perm (Fin 10) := rowFromTail tailRow2

/-- Degree-twelve product row, with an independent dihedral four-point tail. -/
def row12 : Fin 1024 → Perm (Fin 12) := rowFromTail tailRow4

/-- Pair indices have the specified outer-eight-point/inner-tail ordering. -/
theorem rowFromTail_finProdFinEquiv {b k : ℕ} (tail : Fin k → Perm (Fin b))
    (i : Fin 128) (j : Fin k) :
    rowFromTail tail (finProdFinEquiv (i, j)) =
      finBlockSumPermHom 8 b (SymmetricEightCertificates.rowAt i, tail j) := by
  simp [rowFromTail]

/-- Indexing by one finite product index enumerates exactly the pairs of rows. -/
theorem exists_rowFromTail_iff {b k : ℕ} (tail : Fin k → Perm (Fin b))
    (σ : Perm (Fin (8 + b))) :
    (∃ t, rowFromTail tail t = σ) ↔
      ∃ i j, finBlockSumPermHom 8 b (SymmetricEightCertificates.rowAt i, tail j) = σ := by
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨(finProdFinEquiv.symm t).1, (finProdFinEquiv.symm t).2, ht⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨finProdFinEquiv (i, j), (rowFromTail_finProdFinEquiv tail i j).trans hij⟩

end LisiSabatini.SymmetricDoubleCosetRows
