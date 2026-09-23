module

public import LisiSabatini.SymmetricDoubleCosetArithmetic
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Certificate
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Certificate
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Certificate

/-!
# Concrete good double-coset families in degrees nine, ten and twelve

The witnesses below are actual permutations, checked against the product
Sylow subgroups. Individual failed-block proofs are assembled with exact
coverage of all representative pairs.
-/

@[expose] public section

namespace LisiSabatini

open SymmetricDoubleCosetRows

/-- Explicit kernel-certified good double cosets with their exact Sylow orders. -/
theorem exists_symmetricDoubleCosetCertificate (n : ℕ)
    (hn : n = 9 ∨ n = 10 ∨ n = 12) :
    ∃ (R : Sylow 2 (Equiv.Perm (Fin n))),
      Nat.card R = doubleCosetSylowTwoOrder n ∧
      ∃ (g : Fin (doubleCosetGoodCount n) → Equiv.Perm (Fin n)),
        (∀ i, mixedSylowInter R R (g i) = ⊥) ∧
        (∀ i j, i ≠ j → ∀ a ∈ (R : Subgroup _),
          (g i)⁻¹ * a * g j ∉ (R : Subgroup _)) := by
  rcases hn with rfl | rfl | rfl
  · refine ⟨sylow9, ?_, SymmetricDoubleCosetCertificates.S9.reps,
      SymmetricDoubleCosetCertificates.S9.all_good,
      SymmetricDoubleCosetCertificates.S9.all_separated⟩
    simpa [doubleCosetSylowTwoOrder] using card_sylow9
  · refine ⟨sylow10, ?_, SymmetricDoubleCosetCertificates.S10.reps,
      SymmetricDoubleCosetCertificates.S10.all_good,
      SymmetricDoubleCosetCertificates.S10.all_separated⟩
    simpa [doubleCosetSylowTwoOrder] using card_sylow10
  · refine ⟨sylow12, ?_, SymmetricDoubleCosetCertificates.S12.reps,
      SymmetricDoubleCosetCertificates.S12.all_good,
      SymmetricDoubleCosetCertificates.S12.all_separated⟩
    simpa [doubleCosetSylowTwoOrder] using card_sylow12

end LisiSabatini
