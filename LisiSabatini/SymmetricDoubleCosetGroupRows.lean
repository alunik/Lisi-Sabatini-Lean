module

public import LisiSabatini.SymmetricDoubleCosetRows
public import LisiSabatini.SymmetricEightFastSubgroup

/-!
# Actual Sylow subgroups underlying the product certificate rows

The shared eight-point Sylow certificate and the small tail subgroups give
Sylow two-subgroups in degrees nine, ten, and twelve. Membership is equivalent
to occurrence in the computational rows used by the double-coset checks.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini.SymmetricDoubleCosetRows

open Equiv

/-- The degree-nine Sylow row from the eight-point Sylow and a trivial tail. -/
def sylow9 : Sylow 2 (Perm (Fin 9)) :=
  finBlockProductSylow 2
    (SymmetricEightFastSubgroup.sylow2 : Subgroup (Perm (Fin 8))) tailSubgroup1 (by
      rw [SymmetricEightFastSubgroup.card_sylow2, natCard_tailSubgroup1,
        show 8 + 1 = 9 from rfl, finBlockProductTwoPartNine])

/-- The degree-ten Sylow row from the eight-point Sylow and a two-point tail. -/
def sylow10 : Sylow 2 (Perm (Fin 10)) :=
  finBlockProductSylowTen
    (SymmetricEightFastSubgroup.sylow2 : Subgroup (Perm (Fin 8))) tailSubgroup2
    SymmetricEightFastSubgroup.card_sylow2 natCard_tailSubgroup2

/-- The degree-twelve Sylow row from the eight-point Sylow and a dihedral tail. -/
def sylow12 : Sylow 2 (Perm (Fin 12)) :=
  finBlockProductSylowTwelve
    (SymmetricEightFastSubgroup.sylow2 : Subgroup (Perm (Fin 8))) tailSubgroup4
    SymmetricEightFastSubgroup.card_sylow2 natCard_tailSubgroup4

/-- Exact cardinality of the degree-nine Sylow row. -/
theorem card_sylow9 : Nat.card sylow9 = 128 := by
  change Nat.card (finBlockProductSubgroup
    (SymmetricEightFastSubgroup.sylow2 : Subgroup (Perm (Fin 8))) tailSubgroup1) = 128
  rw [natCard_finBlockProductSubgroup, SymmetricEightFastSubgroup.card_sylow2,
    natCard_tailSubgroup1]

/-- Exact cardinality of the degree-ten Sylow row. -/
theorem card_sylow10 : Nat.card sylow10 = 256 :=
  natCard_finBlockProductSylowTen _ _
    SymmetricEightFastSubgroup.card_sylow2 natCard_tailSubgroup2

/-- Exact cardinality of the degree-twelve Sylow row. -/
theorem card_sylow12 : Nat.card sylow12 = 1024 :=
  natCard_finBlockProductSylowTwelve _ _
    SymmetricEightFastSubgroup.card_sylow2 natCard_tailSubgroup4

/-- The degree-nine computational rows enumerate exactly the Sylow subgroup. -/
theorem mem_sylow9_iff_row (σ : Perm (Fin 9)) :
    σ ∈ sylow9 ↔ ∃ i : Fin 128, row9 i = σ := by
  change σ ∈ finBlockProductSubgroup
    (SymmetricEightFastSubgroup.sylow2 : Subgroup (Perm (Fin 8))) tailSubgroup1 ↔ _
  rw [mem_finBlockProductSubgroup_iff_rows _ _
    SymmetricEightCertificates.rowAt tailRow1
    (fun g ↦ (SymmetricEightFastSubgroup.mem_sylow2_iff g).trans
      (SymmetricEightCertificates.mem_row_iff g)) mem_tailSubgroup1_iff]
  exact (exists_rowFromTail_iff tailRow1 σ).symm

/-- The degree-ten computational rows enumerate exactly the Sylow subgroup. -/
theorem mem_sylow10_iff_row (σ : Perm (Fin 10)) :
    σ ∈ sylow10 ↔ ∃ i : Fin 256, row10 i = σ := by
  change σ ∈ finBlockProductSubgroup
    (SymmetricEightFastSubgroup.sylow2 : Subgroup (Perm (Fin 8))) tailSubgroup2 ↔ _
  rw [mem_finBlockProductSubgroup_iff_rows _ _
    SymmetricEightCertificates.rowAt tailRow2
    (fun g ↦ (SymmetricEightFastSubgroup.mem_sylow2_iff g).trans
      (SymmetricEightCertificates.mem_row_iff g)) mem_tailSubgroup2_iff]
  exact (exists_rowFromTail_iff tailRow2 σ).symm

/-- The degree-twelve computational rows enumerate exactly the Sylow subgroup. -/
theorem mem_sylow12_iff_row (σ : Perm (Fin 12)) :
    σ ∈ sylow12 ↔ ∃ i : Fin 1024, row12 i = σ := by
  change σ ∈ finBlockProductSubgroup
    (SymmetricEightFastSubgroup.sylow2 : Subgroup (Perm (Fin 8))) tailSubgroup4 ↔ _
  rw [mem_finBlockProductSubgroup_iff_rows _ _
    SymmetricEightCertificates.rowAt tailRow4
    (fun g ↦ (SymmetricEightFastSubgroup.mem_sylow2_iff g).trans
      (SymmetricEightCertificates.mem_row_iff g)) mem_tailSubgroup4_iff]
  exact (exists_rowFromTail_iff tailRow4 σ).symm

/-- Every degree-nine computational row belongs to the certified Sylow. -/
theorem row9_mem (i : Fin 128) : row9 i ∈ sylow9 :=
  (mem_sylow9_iff_row _).mpr ⟨i, rfl⟩

/-- Every degree-ten computational row belongs to the certified Sylow. -/
theorem row10_mem (i : Fin 256) : row10 i ∈ sylow10 :=
  (mem_sylow10_iff_row _).mpr ⟨i, rfl⟩

/-- Every degree-twelve computational row belongs to the certified Sylow. -/
theorem row12_mem (i : Fin 1024) : row12 i ∈ sylow12 :=
  (mem_sylow12_iff_row _).mpr ⟨i, rfl⟩

end LisiSabatini.SymmetricDoubleCosetRows
