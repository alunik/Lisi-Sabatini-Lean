module

public import LisiSabatini.SymmetricDoubleCosetRows
public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.List.FinRange

/-!
# Central involutions in the double-coset product rows

The simultaneous sibling flip on eight points commutes with all 128 factor
rows. This is checked by 1024 point comparisons. Commutation in the product
rows follows from the block-sum homomorphism, without checking all 1024 rows
in degree twelve. The explicit row indices also certify membership whenever
the row-to-subgroup correspondence is applied.
-/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCentralRows

open Equiv SymmetricDoubleCosetRows

/-- The simultaneous flip `(0 1)(2 3)(4 5)(6 7)` in the shared eight-point table. -/
def z8 : Perm (Fin 8) := SymmetricEightCertificates.p27

/-- The nonidentity permutation of the two-point tail. -/
def z2 : Perm (Fin 2) := tailRow2 1

/-- The central involution `(0 1)(2 3)` of the dihedral four-point tail. -/
def z4 : Perm (Fin 4) := tailRow4 3

/-- Pointwise commutation check for the eight-point factor, in row-major order. -/
def z8CommutationCheck : Bool :=
  (List.finRange 128).all fun i ↦ (List.finRange 8).all fun j ↦
    decide (z8 (SymmetricEightCertificates.rowAt i j) =
      SymmetricEightCertificates.rowAt i (z8 j))

/-- All 128 factor rows commute with the simultaneous sibling flip. -/
theorem z8CommutationCheck_true : z8CommutationCheck = true := by
  decide +kernel

/-- Group commutation follows from the checked pointwise equalities. -/
theorem commute_z8_row (i : Fin 128) : Commute z8 (SymmetricEightCertificates.rowAt i) := by
  change z8 * SymmetricEightCertificates.rowAt i = SymmetricEightCertificates.rowAt i * z8
  apply Equiv.ext
  intro j
  have hi := List.all_eq_true.mp z8CommutationCheck_true i (by simp)
  exact of_decide_eq_true (List.all_eq_true.mp hi j (by simp))

theorem commute_z2_tail : ∀ i : Fin 2, Commute z2 (tailRow2 i) := by
  change ∀ i : Fin 2, z2 * tailRow2 i = tailRow2 i * z2
  decide +kernel

theorem commute_z4_tail : ∀ i : Fin 8, Commute z4 (tailRow4 i) := by
  change ∀ i : Fin 8, z4 * tailRow4 i = tailRow4 i * z4
  decide +kernel

theorem z8_ne_one : z8 ≠ 1 := by decide +kernel
theorem z2_ne_one : z2 ≠ 1 := by decide +kernel
theorem z4_ne_one : z4 ≠ 1 := by decide +kernel

theorem z8_sq : z8 ^ 2 = 1 := by decide +kernel
theorem z2_sq : z2 ^ 2 = 1 := by decide +kernel
theorem z4_sq : z4 ^ 2 = 1 := by decide +kernel

/-- Commutation is preserved by combining the two independent blocks. -/
theorem commute_blockSum_of_factors {a b : ℕ}
    (σ x : Perm (Fin a)) (τ y : Perm (Fin b))
    (hσ : Commute σ x) (hτ : Commute τ y) :
    Commute (finBlockSumPermHom a b (σ, τ)) (finBlockSumPermHom a b (x, y)) := by
  have h : Commute (σ, τ) (x, y) := by
    change (σ * x, τ * y) = (x * σ, y * τ)
    exact Prod.ext hσ.eq hτ.eq
  exact h.map (finBlockSumPermHom a b)

/-- Factorwise commutation controls every product row. -/
theorem commute_rowFromTail_of_factors {b k : ℕ}
    (σ : Perm (Fin 8)) (τ : Perm (Fin b)) (tail : Fin k → Perm (Fin b))
    (hσ : ∀ i, Commute σ (SymmetricEightCertificates.rowAt i))
    (hτ : ∀ j, Commute τ (tail j)) (i : Fin (128 * k)) :
    Commute (finBlockSumPermHom 8 b (σ, τ)) (rowFromTail tail i) :=
  commute_blockSum_of_factors σ _ τ _
    (hσ (finProdFinEquiv.symm i).1) (hτ (finProdFinEquiv.symm i).2)

/-- Centralizers of the factors map into the centralizer of the block product. -/
theorem mem_centralizer_blockProduct_of_factors {a b : ℕ}
    (H : Subgroup (Perm (Fin a))) (K : Subgroup (Perm (Fin b)))
    (σ : Perm (Fin a)) (τ : Perm (Fin b))
    (hσ : σ ∈ Subgroup.centralizer (H : Set (Perm (Fin a))))
    (hτ : τ ∈ Subgroup.centralizer (K : Set (Perm (Fin b)))) :
    finBlockSumPermHom a b (σ, τ) ∈
      Subgroup.centralizer (finBlockProductSubgroup H K : Set (Perm (Fin (a + b)))) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  obtain ⟨x, y, rfl⟩ := (mem_finBlockProductSubgroup_iff H K g).mp hg
  exact (commute_blockSum_of_factors σ x τ y
    ((Subgroup.mem_centralizer_iff.mp hσ x x.property).symm)
    ((Subgroup.mem_centralizer_iff.mp hτ y y.property).symm)).symm.eq

/-- Two involutory factors give an involutory block permutation. -/
theorem blockSum_sq_eq_one {a b : ℕ} (σ : Perm (Fin a)) (τ : Perm (Fin b))
    (hσ : σ ^ 2 = 1) (hτ : τ ^ 2 = 1) :
    finBlockSumPermHom a b (σ, τ) ^ 2 = 1 := by
  rw [← map_pow]
  change finBlockSumPermHom a b (σ ^ 2, τ ^ 2) = 1
  rw [hσ, hτ]
  exact map_one (finBlockSumPermHom a b)

/-- A nonidentity left factor makes the block permutation nonidentity. -/
theorem blockSum_ne_one_of_left {a b : ℕ} (σ : Perm (Fin a)) (τ : Perm (Fin b))
    (hσ : σ ≠ 1) : finBlockSumPermHom a b (σ, τ) ≠ 1 := by
  intro h
  have hpair := finBlockSumPermHom_injective a b
    (h.trans (map_one (finBlockSumPermHom a b)).symm)
  exact hσ (congrArg Prod.fst hpair)

/-- A nonidentity right factor makes the block permutation nonidentity. -/
theorem blockSum_ne_one_of_right {a b : ℕ} (σ : Perm (Fin a)) (τ : Perm (Fin b))
    (hτ : τ ≠ 1) : finBlockSumPermHom a b (σ, τ) ≠ 1 := by
  intro h
  have hpair := finBlockSumPermHom_injective a b
    (h.trans (map_one (finBlockSumPermHom a b)).symm)
  exact hτ (congrArg Prod.snd hpair)

def z9 : Perm (Fin 9) := finBlockSumPermHom 8 1 (z8, 1)
def z10Left : Perm (Fin 10) := finBlockSumPermHom 8 2 (z8, 1)
def z10Right : Perm (Fin 10) := finBlockSumPermHom 8 2 (1, z2)
def z10Both : Perm (Fin 10) := finBlockSumPermHom 8 2 (z8, z2)
def z12Left : Perm (Fin 12) := finBlockSumPermHom 8 4 (z8, 1)
def z12Right : Perm (Fin 12) := finBlockSumPermHom 8 4 (1, z4)
def z12Both : Perm (Fin 12) := finBlockSumPermHom 8 4 (z8, z4)

theorem z10Both_eq_mul : z10Both = z10Left * z10Right := by
  unfold z10Both z10Left z10Right
  rw [← map_mul]
  simp

theorem z12Both_eq_mul : z12Both = z12Left * z12Right := by
  unfold z12Both z12Left z12Right
  rw [← map_mul]
  simp

theorem commute_z9_row (i : Fin 128) : Commute z9 (row9 i) :=
  commute_rowFromTail_of_factors z8 1 tailRow1 commute_z8_row (fun _ ↦ .one_left _) i

theorem commute_z10Left_row (i : Fin 256) : Commute z10Left (row10 i) :=
  commute_rowFromTail_of_factors z8 1 tailRow2 commute_z8_row (fun _ ↦ .one_left _) i

theorem commute_z10Right_row (i : Fin 256) : Commute z10Right (row10 i) :=
  commute_rowFromTail_of_factors 1 z2 tailRow2 (fun _ ↦ .one_left _) commute_z2_tail i

theorem commute_z10Both_row (i : Fin 256) : Commute z10Both (row10 i) :=
  commute_rowFromTail_of_factors z8 z2 tailRow2 commute_z8_row commute_z2_tail i

theorem commute_z12Left_row (i : Fin 1024) : Commute z12Left (row12 i) :=
  commute_rowFromTail_of_factors z8 1 tailRow4 commute_z8_row (fun _ ↦ .one_left _) i

theorem commute_z12Right_row (i : Fin 1024) : Commute z12Right (row12 i) :=
  commute_rowFromTail_of_factors 1 z4 tailRow4 (fun _ ↦ .one_left _) commute_z4_tail i

theorem commute_z12Both_row (i : Fin 1024) : Commute z12Both (row12 i) :=
  commute_rowFromTail_of_factors z8 z4 tailRow4 commute_z8_row commute_z4_tail i

theorem z9_ne_one : z9 ≠ 1 := blockSum_ne_one_of_left _ _ z8_ne_one
theorem z10Left_ne_one : z10Left ≠ 1 := blockSum_ne_one_of_left _ _ z8_ne_one
theorem z10Right_ne_one : z10Right ≠ 1 := blockSum_ne_one_of_right _ _ z2_ne_one
theorem z10Both_ne_one : z10Both ≠ 1 := blockSum_ne_one_of_left _ _ z8_ne_one
theorem z12Left_ne_one : z12Left ≠ 1 := blockSum_ne_one_of_left _ _ z8_ne_one
theorem z12Right_ne_one : z12Right ≠ 1 := blockSum_ne_one_of_right _ _ z4_ne_one
theorem z12Both_ne_one : z12Both ≠ 1 := blockSum_ne_one_of_left _ _ z8_ne_one

theorem z9_sq : z9 ^ 2 = 1 := blockSum_sq_eq_one _ _ z8_sq (one_pow _)
theorem z10Left_sq : z10Left ^ 2 = 1 := blockSum_sq_eq_one _ _ z8_sq (one_pow _)
theorem z10Right_sq : z10Right ^ 2 = 1 := blockSum_sq_eq_one _ _ (one_pow _) z2_sq
theorem z10Both_sq : z10Both ^ 2 = 1 := blockSum_sq_eq_one _ _ z8_sq z2_sq
theorem z12Left_sq : z12Left ^ 2 = 1 := blockSum_sq_eq_one _ _ z8_sq (one_pow _)
theorem z12Right_sq : z12Right ^ 2 = 1 := blockSum_sq_eq_one _ _ (one_pow _) z4_sq
theorem z12Both_sq : z12Both ^ 2 = 1 := blockSum_sq_eq_one _ _ z8_sq z4_sq

theorem z10Left_ne_Right : z10Left ≠ z10Right := by decide +kernel
theorem z10Left_ne_Both : z10Left ≠ z10Both := by decide +kernel
theorem z10Right_ne_Both : z10Right ≠ z10Both := by decide +kernel
theorem z12Left_ne_Right : z12Left ≠ z12Right := by decide +kernel
theorem z12Left_ne_Both : z12Left ≠ z12Both := by decide +kernel
theorem z12Right_ne_Both : z12Right ≠ z12Both := by decide +kernel

/-- Explicit row positions certify membership in the actual row subgroups. -/
theorem z9_eq_row : z9 = row9 27 := by decide +kernel
theorem z10Left_eq_row : z10Left = row10 54 := by decide +kernel
theorem z10Right_eq_row : z10Right = row10 1 := by decide +kernel
theorem z10Both_eq_row : z10Both = row10 55 := by decide +kernel
theorem z12Left_eq_row : z12Left = row12 216 := by decide +kernel
theorem z12Right_eq_row : z12Right = row12 3 := by decide +kernel
theorem z12Both_eq_row : z12Both = row12 219 := by decide +kernel

/-- Rowwise commutation supplies membership in the subgroup centralizer. -/
theorem mem_centralizer_of_row_commute {G : Type*} [Group G]
    (H : Subgroup G) {I : Type*} (row : I → G)
    (hrow : ∀ g, g ∈ H ↔ ∃ i, row i = g) (z : G)
    (hz : ∀ i, Commute z (row i)) : z ∈ Subgroup.centralizer (H : Set G) := by
  apply Subgroup.mem_centralizer_iff.mpr
  intro g hg
  obtain ⟨i, rfl⟩ := (hrow g).mp hg
  exact (hz i).symm.eq

end LisiSabatini.SymmetricDoubleCosetCentralRows
