import LisiSabatini.RepeatedBlockAmplification
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FixedSubmodule

/-!
# Fixed-space codimension bounds over prime fields

For a linear automorphism `g`, its fixed vectors form the kernel of the
displacement map `g - 1`.  Over the prime field `ZMod r`, this identifies
the exact number of fixed vectors with

`r ^ finrank (fixedSpace g)`.

Rank-nullity then turns a lower bound `c` on the rank of `g - 1` (equivalently,
on the codimension of its fixed space) into the uniform estimate

`|Fix(g)| ≤ r ^ (d - c)`

on `Fin d → ZMod r`.  The final results package this estimate for every
nonidentity element of a subgroup and feed it directly into repeated-block
amplification.
-/

noncomputable section

namespace LisiSabatini

universe uK uV

/-! ## The fixed space as a kernel -/

/-- The displacement linear map `g - 1`.  Its kernel is the fixed space of
`g`. -/
abbrev fixedDifferenceLinearMap
    {K : Type uK} {V : Type uV}
    [Semiring K] [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V :=
  g.toLinearEquiv.toLinearMap - LinearMap.id

/-- The linear subspace fixed pointwise by `g`.

This public compatibility spelling remains kernel-reducible because rank
arguments use the range of the same displacement map.  The theorem below
identifies it with mathlib's canonical `LinearMap.fixedSubmodule`. -/
abbrev fixedSpace
    {K : Type uK} {V : Type uV}
    [Semiring K] [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) : Submodule K V :=
  (fixedDifferenceLinearMap g).ker

/-- The project fixed-space spelling is mathlib's canonical fixed submodule. -/
theorem fixedSpace_eq_fixedSubmodule
    {K : Type uK} {V : Type uV}
    [Ring K] [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) :
    fixedSpace g = g.toLinearEquiv.toLinearMap.fixedSubmodule := by
  exact (LinearMap.fixedSubmodule_eq_ker
    g.toLinearEquiv.toLinearMap).symm

/-- The set-theoretic fixed vectors used by repeated-block amplification are
exactly the underlying set of the kernel of `g - 1`. -/
theorem fixedVectorSet_eq_fixedSpace
    {K : Type uK} {V : Type uV}
    [Semiring K] [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) :
    fixedVectorSet g = (fixedSpace g : Set V) := by
  ext v
  change g • v = v ↔ fixedDifferenceLinearMap g v = 0
  rw [Units.smul_def]
  change (g : V →ₗ[K] V) v = v ↔ _
  simp [fixedDifferenceLinearMap, sub_eq_zero]

/-- The identity-on-vectors equivalence between the subtype of fixed vectors
and the fixed subspace. -/
def fixedVectorSubtypeEquivFixedSpace
    {K : Type uK} {V : Type uV}
    [Semiring K] [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) :
    {v : V // v ∈ fixedVectorSet g} ≃ fixedSpace g :=
  Equiv.setCongr (fixedVectorSet_eq_fixedSpace g)

/-! ## Exact cardinality over `ZMod r` -/

/-- Over a prime field, the number of fixed vectors is exactly the field
cardinality raised to the dimension of the fixed subspace. -/
theorem ncard_fixedVectorSet_eq_pow_finrank_fixedSpace_zmod
    {r : ℕ} [Fact (Nat.Prime r)]
    {V : Type uV} [AddCommGroup V] [Module (ZMod r) V]
    [Module.Finite (ZMod r) V]
    (g : LinearMap.GeneralLinearGroup (ZMod r) V) :
    (fixedVectorSet g).ncard =
      r ^ Module.finrank (ZMod r) (fixedSpace g) := by
  calc
    (fixedVectorSet g).ncard =
        Nat.card {v : V // v ∈ fixedVectorSet g} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card (fixedSpace g) :=
      Nat.card_congr (fixedVectorSubtypeEquivFixedSpace g)
    _ = r ^ Module.finrank (ZMod r) (fixedSpace g) := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank
          (K := ZMod r) (V := fixedSpace g))

/-! ## Codimension and rank -/

/-- The codimension of the fixed subspace. -/
def fixedSpaceCodimension
    {K : Type uK} {V : Type uV}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) : ℕ :=
  Module.finrank K V - Module.finrank K (fixedSpace g)

/-- Rank-nullity identifies fixed-space codimension with the rank of `g - 1`.
-/
theorem fixedSpaceCodimension_eq_finrank_range
    {K : Type uK} {V : Type uV}
    [DivisionRing K] [AddCommGroup V] [Module K V]
    [Module.Finite K V]
    (g : LinearMap.GeneralLinearGroup K V) :
    fixedSpaceCodimension g =
      Module.finrank K (fixedDifferenceLinearMap g).range := by
  have hrankNullity :=
    (fixedDifferenceLinearMap g).finrank_range_add_finrank_ker
  unfold fixedSpaceCodimension fixedSpace
  omega

/-- A rank lower bound for `g - 1` gives a fixed-vector bound on the standard
`d`-dimensional prime-field module. -/
theorem ncard_fixedVectorSet_le_pow_sub_of_finrank_range
    {r d c : ℕ} [Fact (Nat.Prime r)]
    (g : LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))
    (hrank : c ≤ Module.finrank (ZMod r)
      (fixedDifferenceLinearMap g).range) :
    (fixedVectorSet g).ncard ≤ r ^ (d - c) := by
  rw [ncard_fixedVectorSet_eq_pow_finrank_fixedSpace_zmod]
  apply Nat.pow_le_pow_right ((Fact.out : Nat.Prime r).pos)
  have hrankNullity :=
    (fixedDifferenceLinearMap g).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hrankNullity
  change Module.finrank (ZMod r) (fixedDifferenceLinearMap g).ker ≤ d - c
  omega

/-- Equivalent codimension form of
`ncard_fixedVectorSet_le_pow_sub_of_finrank_range`. -/
theorem ncard_fixedVectorSet_le_pow_sub_of_fixedSpaceCodimension
    {r d c : ℕ} [Fact (Nat.Prime r)]
    (g : LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))
    (hcodim : c ≤ fixedSpaceCodimension g) :
    (fixedVectorSet g).ncard ≤ r ^ (d - c) := by
  apply ncard_fixedVectorSet_le_pow_sub_of_finrank_range g
  rwa [fixedSpaceCodimension_eq_finrank_range] at hcodim

/-! ## Uniform subgroup and repeated-block forms -/

/-- A uniform rank lower bound for all nonidentity subgroup elements produces
exactly the `hfixed` estimate expected by repeated-block amplification. -/
theorem uniform_fixedVectorSet_ncard_le_pow_sub_of_finrank_range
    {r d c : ℕ} [Fact (Nat.Prime r)]
    (H : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r)))
    (hrank : ∀ h : H, h ≠ 1 →
      c ≤ Module.finrank (ZMod r)
        (fixedDifferenceLinearMap h.1).range) :
    ∀ h : H, h ≠ 1 →
      (fixedVectorSet h.1).ncard ≤ r ^ (d - c) := by
  intro h hh
  exact ncard_fixedVectorSet_le_pow_sub_of_finrank_range h.1 (hrank h hh)

/-- Uniform codimension version of the subgroup fixed-vector estimate. -/
theorem uniform_fixedVectorSet_ncard_le_pow_sub_of_fixedSpaceCodimension
    {r d c : ℕ} [Fact (Nat.Prime r)]
    (H : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r)))
    (hcodim : ∀ h : H, h ≠ 1 → c ≤ fixedSpaceCodimension h.1) :
    ∀ h : H, h ≠ 1 →
      (fixedVectorSet h.1).ncard ≤ r ^ (d - c) := by
  intro h hh
  exact ncard_fixedVectorSet_le_pow_sub_of_fixedSpaceCodimension h.1
    (hcodim h hh)

/-- Repeated-block amplification with a uniform rank lower bound substituted
for the elementwise fixed-set hypothesis. -/
theorem ncard_nonregularVectors_diagonalLinearSubgroup_le_of_finrank_range
    {I : Type*} [Fintype I]
    {r d c : ℕ} [Fact (Nat.Prime r)]
    (H : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))) [Fintype H]
    (hrank : ∀ h : H, h ≠ 1 →
      c ≤ Module.finrank (ZMod r)
        (fixedDifferenceLinearMap h.1).range) :
    (nonregularVectors (diagonalLinearSubgroup I H)).ncard ≤
      (Fintype.card H - 1) *
        (r ^ (d - c)) ^ Fintype.card I := by
  exact ncard_nonregularVectors_diagonalLinearSubgroup_le H
    (r ^ (d - c))
    (uniform_fixedVectorSet_ncard_le_pow_sub_of_finrank_range H hrank)

/-- Concrete `m`-fold version of the rank-codimension amplification bound. -/
theorem ncard_nonregularVectors_diagonalFinSubgroup_le_of_finrank_range
    {r d c : ℕ} [Fact (Nat.Prime r)]
    (m : ℕ)
    (H : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))) [Fintype H]
    (hrank : ∀ h : H, h ≠ 1 →
      c ≤ Module.finrank (ZMod r)
        (fixedDifferenceLinearMap h.1).range) :
    (nonregularVectors (diagonalLinearSubgroup (Fin m) H)).ncard ≤
      (Fintype.card H - 1) * (r ^ (d - c)) ^ m := by
  simpa using
    ncard_nonregularVectors_diagonalLinearSubgroup_le_of_finrank_range
      (I := Fin m) H hrank

end LisiSabatini
