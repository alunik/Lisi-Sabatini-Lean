module

public import LisiSabatini.CommonTranslateCore
public import Mathlib.Data.Finite.Prod
public import Mathlib.LinearAlgebra.Pi

/-!
# Repeated-block amplification of fixed-point bounds

Let `H` be a linear group on a module `W`.  This file considers the diagonal
copy of `H` on a repeated block `I → W`: the same element of `H` acts on
every coordinate.  A vector in the repeated block can be nonregular only if
all of its coordinates are fixed by one common nonidentity element of `H`.

Consequently, if every nonidentity element of `H` fixes at most `b` vectors
of `W`, the diagonal copy has at most

`(|H| - 1) * b ^ |I|`

nonregular vectors.  In particular, passing from one block to `m` repeated
blocks raises each elementwise fixed-point bound to its `m`th power.  The
results are stated for an arbitrary finite index type and specialized to
`Fin m` at the end.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommMonoid W] [Module R W]

/-- The vectors fixed by a specified general-linear element. -/
abbrev fixedVectorSet
    (g : LinearMap.GeneralLinearGroup R W) : Set W :=
  MulAction.fixedBy W g

@[simp]
theorem mem_fixedVectorSet
    (g : LinearMap.GeneralLinearGroup R W) (w : W) :
    w ∈ fixedVectorSet g ↔ g • w = w :=
  Iff.rfl

/-- The coordinatewise diagonal action of a general-linear element on a
repeated block. -/
def diagonalGeneralLinear (I : Type uI) :
    LinearMap.GeneralLinearGroup R W →*
      LinearMap.GeneralLinearGroup R (I → W) where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (LinearEquiv.piCongrRight fun _ ↦ g.toLinearEquiv)
  map_one' := by
    ext x i
    rfl
  map_mul' g h := by
    ext x i
    rfl

@[simp]
theorem diagonalGeneralLinear_apply
    (g : LinearMap.GeneralLinearGroup R W) (x : I → W) (i : I) :
    (diagonalGeneralLinear (R := R) I g • x) i = g • x i :=
  rfl

/-- The diagonal copy of `H` on the repeated block `I → W`. -/
def diagonalLinearSubgroup
    (I : Type uI) (H : Subgroup (LinearMap.GeneralLinearGroup R W)) :
    Subgroup (LinearMap.GeneralLinearGroup R (I → W)) :=
  H.map (diagonalGeneralLinear (R := R) I)

/-- The repeated-block fixed set of `g`: every coordinate is fixed by the
same element. -/
def repeatedFixedVectors
    (I : Type uI) (g : LinearMap.GeneralLinearGroup R W) : Set (I → W) :=
  {x | ∀ i, x i ∈ fixedVectorSet g}

@[simp]
theorem mem_repeatedFixedVectors
    (g : LinearMap.GeneralLinearGroup R W) (x : I → W) :
    x ∈ repeatedFixedVectors I g ↔ ∀ i, g • x i = x i :=
  Iff.rfl

/-- Coordinatewise choice identifies the fixed set on a repeated block with
a power of the fixed set on one block. -/
def repeatedFixedVectorsEquiv
    (I : Type uI) (g : LinearMap.GeneralLinearGroup R W) :
    {x : I → W // x ∈ repeatedFixedVectors I g} ≃
      (I → {w : W // w ∈ fixedVectorSet g}) where
  toFun x i := ⟨x.1 i, x.2 i⟩
  invFun x := ⟨fun i ↦ (x i).1, fun i ↦ (x i).2⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv x := by
    funext i
    rfl

/-- Exact amplification: the fixed set of `g` on `I → W` has cardinality
the `|I|`th power of its fixed-set cardinality on `W`. -/
theorem ncard_repeatedFixedVectors
    [Fintype I] [Finite W]
    (g : LinearMap.GeneralLinearGroup R W) :
    (repeatedFixedVectors I g).ncard =
      (fixedVectorSet g).ncard ^ Fintype.card I := by
  calc
    (repeatedFixedVectors I g).ncard =
        Nat.card {x : I → W // x ∈ repeatedFixedVectors I g} :=
      (Nat.card_coe_set_eq _).symm
    _ = Nat.card (I → {w : W // w ∈ fixedVectorSet g}) :=
      Nat.card_congr (repeatedFixedVectorsEquiv I g)
    _ = Nat.card {w : W // w ∈ fixedVectorSet g} ^ Nat.card I :=
      Nat.card_fun
    _ = (fixedVectorSet g).ncard ^ Nat.card I := by
      rw [Nat.card_coe_set_eq]
    _ = (fixedVectorSet g).ncard ^ Fintype.card I := by
      rw [Nat.card_eq_fintype_card]

/-- The union of the repeated fixed sets of the nonidentity elements of `H`.
This is the natural elementwise envelope for the nonregular locus of the
diagonal copy. -/
def repeatedBlockBadEnvelope
    (I : Type uI) (H : Subgroup (LinearMap.GeneralLinearGroup R W)) :
    Set (I → W) :=
  ⋃ h : {h : H // h ≠ 1}, repeatedFixedVectors I h.1.1

/-- The finite set of nonidentity elements of a finite subgroup. -/
noncomputable def nonidentityElements
    (H : Subgroup (LinearMap.GeneralLinearGroup R W)) [Fintype H] : Finset H := by
  classical
  exact Finset.univ.erase 1

@[simp]
theorem mem_nonidentityElements
    (H : Subgroup (LinearMap.GeneralLinearGroup R W)) [Fintype H]
    (h : H) :
    h ∈ nonidentityElements H ↔ h ≠ 1 := by
  classical
  simp [nonidentityElements]

@[simp]
theorem card_nonidentityElements
    (H : Subgroup (LinearMap.GeneralLinearGroup R W)) [Fintype H] :
    (nonidentityElements H).card = Fintype.card H - 1 := by
  classical
  simp [nonidentityElements]

/-- Every nonregular vector for the diagonal copy of `H` is fixed in every
coordinate by one common nonidentity element of `H`. -/
theorem nonregularVectors_diagonalLinearSubgroup_subset_badEnvelope
    (I : Type uI) (H : Subgroup (LinearMap.GeneralLinearGroup R W)) :
    nonregularVectors (diagonalLinearSubgroup I H) ⊆
      repeatedBlockBadEnvelope I H := by
  intro x hx
  obtain ⟨a, ha_ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hx
  obtain ⟨g, hgH, hga⟩ := a.1.2
  let gH : H := ⟨g, hgH⟩
  have hgH_ne : gH ≠ 1 := by
    intro hg
    apply ha_ne
    apply Subtype.ext
    apply Subtype.ext
    rw [← hga]
    have hg' : g = 1 := congrArg Subtype.val hg
    simp [hg']
  apply Set.mem_iUnion.mpr
  refine ⟨⟨gH, hgH_ne⟩, ?_⟩
  intro i
  have hfix := a.2
  change a.1.1 • x = x at hfix
  rw [← hga] at hfix
  exact congrFun hfix i

/-- Union-bound form before inserting a uniform elementwise estimate. -/
theorem ncard_nonregularVectors_diagonalLinearSubgroup_le_sum
    [Fintype I] [Finite W]
    (H : Subgroup (LinearMap.GeneralLinearGroup R W)) [Fintype H] :
    (nonregularVectors (diagonalLinearSubgroup I H)).ncard ≤
      ∑ h ∈ nonidentityElements H,
        (fixedVectorSet h.1).ncard ^ Fintype.card I := by
  classical
  let : Fintype {h : H // h ≠ 1} := Fintype.ofFinite _
  calc
    _ ≤ (repeatedBlockBadEnvelope I H).ncard :=
      Set.ncard_le_ncard
        (nonregularVectors_diagonalLinearSubgroup_subset_badEnvelope I H)
        (Set.toFinite _)
    _ ≤ ∑ h : {h : H // h ≠ 1},
          (repeatedFixedVectors I h.1.1).ncard := by
      exact Set.ncard_iUnion_le_of_fintype _
    _ = ∑ h : {h : H // h ≠ 1},
          (fixedVectorSet h.1.1).ncard ^ Fintype.card I := by
      apply Finset.sum_congr rfl
      intro h _hh
      exact ncard_repeatedFixedVectors h.1.1
    _ = ∑ h ∈ nonidentityElements H,
          (fixedVectorSet h.1).ncard ^ Fintype.card I := by
      rw [nonidentityElements, ← Finset.filter_ne',
        ← Finset.sum_subtype_eq_sum_filter]
      simp

/-- Repeated-block amplification of a uniform elementwise fixed-point bound.
The factor `|H| - 1` counts the possible nonidentity stabilizing elements. -/
theorem ncard_nonregularVectors_diagonalLinearSubgroup_le
    [Fintype I] [Finite W]
    (H : Subgroup (LinearMap.GeneralLinearGroup R W)) [Fintype H]
    (b : ℕ)
    (hfixed : ∀ h : H, h ≠ 1 → (fixedVectorSet h.1).ncard ≤ b) :
    (nonregularVectors (diagonalLinearSubgroup I H)).ncard ≤
      (Fintype.card H - 1) * b ^ Fintype.card I := by
  classical
  calc
    _ ≤ ∑ h ∈ nonidentityElements H,
          (fixedVectorSet h.1).ncard ^ Fintype.card I :=
      ncard_nonregularVectors_diagonalLinearSubgroup_le_sum H
    _ ≤ ∑ _h ∈ nonidentityElements H,
          b ^ Fintype.card I := by
      apply Finset.sum_le_sum
      intro h _hh
      exact Nat.pow_le_pow_left
        (hfixed h (mem_nonidentityElements H h |>.mp _hh)) _
    _ = (nonidentityElements H).card * b ^ Fintype.card I := by
      rw [Finset.sum_const, Nat.nsmul_eq_mul]
    _ = _ := by
      rw [card_nonidentityElements]

/-- The concrete `m`-fold version used for repeated finite-dimensional
blocks. -/
theorem ncard_nonregularVectors_diagonalFinSubgroup_le
    [Finite W]
    (m : ℕ) (H : Subgroup (LinearMap.GeneralLinearGroup R W)) [Fintype H]
    (b : ℕ)
    (hfixed : ∀ h : H, h ≠ 1 → (fixedVectorSet h.1).ncard ≤ b) :
    (nonregularVectors (diagonalLinearSubgroup (Fin m) H)).ncard ≤
      (Fintype.card H - 1) * b ^ m := by
  simpa using
    ncard_nonregularVectors_diagonalLinearSubgroup_le
      (I := Fin m) H b hfixed

end LisiSabatini
