module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Even dimension of nondegenerate alternating spaces

This file isolates the determinant argument used by the intrinsic
extraspecial-group development: over a field of characteristic different
from two, a finite-dimensional nondegenerate alternating bilinear space has
even dimension.
-/

@[expose] public section

noncomputable section

open Matrix

namespace LisiSabatini

/-- In an odd prime field, the scalar two is nonzero. -/
theorem two_ne_zero_zmod_of_prime_ne_two {p : ℕ}
    (hp : Nat.Prime p) (hpTwo : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hzero
  rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hpOne | hpEq
  · exact hp.ne_one hpOne
  · exact hpTwo hpEq

/-- A nondegenerate alternating bilinear form on a finitely based module over
an integral commutative ring has an even number of basis vectors when two is
nonzero.  Stating the determinant core with a supplied basis avoids any
field-instance diamonds. -/
theorem even_card_basis_of_nondegenerate_alternating
    {k V ι : Type*} [CommRing k] [IsDomain k]
    [AddCommGroup V] [Module k V] [Fintype ι]
    (h2 : (2 : k) ≠ 0)
    (B : LinearMap.BilinForm k V)
    (halt : B.IsAlt) (hnd : B.Nondegenerate)
    (b : Module.Basis ι k V) : Even (Fintype.card ι) := by
  classical
  let A : Matrix ι ι k := LinearMap.BilinForm.toMatrix b B
  have hskew : Aᵀ = -A := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, A,
      LinearMap.BilinForm.toMatrix_apply]
    exact (halt.neg_eq (b i) (b j)).symm
  have hdet_ne : A.det ≠ 0 := by
    exact Matrix.nondegenerate_iff_det_ne_zero.mp (hnd.toMatrix b)
  by_contra heven
  have hodd : Odd (Fintype.card ι) :=
    Nat.not_even_iff_odd.mp heven
  have hdet : A.det = -A.det := by
    calc
      A.det = Aᵀ.det := (Matrix.det_transpose A).symm
      _ = (-A).det := congrArg Matrix.det hskew
      _ = (-1 : k) ^ Fintype.card ι * A.det := Matrix.det_neg A
      _ = -A.det := by rw [hodd.neg_one_pow]; simp
  have hadd : A.det + A.det = 0 := by
    nth_rewrite 1 [hdet]
    exact neg_add_cancel A.det
  have hmul : (2 : k) * A.det = 0 := by
    simpa [two_mul] using hadd
  exact hdet_ne ((mul_eq_zero.mp hmul).resolve_left h2)

/-- A finite-dimensional space carrying a nondegenerate alternating bilinear
form over a field of characteristic different from two has even dimension. -/
theorem even_finrank_of_nondegenerate_alternating
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0)
    (B : LinearMap.BilinForm k V)
    (halt : B.IsAlt) (hnd : B.Nondegenerate) :
    Even (Module.finrank k V) := by
  simpa using even_card_basis_of_nondegenerate_alternating
    h2 B halt hnd (Module.finBasis k V)

/-- Cardinal form of `even_finrank_of_nondegenerate_alternating` over a
finite field: the underlying space has square field-power cardinality. -/
theorem exists_natCard_eq_pow_two_mul_of_nondegenerate_alternating
    {k V : Type*} [Field k] [Finite k] [AddCommGroup V] [Module k V]
    [Finite V] [FiniteDimensional k V]
    (h2 : (2 : k) ≠ 0)
    (B : LinearMap.BilinForm k V)
    (halt : B.IsAlt) (hnd : B.Nondegenerate) :
    ∃ n : ℕ, Nat.card V = Nat.card k ^ (2 * n) := by
  obtain ⟨n, hn⟩ := even_finrank_of_nondegenerate_alternating
    h2 B halt hnd
  refine ⟨n, ?_⟩
  rw [Module.natCard_eq_pow_finrank (K := k) (V := V), hn]
  congr 1
  omega

end LisiSabatini
