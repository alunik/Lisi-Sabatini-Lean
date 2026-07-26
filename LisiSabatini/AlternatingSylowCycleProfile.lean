import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.GroupTheory.Perm.Centralizer
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Exact Sylow cycle profiles for symmetric and alternating groups

This file contains the arithmetic core of the Sylow cycle-profile
calculation.  If `W k` is the standard Sylow `p`-subgroup on `p ^ k`
letters and `A k` records elements of order dividing `p` according to
their number of `p`-cycles, then

`A (k + 1) = A k ^ p + (p - 1) * |W k| ^ (p - 1) * X ^ (p ^ k)`.

The first term records elements with trivial top permutation in the
regular wreath product.  For a nontrivial top permutation, the product
of the base components must be one; this leaves `|W k| ^ (p - 1)`
choices, all with `p ^ k` cycles of length `p`.

Multiplying these tower profiles according to the base-`p` digits of
`n` gives the profile for the standard Sylow subgroup of `S_n`.  The
group-theoretic identification of profile coefficients with actual
Sylow/class intersections is deliberately kept out of this arithmetic
module.
-/

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

set_option maxRecDepth 100000

/-! ## Tower and base-`p` profiles -/

/-- Order of the standard iterated Sylow `p`-subgroup on `p ^ k`
letters. -/
def sylowTowerOrder (p : ℕ) : ℕ → ℕ
  | 0 => 1
  | k + 1 => p * (sylowTowerOrder p k) ^ p

/-- Cycle-profile polynomial for the elements of order dividing `p` in
the standard iterated Sylow subgroup on `p ^ k` letters.  The constant
coefficient counts the identity. -/
def sylowTowerCycleProfile (p : ℕ) : ℕ → Polynomial ℕ
  | 0 => 1
  | k + 1 =>
      sylowTowerCycleProfile p k ^ p +
        Polynomial.C
            ((p - 1) * (sylowTowerOrder p k) ^ (p - 1)) *
          Polynomial.X ^ (p ^ k)

@[simp]
theorem sylowTowerOrder_zero (p : ℕ) :
    sylowTowerOrder p 0 = 1 :=
  rfl

@[simp]
theorem sylowTowerOrder_succ (p k : ℕ) :
    sylowTowerOrder p (k + 1) =
      p * (sylowTowerOrder p k) ^ p :=
  rfl

@[simp]
theorem sylowTowerCycleProfile_zero (p : ℕ) :
    sylowTowerCycleProfile p 0 = 1 :=
  rfl

/-- The exact regular-wreath-product recurrence. -/
theorem sylowTowerCycleProfile_succ (p k : ℕ) :
    sylowTowerCycleProfile p (k + 1) =
      sylowTowerCycleProfile p k ^ p +
        Polynomial.C
            ((p - 1) * (sylowTowerOrder p k) ^ (p - 1)) *
          Polynomial.X ^ (p ^ k) :=
  rfl

/-- The base-`p` digit of `n` in place `k`. -/
def basePDigit (n p k : ℕ) : ℕ :=
  n / p ^ k % p

/-- The exact cycle-profile polynomial obtained by multiplying the
tower profiles selected by the base-`p` digits of `n`.

The range `n + 1` is deliberately redundant.  For prime `p`, every
later digit is zero, while this formulation remains executable without
choosing a logarithm convention at `n = 0`. -/
def sylowCycleProfile (n p : ℕ) : Polynomial ℕ :=
  ∏ k ∈ Finset.range (n + 1),
    if basePDigit n p k = 0 then 1
    else sylowTowerCycleProfile p k ^ basePDigit n p k

/-! ## Prime-cycle classes and normalized quadratic costs -/

/-- Number of elements in the `S_n` conjugacy class of cycle type
`p ^ j 1 ^ (n - p * j)`. -/
def primeCycleClassCard (n p j : ℕ) : ℕ :=
  n.factorial /
    (p ^ j * j.factorial * (n - p * j).factorial)

/-- Permutations of cycle type `p ^ j 1 ^ (n - p * j)`. -/
def primeCycleTypeFinset (n p j : ℕ) :
    Finset (Equiv.Perm (Fin n)) :=
  Finset.univ.filter fun g ↦
    g.cycleType = Multiset.replicate j p

/-- Mathlib's general cycle-type formula gives the class cardinality
used in the quadratic cost. -/
theorem card_primeCycleTypeFinset
    {n p j : ℕ} (hp : 2 ≤ p) (hj : 0 < j) (hjn : p * j ≤ n) :
    (primeCycleTypeFinset n p j).card =
      primeCycleClassCard n p j := by
  classical
  have hvalid :
      (Multiset.replicate j p).sum ≤ Fintype.card (Fin n) ∧
        ∀ a ∈ Multiset.replicate j p, 2 ≤ a := by
    constructor
    · simpa [Nat.mul_comm] using hjn
    · intro a ha
      simpa [Multiset.eq_of_mem_replicate ha] using hp
  rw [primeCycleTypeFinset,
    Equiv.Perm.card_of_cycleType, if_pos hvalid]
  simp [primeCycleClassCard, hj.ne', Nat.mul_comm,
    Nat.mul_left_comm, Nat.mul_assoc]

/-- The exact normalized quadratic class-sum cost read from the
cycle-profile recurrence for `S_n`. -/
def symmetricSylowProfileQuadraticCost (n p : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 (n / p),
    (sylowCycleProfile n p).coeff j ^ 2 /
      (primeCycleClassCard n p j : ℝ)

/-- The corresponding profile cost for `A_n`.

At `p = 2`, only cycle types with an even number of transpositions lie
in the alternating group.  At odd primes every `p`-cycle is even, so
the arithmetic value is the symmetric-group value. -/
def alternatingSylowProfileQuadraticCost (n p : ℕ) : ℝ :=
  if p = 2 then
    ∑ j ∈ Finset.Icc 1 (n / 2),
      if Even j then
        (sylowCycleProfile n 2).coeff j ^ 2 /
          (primeCycleClassCard n 2 j : ℝ)
      else 0
  else
    symmetricSylowProfileQuadraticCost n p

/-- Removing the odd-transposition rows can only decrease the
quadratic cost. -/
theorem alternatingSylowProfileQuadraticCost_le_symmetric
    (n p : ℕ) :
    alternatingSylowProfileQuadraticCost n p ≤
      symmetricSylowProfileQuadraticCost n p := by
  by_cases hp : p = 2
  · subst p
    rw [alternatingSylowProfileQuadraticCost, if_pos rfl]
    rw [symmetricSylowProfileQuadraticCost]
    apply Finset.sum_le_sum
    intro j _hj
    split_ifs
    · exact le_rfl
    · positivity
  · simp [alternatingSylowProfileQuadraticCost, hp]

end LisiSabatini
