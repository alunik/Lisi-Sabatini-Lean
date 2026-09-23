module

public import LisiSabatini.AlternatingSylowQuadraticFormula
public import LisiSabatini.CyclicSylowQuadraticBound
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Exact odd-prime costs for the tiny symmetric certificates

Only three linear Sylow cycle polynomials are needed. These exact
arithmetic facts apply to arbitrary prescribed mixed Sylow rows.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini.SymmetricFiniteCertificates

private theorem profile_five_three :
    sylowCycleProfile 5 3 = 1 + Polynomial.C 2 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem profile_five_five :
    sylowCycleProfile 5 5 = 1 + Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

private theorem profile_six_five :
    sylowCycleProfile 6 5 = 1 + Polynomial.C 4 * Polynomial.X := by
  norm_num [sylowCycleProfile, Finset.prod_range_succ, basePDigit]
  norm_num [sylowTowerCycleProfile, sylowTowerOrder]

theorem symmetricProfile_five_three : symmetricSylowProfileQuadraticCost 5 3 = 1 / 5 := by
  norm_num [symmetricSylowProfileQuadraticCost, profile_five_three,
    primeCycleClassCard, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_one, Polynomial.coeff_X, Nat.factorial]

theorem symmetricProfile_five_five : symmetricSylowProfileQuadraticCost 5 5 = 2 / 3 := by
  norm_num [symmetricSylowProfileQuadraticCost, profile_five_five,
    primeCycleClassCard, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_one, Polynomial.coeff_X, Nat.factorial]

theorem symmetricProfile_six_five : symmetricSylowProfileQuadraticCost 6 5 = 1 / 9 := by
  norm_num [symmetricSylowProfileQuadraticCost, profile_six_five,
    primeCycleClassCard, Polynomial.coeff_add, Polynomial.coeff_C_mul,
    Polynomial.coeff_one, Polynomial.coeff_X, Nat.factorial]

end LisiSabatini.SymmetricFiniteCertificates
