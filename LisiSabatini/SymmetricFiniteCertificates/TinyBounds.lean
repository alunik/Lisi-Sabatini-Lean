module

public import LisiSabatini.SymmetricFiniteCertificates.SylowTwoWitnesses
public import LisiSabatini.SymmetricFiniteCertificates.OddCosts
public import LisiSabatini.SylowDoubleCosetBound

/-!
# Small symmetric bad-conjugator bounds from tiny certificates

A single good Sylow-two pair gives an entire good double coset, of order
64 in S5 and 256 in S6. The remaining bounds here are exact odd-prime
cycle-profile bounds. Every statement permits independently prescribed rows.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini.SymmetricFiniteCertificates

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem symmetricFive_two_bad_bound
    (P Q : Sylow 2 (Equiv.Perm (Fin 5))) :
    (mixedSylowPairBadConjugators P Q).ncard ≤ 56 := by
  have h := bad_probability_le_of_one_trivial_pair S5Tiny.sylow2
    ⟨S5Tiny.witness, S5Tiny.sylow2_inter_witness_eq_bot⟩ P Q
  rw [S5Tiny.card_sylow2, S5Tiny.group_card] at h
  norm_num at h
  have hreal : ((mixedSylowPairBadConjugators P Q).ncard : ℝ) ≤ 56 := by linarith
  exact_mod_cast hreal

theorem symmetricSix_two_bad_bound
    (P Q : Sylow 2 (Equiv.Perm (Fin 6))) :
    (mixedSylowPairBadConjugators P Q).ncard ≤ 464 := by
  have h := bad_probability_le_of_one_trivial_pair S6Tiny.sylow2
    ⟨S6Tiny.witness, S6Tiny.sylow2_inter_witness_eq_bot⟩ P Q
  rw [S6Tiny.card_sylow2, S6Tiny.group_card] at h
  norm_num at h
  have hreal : ((mixedSylowPairBadConjugators P Q).ncard : ℝ) ≤ 464 := by linarith
  exact_mod_cast hreal

theorem symmetricFive_three_bad_bound
    (P Q : Sylow 3 (Equiv.Perm (Fin 5))) :
    (mixedSylowPairBadConjugators P Q).ncard ≤ 12 := by
  have h := bad_probability_le_cyclic_quadratic_cost P Q
  rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile (by decide) P,
    symmetricProfile_five_three, S5Tiny.group_card] at h
  norm_num at h
  have hreal : ((mixedSylowPairBadConjugators P Q).ncard : ℝ) ≤ 12 := by linarith
  exact_mod_cast hreal

theorem symmetricFive_five_bad_bound
    (P Q : Sylow 5 (Equiv.Perm (Fin 5))) :
    (mixedSylowPairBadConjugators P Q).ncard ≤ 20 := by
  have h := bad_probability_le_cyclic_quadratic_cost P Q
  rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile (by decide) P,
    symmetricProfile_five_five, S5Tiny.group_card] at h
  norm_num at h
  have hreal : ((mixedSylowPairBadConjugators P Q).ncard : ℝ) ≤ 20 := by linarith
  exact_mod_cast hreal

theorem symmetricSix_five_bad_bound
    (P Q : Sylow 5 (Equiv.Perm (Fin 6))) :
    (mixedSylowPairBadConjugators P Q).ncard ≤ 20 := by
  have h := bad_probability_le_cyclic_quadratic_cost P Q
  rw [normalizedSameRowSylowQuadraticCost_perm_eq_profile (by decide) P,
    symmetricProfile_six_five, S6Tiny.group_card] at h
  norm_num at h
  have hreal : ((mixedSylowPairBadConjugators P Q).ncard : ℝ) ≤ 20 := by linarith
  exact_mod_cast hreal

end LisiSabatini.SymmetricFiniteCertificates
