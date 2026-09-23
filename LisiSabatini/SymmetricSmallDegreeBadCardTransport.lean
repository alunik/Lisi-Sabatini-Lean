module

public import LisiSabatini.CyclicSylowQuadraticBound
public import LisiSabatini.SylowCoreAttainment

/-!
# Independence of the full bad-set cardinality from the Sylow rows

Uniform sampling in the full group permits two independent row changes:
right multiplication absorbs the second Sylow row, and conjugation changes
the first. This statement is for the full group, rather than an arbitrary
conjugacy-invariant sampling class.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

variable {G : Type*} [Group G]

/-- Absorb a conjugation of the second row by right multiplication. -/
theorem mixedSylowInter_smul_right {p : ℕ} (P Q : Sylow p G) (a x : G) :
    mixedSylowInter P (a • Q) x = mixedSylowInter P Q (x * a) := by
  simp only [mixedSylowInter, mul_smul]

/-- The cardinality of the full bad set is independent of its second row. -/
theorem ncard_mixed_bad_eq_same_row {p : ℕ} [Fact p.Prime] [Finite G]
    (P Q : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard =
      (mixedSylowPairBadConjugators P P).ncard := by
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P Q
  subst Q
  apply Set.ncard_congr'
  apply (Equiv.mulRight a).subtypeEquiv
  intro x
  change mixedSylowInter P (a • P) x ≠ ⊥ ↔ mixedSylowInter P P (x * a) ≠ ⊥
  rw [mixedSylowInter_smul_right]

/-- Conjugation transports the full same-row bad set bijectively. -/
theorem ncard_same_row_bad_eq_of_smul {p : ℕ} (P : Sylow p G) (a : G) :
    (mixedSylowPairBadConjugators P P).ncard =
      (mixedSylowPairBadConjugators (a • P) (a • P)).ncard := by
  apply Set.ncard_congr'
  apply (MulAut.conj a).toEquiv.subtypeEquiv
  intro x
  change sylowInter P x ≠ ⊥ ↔ sylowInter (a • P) (a * x * a⁻¹) ≠ ⊥
  rw [sylowInter_smul_conjugate]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective _
    (MulAut.conj a).injective)).symm

/-- Exact row independence of full-group pair failure. -/
theorem ncard_mixed_bad_eq_reference {p : ℕ} [Fact p.Prime] [Finite G]
    (P Q S : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard =
      (mixedSylowPairBadConjugators S S).ncard := by
  rw [ncard_mixed_bad_eq_same_row]
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P S
  subst S
  exact ncard_same_row_bad_eq_of_smul P a

end LisiSabatini
