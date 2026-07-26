import LisiSabatini.AlternatingSylowCycleProfile
import Mathlib.GroupTheory.Perm.Cycle.PossibleTypes
import Mathlib.GroupTheory.Sylow

/-!
# From Sylow cycle-profile coefficients to symmetric-group rows

This file isolates the group-theoretic interface consumed by the
canonical base-`p` block construction.  A row is the intersection of a
Sylow subgroup of `S_n` with one prime-cycle type, and
`HasSymmetricSylowCycleProfileCoefficients` says that a single Sylow
subgroup realizes all coefficients of the arithmetic profile.
-/

noncomputable section

open scoped BigOperators

namespace LisiSabatini

local instance alternatingCoefficientDecidableIsConj
    (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

/-- The intersection of a Sylow row with the cycle type
`p^j 1^(n-pj)`. -/
def primeCycleTypeSylowRow
    (n p j : ℕ) (P : Sylow p (Equiv.Perm (Fin n))) :
    Finset (Equiv.Perm (Fin n)) := by
  classical
  exact (primeCycleTypeFinset n p j).filter fun g ↦ g ∈ P

/-- The exact coefficient statement supplied by the canonical
Sylow-wreath-product support calculation. -/
def HasSymmetricSylowCycleProfileCoefficients
    (n p : ℕ) : Prop :=
  ∃ P : Sylow p (Equiv.Perm (Fin n)),
    ∀ j ∈ Finset.Icc 1 (n / p),
      (primeCycleTypeSylowRow n p j P).card =
        (sylowCycleProfile n p).coeff j

/-- Validity condition for the cycle type `p^j`. -/
def IsValidPrimeCycleType (n p j : ℕ) : Prop :=
  (Multiset.replicate j p).sum ≤ n ∧
    ∀ a ∈ Multiset.replicate j p, 2 ≤ a

theorem isValidPrimeCycleType_of_prime
    {n p j : ℕ} (hp : p.Prime) (hpj : p * j ≤ n) :
    IsValidPrimeCycleType n p j := by
  constructor
  · simpa [Nat.mul_comm] using hpj
  · intro a ha
    simpa [Multiset.eq_of_mem_replicate ha] using hp.two_le

/-- A canonical conjugacy-class label of cycle type
`p^j 1^(n-pj)`.  Outside the valid range it is harmlessly set to the
identity class. -/
def primeCycleTypeClass (n p j : ℕ) :
    ConjClasses (Equiv.Perm (Fin n)) := by
  classical
  exact
    if h : IsValidPrimeCycleType n p j then
      ConjClasses.mk
        (Classical.choose
          ((Equiv.Perm.exists_with_cycleType_iff
            (α := Fin n)
            (m := Multiset.replicate j p)).mpr
              (by simpa [IsValidPrimeCycleType] using h)))
    else 1

theorem cycleType_rep_primeCycleTypeClass
    {n p j : ℕ} (h : IsValidPrimeCycleType n p j) :
    ∃ g : Equiv.Perm (Fin n),
      ConjClasses.mk g = primeCycleTypeClass n p j ∧
        g.cycleType = Multiset.replicate j p := by
  classical
  have hex :
      ∃ g : Equiv.Perm (Fin n),
        g.cycleType = Multiset.replicate j p :=
    (Equiv.Perm.exists_with_cycleType_iff
      (α := Fin n) (m := Multiset.replicate j p)).mpr
        (by simpa [IsValidPrimeCycleType] using h)
  refine ⟨Classical.choose hex, ?_, ?_⟩
  · simp only [primeCycleTypeClass, dif_pos h]
  · exact Classical.choose_spec hex

theorem carrier_primeCycleTypeClass
    {n p j : ℕ} (h : IsValidPrimeCycleType n p j) :
    (primeCycleTypeClass n p j).carrier =
      {g : Equiv.Perm (Fin n) |
        g.cycleType = Multiset.replicate j p} := by
  ext g
  obtain ⟨g₀, hg₀class, hg₀type⟩ :=
    cycleType_rep_primeCycleTypeClass h
  rw [ConjClasses.mem_carrier_iff_mk_eq, ← hg₀class,
    ConjClasses.mk_eq_mk_iff_isConj,
    Equiv.Perm.isConj_iff_cycleType_eq, Set.mem_setOf_eq,
    hg₀type]

theorem primeCycleTypeClass_injective
    {n p : ℕ} (hp : p.Prime) :
    Set.InjOn (primeCycleTypeClass n p)
      (Finset.Icc 1 (n / p)) := by
  intro i hi j hj hij
  have hiMul : p * i ≤ n := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hp.pos).mp
        (Finset.mem_Icc.mp hi).2
  have hjMul : p * j ≤ n := by
    simpa [Nat.mul_comm] using
      (Nat.le_div_iff_mul_le hp.pos).mp
        (Finset.mem_Icc.mp hj).2
  obtain ⟨gi, hgiClass, hgiType⟩ :=
    cycleType_rep_primeCycleTypeClass
      (isValidPrimeCycleType_of_prime hp hiMul)
  obtain ⟨gj, hgjClass, hgjType⟩ :=
    cycleType_rep_primeCycleTypeClass
      (isValidPrimeCycleType_of_prime hp hjMul)
  apply Multiset.replicate_left_injective p
  change Multiset.replicate i p = Multiset.replicate j p
  rw [← hgiType, ← hgjType]
  exact Equiv.Perm.isConj_iff_cycleType_eq.mp
    (ConjClasses.mk_eq_mk_iff_isConj.mp
      (hgiClass.trans (hij.trans hgjClass.symm)))

/-- The canonical class has the class cardinality used by the
arithmetic profile. -/
theorem ncard_carrier_primeCycleTypeClass
    {n p j : ℕ} (hp : p.Prime) (hj : 0 < j)
    (hpj : p * j ≤ n) :
    (primeCycleTypeClass n p j).carrier.ncard =
      primeCycleClassCard n p j := by
  have hvalid := isValidPrimeCycleType_of_prime hp hpj
  rw [carrier_primeCycleTypeClass hvalid]
  calc
    {g : Equiv.Perm (Fin n) |
        g.cycleType = Multiset.replicate j p}.ncard =
        (primeCycleTypeFinset n p j).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext g
      simp [primeCycleTypeFinset]
    _ = primeCycleClassCard n p j :=
      card_primeCycleTypeFinset hp.two_le hj hpj

/-- The row cardinal is the cardinal of the intersection of the
canonical conjugacy class with the Sylow subgroup. -/
theorem card_primeCycleTypeSylowRow_eq_ncard_inter
    {n p j : ℕ} (hp : p.Prime) (hpj : p * j ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n))) :
    (primeCycleTypeSylowRow n p j P).card =
      ((primeCycleTypeClass n p j).carrier ∩
        ((P : Subgroup (Equiv.Perm (Fin n))) : Set _)).ncard := by
  classical
  have hvalid := isValidPrimeCycleType_of_prime hp hpj
  rw [← Set.ncard_coe_finset]
  congr 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_inter_iff,
    primeCycleTypeSylowRow, Finset.mem_filter,
    primeCycleTypeFinset, Finset.mem_univ, true_and,
    carrier_primeCycleTypeClass hvalid, Set.mem_setOf_eq]
  apply and_congr_right
  intro _hcycle
  rfl

end LisiSabatini
