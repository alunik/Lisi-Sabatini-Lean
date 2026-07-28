module

public import LisiSabatini.AffineTwoBaseOrbitAvoidance
public import LisiSabatini.MappedPCoreFrattini
public import LisiSabatini.MappedPCoreCyclicCenterClassTwo
public import LisiSabatini.PrimitiveTopMixedPrimeCoreDominationCore

/-!
# The strong odd-prime quasiprimitive affine leaf

The imprimitive two-base recursion needs a common regular point in the
diagonal action outside two prescribed component orbits.  For odd acting
primes in odd characteristic, the existing one-point theorem already has
one full orbit of reserve.  Squaring that estimate gives exactly the
two-orbit reserve on the doubled module.

This file makes that implication explicit and transfers it from the normal
prime cores to arbitrary normal prime subgroups.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI

open PrimeCoreMixedCyclicCenterFullSchurFamilyRows

variable {r d : ℕ} [Fact r.Prime] [NeZero r]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
variable {I : Type uI} [Fintype I] {p : I → ℕ}

/-- The exact one-point orbit reserve for a structural prime-core family
amplifies to two-orbit avoidance in the diagonal action. -/
theorem
    twoOrbitAvoidingCommonRegularTranslates_diagonal_pCores_of_rows
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (R : PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun i ↦
        (((pCore (p i) K).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r)))) := by
  apply
    twoOrbitAvoidingCommonRegularTranslates_diagonal_of_onePointOrbitReserve
      (fun i ↦ (pCore (p i) K).map K.subtype)
  intro i₀ c
  rw [show Nat.card (Fin d → ZMod r) = r ^ d by
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]]
  exact
    R.sum_ncard_nonregularVectors_add_pCoreOrbit_lt
      hrTwo hd hp hpTwo hcross hinj i₀ c

set_option linter.unusedFintypeInType false in
/-- At an odd-characteristic quasiprimitive leaf, every distinctly
odd-prime-labelled family of normal components has the recursively stable
two-orbit diagonal property. -/
theorem
    twoOrbitAvoidingCommonRegularTranslates_diagonal_of_quasiprimitive_of_oddPrimes
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (hinj : Function.Injective p)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (H : I → Subgroup K)
    (hHnormal : ∀ i, (H i).Normal)
    (hHp : ∀ i, IsPGroup (p i) (H i)) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun i ↦
        ((H i).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))) := by
  let R :
      PrimeCoreMixedCyclicCenterFullSchurFamilyRows r d K p :=
    PrimeCoreMixedCyclicCenterFullSchurFamilyRows.ofQuasiprimitive
      hp hcross hqp
      (fun i hne hnoncomm ↦ by
        let hA : IsAdmissibleNoncommutingPrimeCore r d (p i) K :=
          ⟨hp i, hpTwo i, hcross i, hne, hnoncomm⟩
        exact
          mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
            (Fact.out : Nat.Prime r) hqp hA
            (mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
              (Fact.out : Nat.Prime r) hqp hA))
  apply
    TwoOrbitAvoidingCommonRegularTranslates.mono
      (B := fun i ↦
        (((pCore (p i) K).map K.subtype).map
          (diagonalGeneralLinearHom (ZMod r) (Fin d → ZMod r))))
  · intro i
    exact Subgroup.map_mono
      (map_normalPSubgroup_le_map_pCore (hHp i) (hHnormal i))
  · exact
      twoOrbitAvoidingCommonRegularTranslates_diagonal_pCores_of_rows
        hrTwo hd hp hpTwo hcross hinj R

end LisiSabatini
