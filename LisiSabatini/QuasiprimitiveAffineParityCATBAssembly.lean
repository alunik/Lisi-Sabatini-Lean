import LisiSabatini.QuasiprimitiveAffineParityCATB

/-!
# Assembly of the quasiprimitive affine parity leaves

In odd characteristic an injectively prime-labelled family has at most one
acting `2`-component.  The odd acting-prime rows occupy strictly less than
half of the doubled module by
`two_mul_sum_affineTwoBaseBadSet_lt_of_quasiprimitive_of_oddPrimes`.
The supplied symplectic-type estimate gives the same strict half-density
for the mapped normal `2`-core.  Splitting the index family by parity
therefore proves CATB.

This file contains no classification assertion.  It turns the exact
`TwoCoreSymplecticTypeHalfDensityData` publication boundary into the full
quasiprimitive CATB conclusion.
-/

noncomputable section

open scoped BigOperators

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uI

namespace QuasiprimitiveAffineParityCATB

variable {r d : ℕ} [Fact r.Prime] [NeZero r]
variable {K : Subgroup
  (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}

private abbrev TwoIndex {I : Type uI} (p : I → ℕ) :=
  {i : I // p i = 2}

private abbrev OddIndex {I : Type uI} (p : I → ℕ) :=
  {i : I // p i ≠ 2}

/-- Split a finite sum into the unique possible `2`-label and all odd
prime labels. -/
private theorem sum_eq_sum_twoIndex_add_oddIndex
    {I : Type uI} [Fintype I] (p : I → ℕ) (f : I → ℕ) :
    (∑ i, f i) =
      (∑ i : TwoIndex p, f i.1) +
        ∑ i : OddIndex p, f i.1 := by
  classical
  simpa [TwoIndex, OddIndex] using
    (Fintype.sum_subtype_add_sum_subtype
      (fun i ↦ p i = 2) f).symm

/-- Injective prime labels make the `2`-label subtype a subsingleton. -/
private theorem card_twoIndex_le_one
    {I : Type uI} [Fintype I] (p : I → ℕ)
    (hinj : Function.Injective p) :
    Fintype.card (TwoIndex p) ≤ 1 := by
  letI : Subsingleton (TwoIndex p) :=
    ⟨fun i j ↦ Subtype.ext
      (hinj (i.2.trans j.2.symm))⟩
  exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance

/-- In odd characteristic, the two-core half-density datum and the
classification-free odd-prime half bound assemble to full CATB at a
quasiprimitive leaf. -/
theorem commonAffineTwoBaseTranslates_of_quasiprimitive_of_oddChar
    [Fintype ((pCore 2 K).map K.subtype)]
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hdata : TwoCoreSymplecticTypeHalfDensityData K) :
    CommonAffineTwoBaseTranslates.{uI} r d K := by
  classical
  rw [commonAffineTwoBaseTranslates_iff_on,
    commonAffineTwoBaseTranslatesOn_iff_primeCores]
  intro I _ p hp hinj hcross a b
  let f : I → ℕ := fun i ↦
    (affineTwoBaseBadSet
      ((pCore (p i) K).map K.subtype) (a i) (b i)).ncard
  let T := TwoIndex p
  let O := OddIndex p
  let pO : O → ℕ := fun i ↦ p i.1
  let aO : O → Fin d → ZMod r := fun i ↦ a i.1
  let bO : O → Fin d → ZMod r := fun i ↦ b i.1
  let B₂ :=
    (affineTwoBaseBadSet
      ((pCore 2 K).map K.subtype) 0 0).ncard
  let M := r ^ (2 * d)
  have hodd : 2 * (∑ i : O, f i.1) < M := by
    have h :=
      two_mul_sum_affineTwoBaseBadSet_lt_of_quasiprimitive_of_oddPrimes
        (K := K) hrTwo hd
        (p := pO)
        (fun i ↦ hp i.1)
        (fun i ↦ i.2)
        (fun i ↦ hcross i.1)
        (fun _i _j hij ↦ Subtype.ext (hinj hij))
        hqp aO bO
    simpa [f, O, pO, aO, bO, M] using h
  have htwoCore : 2 * B₂ < M := by
    simpa [B₂, M] using
      two_mul_ncard_affineTwoBaseBadSet_mapped_pCore_two_lt_of_quasiprimitive
        hqp hrTwo hd hdata
  have htwoSum : (∑ i : T, f i.1) ≤ B₂ := by
    have hterm : ∀ i : T, f i.1 = B₂ := by
      intro i
      dsimp only [f, B₂]
      rw [affineTwoBaseBadSet_ncard_eq_untranslated]
      simp [i.2]
    calc
      (∑ i : T, f i.1) =
          Fintype.card T * B₂ := by
        simp_rw [hterm]
        simp
      _ ≤ 1 * B₂ :=
        Nat.mul_le_mul_right B₂
          (by
            simpa [T] using card_twoIndex_le_one p hinj)
      _ = B₂ := one_mul B₂
  have htwo : 2 * (∑ i : T, f i.1) < M :=
    (Nat.mul_le_mul_left 2 htwoSum).trans_lt htwoCore
  apply
    exists_commonAffineTwoBaseTranslates_of_sum_bad_ncard_lt
      (fun i ↦ (pCore (p i) K).map K.subtype) a b
  have hsplit :
      (∑ i, f i) =
        (∑ i : T, f i.1) + ∑ i : O, f i.1 := by
    simpa [T, O] using sum_eq_sum_twoIndex_add_oddIndex p f
  have htop :
      Nat.card ((Fin d → ZMod r) × (Fin d → ZMod r)) = M := by
    rw [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    dsimp only [M]
    rw [← pow_add]
    congr 1
    omega
  change (∑ i, f i) <
    Nat.card ((Fin d → ZMod r) × (Fin d → ZMod r))
  rw [hsplit, htop]
  omega

end QuasiprimitiveAffineParityCATB

end LisiSabatini
