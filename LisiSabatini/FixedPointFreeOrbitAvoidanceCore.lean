import LisiSabatini.FixedPointFreeNCASCore
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# Core counting bounds for fixed-point-free prime families

A fixed-point-free linear group acts freely on the nonzero vectors.  This
core records the resulting order divisibility and the sharp bounds on the
number of active, distinctly odd-prime-labelled components.  The later
orbit-avoidance adapters remain in `FixedPointFreeOrbitAvoidance.lean`.
-/

noncomputable section

namespace LisiSabatini

universe uI uR uV

/-! ## The free action on nonzero vectors -/

/-- The nonzero vectors form a subaction for every linear group. -/
def nonzeroVectorSubMulAction
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) :
    SubMulAction H V where
  carrier := {v : V | v ≠ 0}
  smul_mem' := by
    intro g v hv hzero
    apply hv
    have h := congrArg (fun w : V ↦ g⁻¹ • w) hzero
    simpa using h

@[simp]
theorem mem_nonzeroVectorSubMulAction_iff
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) (v : V) :
    v ∈ nonzeroVectorSubMulAction H ↔ v ≠ 0 :=
  Iff.rfl

/-- Fixed-point-freeness away from zero makes the induced action on the
nonzero-vector subaction free. -/
theorem stabilizer_nonzeroVectorSubMulAction_eq_bot
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hfp : FixedPointFreeOffZero H)
    (v : nonzeroVectorSubMulAction H) :
    MulAction.stabilizer H v = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  by_cases hgone : g = 1
  · exact hgone
  · have hfixSubtype : g • v = v :=
      MulAction.mem_stabilizer_iff.mp hg
    have hfix : g • (v : V) = v :=
      congrArg Subtype.val hfixSubtype
    exact False.elim (v.2 (hfp g hgone v hfix))

/-- A finite fixed-point-free linear group has order dividing the number of
nonzero vectors.

The proof uses the class-formula equivalence for the free action on the
nonzero-vector subaction. -/
theorem natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero
    {R : Type uR} {V : Type uV}
    [Finite V] [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hfp : FixedPointFreeOffZero H) :
    Nat.card H ∣ Nat.card V - 1 := by
  classical
  let NZ := nonzeroVectorSubMulAction H
  let e : NZ ≃
      Quotient (MulAction.orbitRel H NZ) × H :=
    MulAction.selfEquivOrbitsQuotientProd
      (fun v ↦ stabilizer_nonzeroVectorSubMulAction_eq_bot H hfp v)
  let nzEquiv : NZ ≃ {v : V // v ≠ 0} :=
    { toFun := fun v ↦ ⟨v.1, v.2⟩
      invFun := fun v ↦ ⟨v.1, v.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hcardNZ : Nat.card NZ = Nat.card V - 1 := by
    letI : Fintype V := Fintype.ofFinite V
    calc
      Nat.card NZ = Nat.card {v : V // v ≠ 0} :=
        Nat.card_congr nzEquiv
      _ = Nat.card V - 1 := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        rw [Fintype.card_subtype_compl (fun v : V ↦ v = 0)]
        simp
  have he : Nat.card NZ =
      Nat.card (Quotient (MulAction.orbitRel H NZ)) * Nat.card H := by
    calc
      Nat.card NZ =
          Nat.card (Quotient (MulAction.orbitRel H NZ) × H) :=
        Nat.card_congr e
      _ = Nat.card (Quotient (MulAction.orbitRel H NZ)) *
          Nat.card H := Nat.card_prod _ _
  refine ⟨Nat.card (Quotient (MulAction.orbitRel H NZ)), ?_⟩
  rw [← hcardNZ, he, Nat.mul_comm]

/-! ## The sharp half-size orbit bound -/

/-- A nontrivial odd `p`-group acting fixed-point-freely on a finite set of
odd cardinality has order at most half the number of nonzero vectors. -/
theorem natCard_le_half_natCard_sub_one_of_oddPGroup_fixedPointFreeOffZero
    {R : Type uR} {V : Type uV}
    [Finite V] [Semiring R] [AddCommMonoid V] [Module R V]
    (hVodd : Odd (Nat.card V)) (hV : 1 < Nat.card V)
    {p : ℕ} (hp : Nat.Prime p) (hpTwo : p ≠ 2)
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hP : IsPGroup p H)
    (hfp : FixedPointFreeOffZero H) :
    Nat.card H ≤ (Nat.card V - 1) / 2 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : Fintype V := Fintype.ofFinite V
  have hVnontrivial : Nontrivial V :=
    Finite.one_lt_card_iff_nontrivial.mp (by
      simpa only [Nat.card_eq_fintype_card] using hV)
  letI : Nontrivial V := hVnontrivial
  obtain ⟨v : V, hv⟩ := exists_ne (0 : V)
  letI : Finite H := Finite.of_injective
    (fun g : H ↦ g • v)
    (orbitMap_injective_of_fixedPointFreeOffZero_of_ne_zero H hfp hv)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hpodd : Odd p := hp.odd_of_ne_two hpTwo
  have hcardOdd : Odd (Nat.card H) := by
    rw [hn]
    exact hpodd.pow
  obtain ⟨k, hk⟩ :=
    natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero H hfp
  have hpredEven : Even (Nat.card V - 1) :=
    hVodd.tsub_odd odd_one
  have hprodEven : Even (Nat.card H * k) := by
    rw [← hk]
    exact hpredEven
  have hkEven : Even k :=
    (Nat.even_mul.mp hprodEven).resolve_left
      (Nat.not_even_iff_odd.mpr hcardOdd)
  have hkZero : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    omega
  have hkTwo : 2 ≤ k :=
    by
      have := Nat.one_lt_of_ne_zero_of_even hkZero hkEven
      omega
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr
  calc
    Nat.card H * 2 ≤ Nat.card H * k :=
      Nat.mul_le_mul_left _ hkTwo
    _ = Nat.card V - 1 := hk.symm

/-! ## Distinct odd primes bound the active translated origins -/

/-- Division by two is injective on odd natural numbers. -/
theorem nat_div_two_injective_of_odd
    {m n : ℕ} (hm : Odd m) (hn : Odd n)
    (hdiv : m / 2 = n / 2) :
    m = n := by
  have hmmod : m % 2 = 1 :=
    Nat.not_even_iff.mp (Nat.not_even_iff_odd.mpr hm)
  have hnmod : n % 2 = 1 :=
    Nat.not_even_iff.mp (Nat.not_even_iff_odd.mpr hn)
  have hmform := Nat.two_mul_odd_div_two hmmod
  have hnform := Nat.two_mul_odd_div_two hnmod
  omega

/-- Strict order between odd naturals descends after division by two. -/
theorem nat_div_two_lt_div_two_of_odd_of_lt
    {m n : ℕ} (hm : Odd m) (hn : Odd n) (hmn : m < n) :
    m / 2 < n / 2 := by
  have hmmod : m % 2 = 1 :=
    Nat.not_even_iff.mp (Nat.not_even_iff_odd.mpr hm)
  have hnmod : n % 2 = 1 :=
    Nat.not_even_iff.mp (Nat.not_even_iff_odd.mpr hn)
  have hmform := Nat.two_mul_odd_div_two hmmod
  have hnform := Nat.two_mul_odd_div_two hnmod
  omega

/-- A distinctly odd-prime-labelled active fixed-point-free family has at
most half as many active groups as ambient vectors. -/
theorem activeLinearIndices_card_le_natCard_div_two_of_distinct_odd_primes_fixedPointFreeOffZero
    {I : Type uI} [Fintype I]
    {R : Type uR} {V : Type uV}
    [Finite V] [Semiring R] [AddCommMonoid V] [Module R V]
    (hVodd : Odd (Nat.card V))
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hpTwo : ∀ i, p i ≠ 2)
    (hinj : Function.Injective p)
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R V))
    (hP : ∀ i, IsPGroup (p i) (H i))
    (hfp : ∀ i ∈ activeLinearIndices H,
      FixedPointFreeOffZero (H i)) :
    (activeLinearIndices H).card ≤ Nat.card V / 2 := by
  classical
  let active := activeLinearIndices H
  have hpodd : ∀ i, Odd (p i) :=
    fun i ↦ (hp i).odd_of_ne_two (hpTwo i)
  have hhalfInj : Function.Injective (fun i : I ↦ p i / 2) := by
    intro i j hij
    apply hinj
    exact nat_div_two_injective_of_odd (hpodd i) (hpodd j) hij
  have hprimeLt : ∀ i ∈ active, p i < Nat.card V := by
    intro i hi
    have hne : H i ≠ ⊥ := by
      simpa only [active, activeLinearIndices, Finset.mem_filter,
        Finset.mem_univ, true_and] using hi
    exact prime_lt_natCard_of_fixedPointFreeOffZero
      (hp i) (H i) (hP i) hne (hfp i hi)
  have himage : active.image (fun i ↦ p i / 2) ⊆
      Finset.range (Nat.card V / 2) := by
    intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_range.mpr
      (nat_div_two_lt_div_two_of_odd_of_lt
        (hpodd i) hVodd (hprimeLt i hi))
  calc
    active.card = (active.image (fun i ↦ p i / 2)).card := by
      symm
      exact Finset.card_image_of_injective active hhalfInj
    _ ≤ (Finset.range (Nat.card V / 2)).card :=
      Finset.card_le_card himage
    _ = Nat.card V / 2 := Finset.card_range _

end LisiSabatini
