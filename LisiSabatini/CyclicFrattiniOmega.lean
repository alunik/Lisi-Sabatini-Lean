module

public import LisiSabatini.CyclicPGroupAutomorphism
public import LisiSabatini.ClassTwoFrattini
public import LisiSabatini.HallPGroupStructure

/-!
# The prime-order layer of a cyclic Frattini subgroup

This file isolates the elementary automorphism argument used in the
index-prime Hall branch.  An automorphism of a finite cyclic `p`-group whose
order divides a power of `p` fixes the elements killed by the `p`-th power.
Consequently the prime-order layer of a cyclic Frattini subgroup of a finite
`p`-group is central.  Moreover every commutator with the Frattini subgroup
belongs to that layer.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped IsMulCommutative

set_option backward.isDefEq.respectTransparency false

open Subgroup
open scoped commutatorElement

private theorem zmod_pow_primePow
    {p : ℕ} (hp : p.Prime) (x : ZMod p) :
    ∀ n : ℕ, x ^ (p ^ n) = x := by
  let : Fact p.Prime := ⟨hp⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_mul, ih, ZMod.pow_card]

theorem cyclicIsMulCommutative
    {A : Type*} [Group A] (hA : IsCyclic A) : IsMulCommutative A := by
  let : IsCyclic A := hA
  exact IsCyclic.isMulCommutative

/-- A `p`-power-order automorphism of a finite cyclic `p`-group fixes its
prime-order layer.  The hypothesis is phrased as a power relation so that it
can be applied directly to conjugation by an element of a `p`-group. -/
theorem cyclicPGroup_aut_primeKernel_fixed_of_pow_primePower_eq_one
    {p s : ℕ} {A : Type*} [Group A] [Finite A]
    (hp : p.Prime) (hAp : IsPGroup p A) (hACyclic : IsCyclic A)
    (sigma : MulAut A) (hsigma : sigma ^ (p ^ s) = 1) :
    ∀ a : A, a ^ p = 1 → sigma a = a := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hA : Nontrivial A
  · let : Nontrivial A := hA
    let : IsCyclic A := hACyclic
    obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hAp
    have hn : n ≠ 0 := by
      intro hn0
      have hgt := Finite.one_lt_card (α := A)
      rw [hcard, hn0, pow_zero] at hgt
      exact (Nat.lt_irrefl 1 hgt)
    obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := A)
    have hgOrder : orderOf g = p ^ n := by
      rw [orderOf_eq_card_of_forall_mem_powers hg, hcard]
    have hgNe : g ≠ 1 := by
      intro hgone
      have hone : orderOf g = 1 := by simp [hgone]
      have hgt := Finite.one_lt_card (α := A)
      rw [← orderOf_eq_card_of_forall_mem_powers hg, hone] at hgt
      exact (Nat.lt_irrefl 1 hgt)
    obtain ⟨k, hk⟩ := hg (sigma g)
    change g ^ k = sigma g at hk
    have hkpos : 0 < k := by
      rcases k with _ | k
      · simp only [pow_zero] at hk
        exfalso
        apply hgNe
        apply sigma.injective
        simpa using hk.symm
      · exact Nat.succ_pos k
    have hiterate : ∀ j : ℕ, (sigma ^ j) g = g ^ (k ^ j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          calc
            (sigma ^ (j + 1)) g = (sigma ^ j) (sigma g) := by
              rw [pow_succ]
              rfl
            _ = (sigma ^ j) (g ^ k) := by rw [← hk]
            _ = ((sigma ^ j) g) ^ k := map_pow (sigma ^ j) g k
            _ = (g ^ (k ^ j)) ^ k := by rw [ih]
            _ = g ^ (k ^ (j + 1)) := by
              rw [← pow_mul, pow_succ]
    have hgPow : g ^ (k ^ (p ^ s)) = g := by
      rw [← hiterate (p ^ s), hsigma]
      rfl
    have hmodN : k ^ (p ^ s) ≡ 1 [MOD p ^ n] := by
      rw [← hgOrder]
      exact pow_eq_pow_iff_modEq.mp (by simpa using hgPow)
    have hpDvdPowN : p ∣ p ^ n := dvd_pow_self p hn
    have hmodP : k ^ (p ^ s) ≡ 1 [MOD p] :=
      hmodN.of_dvd hpDvdPowN
    have hcastPow : (k : ZMod p) ^ (p ^ s) = 1 := by
      rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
      exact hmodP
    have hcast : (k : ZMod p) = 1 := by
      rw [← zmod_pow_primePow hp (k : ZMod p) s]
      exact hcastPow
    have hkMod : k ≡ 1 [MOD p] := by
      exact (ZMod.natCast_eq_natCast_iff k 1 p).mp (by simpa using hcast)
    have hpDvdSub : p ∣ k - 1 :=
      (Nat.modEq_iff_dvd' hkpos).mp hkMod.symm
    intro a ha
    obtain ⟨m, rfl⟩ := hg a
    have hpowOne : g ^ (m * p) = 1 := by
      simpa [pow_mul] using ha
    have hcardDvdMP : p ^ n ∣ m * p := by
      rw [← hgOrder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hpowOne
    have hnSplit : p ^ n = p ^ (n - 1) * p := by
      rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)]
    have hpredDvdM : p ^ (n - 1) ∣ m := by
      rw [hnSplit] at hcardDvdMP
      exact (Nat.mul_dvd_mul_iff_right hp.pos).mp hcardDvdMP
    have hcardDvdDiff : p ^ n ∣ (k - 1) * m := by
      obtain ⟨u, hu⟩ := hpDvdSub
      obtain ⟨v, hv⟩ := hpredDvdM
      refine ⟨u * v, ?_⟩
      rw [hu, hv, hnSplit]
      ac_rfl
    have hkm : k * m ≡ m [MOD p ^ n] := by
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd' (Nat.le_mul_of_pos_left m hkpos)]
      simpa [Nat.mul_sub_right_distrib] using hcardDvdDiff
    calc
      sigma (g ^ m) = (sigma g) ^ m := map_pow sigma g m
      _ = (g ^ k) ^ m := by rw [← hk]
      _ = g ^ (k * m) := by rw [pow_mul]
      _ = g ^ m := by
        apply pow_eq_pow_iff_modEq.mpr
        simpa [hgOrder] using hkm
  · have : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    intro a _
    exact Subsingleton.elim _ _

/-- Exact-order form of
`cyclicPGroup_aut_primeKernel_fixed_of_pow_primePower_eq_one`. -/
theorem cyclicPGroup_aut_primeKernel_fixed_of_orderOf_eq_primePower
    {p s : ℕ} {A : Type*} [Group A] [Finite A]
    (hp : p.Prime) (hAp : IsPGroup p A) (hACyclic : IsCyclic A)
    (sigma : MulAut A) (hsigma : orderOf sigma = p ^ s) :
    ∀ a : A, a ^ p = 1 → sigma a = a := by
  apply cyclicPGroup_aut_primeKernel_fixed_of_pow_primePower_eq_one
    hp hAp hACyclic sigma
  rw [← hsigma]
  exact pow_orderOf_eq_one sigma

/-! ## The prime kernel inside a commutative subgroup -/

/-- The elements of a commutative subgroup `A` killed by the `p`-th power,
viewed as a subgroup of the ambient group.  The commutativity proof is an
explicit argument so that the object can be named without installing a
global typeclass instance. -/
def subgroupPrimeKernel
    {G : Type*} [Group G] (p : ℕ) (A : Subgroup G)
    (hAcomm : IsMulCommutative A) : Subgroup G := by
  letI : IsMulCommutative A := hAcomm
  exact ((powMonoidHom p : A →* A).ker).map A.subtype

/-- Intrinsic membership in `subgroupPrimeKernel`. -/
theorem mem_subgroupPrimeKernel_iff
    {G : Type*} [Group G] {p : ℕ} {A : Subgroup G}
    (hAcomm : IsMulCommutative A) (x : G) :
    x ∈ subgroupPrimeKernel p A hAcomm ↔ x ∈ A ∧ x ^ p = 1 := by
  let : IsMulCommutative A := hAcomm
  constructor
  · intro hx
    change x ∈ ((powMonoidHom p : A →* A).ker).map A.subtype at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨a.2, ?_⟩
    have hapow : a ^ p = 1 := by
      exact MonoidHom.mem_ker.mp ha
    exact congrArg Subtype.val hapow
  · rintro ⟨hxA, hxpow⟩
    change x ∈ ((powMonoidHom p : A →* A).ker).map A.subtype
    apply Subgroup.mem_map.mpr
    refine ⟨⟨x, hxA⟩, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact hxpow

/-- The prime-order layer of a cyclic Frattini subgroup. -/
def frattiniPrimeKernel
    (p : ℕ) (P : Type*) [Group P]
    (hPhiCyclic : IsCyclic (frattini P)) : Subgroup P :=
  subgroupPrimeKernel p (frattini P)
    (cyclicIsMulCommutative hPhiCyclic)

@[simp]
theorem mem_frattiniPrimeKernel_iff
    {p : ℕ} {P : Type*} [Group P]
    (hPhiCyclic : IsCyclic (frattini P)) (x : P) :
    x ∈ frattiniPrimeKernel p P hPhiCyclic ↔
      x ∈ frattini P ∧ x ^ p = 1 :=
  mem_subgroupPrimeKernel_iff
    (cyclicIsMulCommutative hPhiCyclic) x

/-- The prime-order layer of a cyclic Frattini subgroup is characteristic
in the ambient group. -/
theorem frattiniPrimeKernel_characteristic
    {p : ℕ} {P : Type*} [Group P]
    (hPhiCyclic : IsCyclic (frattini P)) :
    (frattiniPrimeKernel p P hPhiCyclic).Characteristic := by
  let : IsMulCommutative (frattini P) :=
    cyclicIsMulCommutative hPhiCyclic
  unfold frattiniPrimeKernel subgroupPrimeKernel
  apply characteristic_map_subtype
  exact powMonoidHom_ker_characteristic (frattini P) p

/-! ## Conjugation on a cyclic Frattini subgroup -/

/-- Conjugation by any element of a finite `p`-group has `p`-th power one
on a cyclic Frattini subgroup.  Indeed the conjugating element's `p`-th
power lies in `Phi(P)`, and a cyclic subgroup is commutative. -/
theorem frattini_conj_pow_prime_eq_one_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P)) (x : P) :
    let conjPhi : P →* MulAut (frattini P) := MulAut.conjNormal
    (conjPhi x) ^ p = 1 := by
  dsimp only
  let : IsMulCommutative (frattini P) :=
    cyclicIsMulCommutative hPhiCyclic
  let conjPhi : P →* MulAut (frattini P) := MulAut.conjNormal
  have hxpowPhi : x ^ p ∈ frattini P :=
    pow_prime_mem_frattini_of_isPGroup hp hPp x
  have hconjPowOne : conjPhi (x ^ p) = 1 := by
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    have hcomm : x ^ p * (a : P) = (a : P) * x ^ p := by
      exact congrArg Subtype.val
        (mul_comm (⟨x ^ p, hxpowPhi⟩ : frattini P) a)
    simp only [conjPhi, MulAut.conjNormal_apply, MulAut.one_apply]
    calc
      x ^ p * (a : P) * (x ^ p)⁻¹ =
          (a : P) * x ^ p * (x ^ p)⁻¹ := by rw [hcomm]
      _ = a := by simp
  rw [← map_pow]
  exact hconjPowOne

/-- Every element of `Phi(P)` killed by the `p`-th power is central when
`Phi(P)` is cyclic.  This is the cyclic-Frattini `Omega₁` centrality
statement, exposed directly for ambient elements. -/
theorem frattini_prime_order_element_mem_center_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P))
    {z : P} (hzPhi : z ∈ frattini P) (hzpow : z ^ p = 1) :
    z ∈ Subgroup.center P := by
  let : IsMulCommutative (frattini P) :=
    cyclicIsMulCommutative hPhiCyclic
  let conjPhi : P →* MulAut (frattini P) := MulAut.conjNormal
  rw [Subgroup.mem_center_iff]
  intro x
  have hsigma : (conjPhi x) ^ (p ^ 1) = 1 := by
    simpa using
      (frattini_conj_pow_prime_eq_one_of_isCyclic hp hPp hPhiCyclic x)
  have hfix : conjPhi x (⟨z, hzPhi⟩ : frattini P) = ⟨z, hzPhi⟩ :=
    cyclicPGroup_aut_primeKernel_fixed_of_pow_primePower_eq_one
      hp (hPp.to_subgroup (frattini P)) hPhiCyclic (conjPhi x) hsigma
      ⟨z, hzPhi⟩ (by
        apply Subtype.ext
        exact hzpow)
  have hconj : x * z * x⁻¹ = z := by
    simpa only [conjPhi, MulAut.conjNormal_apply] using
      congrArg Subtype.val hfix
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- Subgroup form of cyclic-Frattini `Omega₁` centrality. -/
theorem frattiniPrimeKernel_le_center_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P)) :
    frattiniPrimeKernel p P hPhiCyclic ≤
      Subgroup.center P := by
  intro z hz
  rw [mem_frattiniPrimeKernel_iff] at hz
  exact frattini_prime_order_element_mem_center_of_isCyclic
    hp hPp hPhiCyclic hz.1 hz.2

/-! ## Commutators with the Frattini subgroup -/

/-- In the odd-prime case, every basic commutator with `Phi(P)` has
`p`-th power one.  Here the previously proved automorphism theorem
`cyclicPGroup_aut_pow_fixed_of_pow_prime_eq_one` is used at exactly the
remaining point: conjugation fixes all `p`-th powers in the cyclic
Frattini subgroup. -/
theorem frattini_commutator_pow_prime_eq_one_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P))
    (x : P) {c : P} (hc : c ∈ frattini P) :
    ⁅x, c⁆ ^ p = 1 := by
  let : IsMulCommutative (frattini P) :=
    cyclicIsMulCommutative hPhiCyclic
  let conjPhi : P →* MulAut (frattini P) := MulAut.conjNormal
  let cPhi : frattini P := ⟨c, hc⟩
  have hsigma : (conjPhi x) ^ p = 1 :=
    frattini_conj_pow_prime_eq_one_of_isCyclic hp hPp hPhiCyclic x
  have hfixPowers : ∀ a : frattini P,
      conjPhi x (a ^ p) = a ^ p :=
    cyclicPGroup_aut_pow_fixed_of_pow_prime_eq_one
      hp hpOdd (hPp.to_subgroup (frattini P)) hPhiCyclic
      (conjPhi x) hsigma
  have hpow : ((conjPhi x cPhi) * cPhi⁻¹) ^ p = 1 := by
    calc
      ((conjPhi x cPhi) * cPhi⁻¹) ^ p =
          (conjPhi x cPhi) ^ p * (cPhi⁻¹) ^ p := mul_pow _ _ p
      _ = conjPhi x (cPhi ^ p) * (cPhi ^ p)⁻¹ := by
        rw [map_pow, inv_pow]
      _ = 1 := by rw [hfixPowers cPhi, mul_inv_cancel]
  have hpowAmbient := congrArg Subtype.val hpow
  simpa only [conjPhi, cPhi, MulAut.conjNormal_apply,
    commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_pow, Subgroup.coe_one] using hpowAmbient

/-- A basic commutator with `Phi(P)` lies in the Frattini subgroup and in
its prime-order layer. -/
theorem frattini_commutator_mem_primeKernel_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P))
    (x : P) {c : P} (hc : c ∈ frattini P) :
    ⁅x, c⁆ ∈ frattiniPrimeKernel p P hPhiCyclic := by
  rw [mem_frattiniPrimeKernel_iff]
  refine ⟨?_, frattini_commutator_pow_prime_eq_one_of_isCyclic
    hp hpOdd hPp hPhiCyclic x hc⟩
  exact (Subgroup.commutator_le_right
    (⊤ : Subgroup P) (frattini P))
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hc)

/-- Every basic commutator with a cyclic Frattini subgroup is central and
has `p`-th power one. -/
theorem frattini_commutator_mem_center_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P))
    (x : P) {c : P} (hc : c ∈ frattini P) :
    ⁅x, c⁆ ∈ Subgroup.center P := by
  apply frattiniPrimeKernel_le_center_of_isCyclic hp hPp hPhiCyclic
  exact frattini_commutator_mem_primeKernel_of_isCyclic
    hp hpOdd hPp hPhiCyclic x hc

/-- Subgroup form: `[P, Phi(P)]` is contained in the central prime-order
layer of `Phi(P)`. -/
theorem commutator_top_frattini_le_primeKernel_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P)) :
    ⁅(⊤ : Subgroup P), frattini P⁆ ≤
      frattiniPrimeKernel p P hPhiCyclic := by
  apply Subgroup.commutator_le.mpr
  intro x _ c hc
  exact frattini_commutator_mem_primeKernel_of_isCyclic
    hp hpOdd hPp hPhiCyclic x hc

/-- In particular `[P, Phi(P)]` is central. -/
theorem commutator_top_frattini_le_center_of_isCyclic
    {p : ℕ} {P : Type*} [Group P] [Finite P]
    (hp : p.Prime) (hpOdd : Odd p) (hPp : IsPGroup p P)
    (hPhiCyclic : IsCyclic (frattini P)) :
    ⁅(⊤ : Subgroup P), frattini P⁆ ≤ Subgroup.center P :=
  (commutator_top_frattini_le_primeKernel_of_isCyclic
    hp hpOdd hPp hPhiCyclic).trans
      (frattiniPrimeKernel_le_center_of_isCyclic hp hPp hPhiCyclic)

end LisiSabatini
