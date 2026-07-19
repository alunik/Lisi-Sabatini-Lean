import LisiSabatini.ClassTwoCommutator
import Mathlib.GroupTheory.Frattini
import Mathlib.GroupTheory.Sylow

/-!
# Frattini control of class-two p-groups

Mathlib defines the Frattini subgroup but does not yet package the standard
finite-`p`-group facts needed in Hall's argument.  This file proves that a
maximal subgroup of a finite `p`-group has index `p`, hence that the derived
subgroup and all `p`-th powers lie in the Frattini subgroup.

For a class-two group, centrality of all `p`-th powers is equivalent to the
needed exponent bound on the derived subgroup.  Consequently
`frattini G ≤ Z(G)` implies `(G')^p = 1`.  This isolates the next Hall step
as a subgroup inclusion rather than an elementwise spectrum assumption.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

/-! ## Maximal subgroups and the Frattini subgroup -/

/-- Every maximal subgroup of a finite `p`-group has index `p`. -/
theorem isCoatom_index_eq_prime_of_isPGroup
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (M : Subgroup G) (hM : IsCoatom M) :
    M.index = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent G := hGp.isNilpotent
  have hnormalAll : ∀ H : Subgroup G, IsCoatom H → H.Normal :=
    ((isNilpotent_of_finite_tfae (G := G)).out 0 2).mp hnil
  letI : M.Normal := hnormalAll M hM
  obtain ⟨n, hcardM⟩ := IsPGroup.iff_card.mp (hGp.to_subgroup M)
  obtain ⟨k, hindex⟩ := hGp.index M
  have hindexNeOne : M.index ≠ 1 := by
    intro hi
    exact hM.ne_top (Subgroup.index_eq_one.mp hi)
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hkzero
    apply hindexNeOne
    rw [hindex, hkzero, pow_zero]
  have hcardG : Nat.card G = p ^ (n + k) := by
    calc
      Nat.card G = Nat.card M * M.index := M.card_mul_index.symm
      _ = p ^ n * p ^ k := by rw [hcardM, hindex]
      _ = p ^ (n + k) := (pow_add p n k).symm
  have hdiv : p ^ (n + 1) ∣ Nat.card G := by
    rw [hcardG]
    exact pow_dvd_pow p (Nat.add_le_add_left hk n)
  obtain ⟨K, hcardK, hMK⟩ :=
    Sylow.exists_subgroup_card_pow_succ hdiv hcardM
  have hKneM : K ≠ M := by
    intro hKM
    subst K
    rw [hcardM] at hcardK
    exact (Nat.pow_lt_pow_right hp.one_lt (Nat.lt_succ_self n)).ne hcardK
  have hMltK : M < K := lt_of_le_of_ne hMK hKneM.symm
  have hKtop : K = ⊤ := hM.2 K hMltK
  have hcardGsucc : Nat.card G = p ^ (n + 1) := by
    calc
      Nat.card G = Nat.card (⊤ : Subgroup G) := Subgroup.card_top.symm
      _ = Nat.card K := by rw [hKtop]
      _ = p ^ (n + 1) := hcardK
  have hmul := M.card_mul_index
  rw [hcardM, hcardGsucc, pow_succ] at hmul
  exact Nat.mul_left_cancel (pow_pos hp.pos n) hmul

/-- The derived subgroup of a finite `p`-group lies in its Frattini
subgroup. -/
theorem commutator_le_frattini_of_isPGroup
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G) :
    commutator G ≤ frattini G := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [frattini, Order.radical]
  refine le_iInf fun M ↦ le_iInf fun hM ↦ ?_
  change IsCoatom M at hM
  have hnil : Group.IsNilpotent G := hGp.isNilpotent
  have hnormalAll : ∀ H : Subgroup G, IsCoatom H → H.Normal :=
    ((isNilpotent_of_finite_tfae (G := G)).out 0 2).mp hnil
  letI : M.Normal := hnormalAll M hM
  have hcardQ : Nat.card (G ⧸ M) = p := by
    rw [← M.index_eq_card]
    exact isCoatom_index_eq_prime_of_isPGroup hp hGp M hM
  letI : IsCyclic (G ⧸ M) := isCyclic_of_prime_card hcardQ
  apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
  exact IsCyclic.commutative

/-- Every `p`-th power in a finite `p`-group lies in its Frattini
subgroup. -/
theorem pow_prime_mem_frattini_of_isPGroup
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G) (x : G) :
    x ^ p ∈ frattini G := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [frattini, Order.radical]
  simp only [Subgroup.mem_iInf]
  intro M hM
  change IsCoatom M at hM
  have hnil : Group.IsNilpotent G := hGp.isNilpotent
  have hnormalAll : ∀ H : Subgroup G, IsCoatom H → H.Normal :=
    ((isNilpotent_of_finite_tfae (G := G)).out 0 2).mp hnil
  letI : M.Normal := hnormalAll M hM
  have hcardQ : Nat.card (G ⧸ M) = p := by
    rw [← M.index_eq_card]
    exact isCoatom_index_eq_prime_of_isPGroup hp hGp M hM
  rw [← QuotientGroup.eq_one_iff]
  change (QuotientGroup.mk' M x) ^ p = 1
  rw [← hcardQ]
  exact pow_card_eq_one'

/-! ## Class-two exponent transfer -/

/-- In a class-two group, central `p`-th powers force every element of the
derived subgroup to have `p`-th power one. -/
theorem commutator_pow_eq_one_of_classTwo_of_pow_mem_center
    {p : ℕ} {G : Type*} [Group G]
    (hclass : commutator G ≤ Subgroup.center G)
    (hpowerCenter : ∀ x : G, x ^ p ∈ Subgroup.center G) :
    ∀ c : commutator G, (c : G) ^ p = 1 := by
  let D := commutator G
  letI : IsMulCommutative D := by
    refine ⟨⟨fun a b ↦ Subtype.ext ?_⟩⟩
    exact (Subgroup.mem_center_iff.mp (hclass a.2) b).symm
  let K0 : Subgroup D := (powMonoidHom p : D →* D).ker
  let K : Subgroup G := K0.map D.subtype
  have hDK : D ≤ K := by
    change ⁅(⊤ : Subgroup G), ⊤⁆ ≤ K
    apply Subgroup.commutator_le.mpr
    intro x _hx y _hy
    have hxyD : ⁅x, y⁆ ∈ D :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y)
    let cD : D := ⟨⁅x, y⁆, hxyD⟩
    have hxyCenter : ⁅x, y⁆ ∈ Subgroup.center G := hclass hxyD
    have hcPow : (cD : G) ^ p = 1 := by
      rw [← commutatorElement_pow_left_of_mem_center x y hxyCenter p]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hpowerCenter x) y).symm
    apply Subgroup.mem_map.mpr
    refine ⟨cD, ?_, rfl⟩
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    exact hcPow
  intro c
  obtain ⟨k, hk, hkcoe⟩ := Subgroup.mem_map.mp (hDK c.2)
  have hkpow : k ^ p = 1 := MonoidHom.mem_ker.mp hk
  rw [← hkcoe]
  exact congrArg Subtype.val hkpow

/-- If the Frattini subgroup of a finite class-two `p`-group is central,
then its derived subgroup has exponent dividing `p`. -/
theorem commutator_pow_prime_eq_one_of_frattini_le_center
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hclass : commutator G ≤ Subgroup.center G)
    (hPhi : frattini G ≤ Subgroup.center G) :
    ∀ c : commutator G, (c : G) ^ p = 1 := by
  apply commutator_pow_eq_one_of_classTwo_of_pow_mem_center hclass
  intro x
  exact hPhi (pow_prime_mem_frattini_of_isPGroup hp hGp x)

end LisiSabatini
