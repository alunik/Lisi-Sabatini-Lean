module

public import LisiSabatini.HobbyFrattiniTheoremCore
public import LisiSabatini.CyclicFrattiniCentralityCore

/-!
# The rank-two extraction used in translated regularity

This file extracts an ambient-normal elementary abelian subgroup of order
`p ^ 2` from any ambient-normal noncyclic abelian subgroup of a finite
`p`-group.  The extraction is valid for every prime, including `2`.

For odd primes we also prove the required existence theorem: every finite
noncyclic `p`-group has an ambient-normal elementary abelian subgroup of
order `p ^ 2`.  The proof uses the established cyclic-Frattini results,
the class-two product-power formula, and cyclicity of a group with cyclic
image and central kernel.  No classification theorem is assumed.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped IsMulCommutative commutatorElement

/-- The prime kernel of an ambient-normal abelian subgroup is
ambient-normal. -/
theorem subgroupPrimeKernel_normal
    {p : ℕ} {G : Type*} [Group G]
    (A : Subgroup G) (hA : A.Normal) (hAcomm : IsMulCommutative A) :
    (subgroupPrimeKernel p A hAcomm).Normal := by
  refine ⟨?_⟩
  intro x hx g
  obtain ⟨hxA, hxpow⟩ := (mem_subgroupPrimeKernel_iff hAcomm x).mp hx
  apply (mem_subgroupPrimeKernel_iff hAcomm (g * x * g⁻¹)).mpr
  refine ⟨hA.conj_mem x hxA g, ?_⟩
  have hpow := map_pow (MulAut.conj g) x p
  simpa only [MulAut.conj_apply, hxpow, map_one] using hpow.symm

/-- A normal noncyclic abelian subgroup of a finite `p`-group contains
an ambient-normal elementary abelian subgroup of order `p ^ 2`.

The exponent assertion is given explicitly, so users need not install a
particular elementary-abelian coordinate structure. -/
theorem exists_normal_primeSquare_of_normal_noncyclic_abelian
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (A : Subgroup G) (hA : A.Normal)
    (hAcomm : IsMulCommutative A) (hAnoncyclic : ¬ IsCyclic A) :
    ∃ E : Subgroup G,
      E.Normal ∧ E ≤ A ∧ Nat.card E = p ^ 2 ∧
        IsMulCommutative E ∧ (∀ x : E, x ^ p = 1) ∧ ¬ IsCyclic E := by
  let : Fact p.Prime := ⟨hp⟩
  let groupA : Group A := inferInstance
  let : CommGroup A := { groupA with mul_comm := hAcomm.1.1 }
  let K : Subgroup G := subgroupPrimeKernel p A hAcomm
  have hKnormal : K.Normal := subgroupPrimeKernel_normal A hA hAcomm
  have hKcard : p ^ 2 ≤ Nat.card K := by
    have hOmega := prime_sq_le_natCard_powMonoidHom_ker_of_not_isCyclic
      hp (hGp.to_subgroup A) hAnoncyclic
    change p ^ 2 ≤ Nat.card (((powMonoidHom p : A →* A).ker).map A.subtype)
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact hOmega
  obtain ⟨C, E, _hCnormal, hEnormal, _hCE, hEK, _hCcard, hEcard, _hCcenter⟩ :=
    exists_normal_flag_card_prime_prime_sq_le hp hGp K hKnormal hKcard
  have hEA : E ≤ A := by
    intro x hx
    exact (mem_subgroupPrimeKernel_iff hAcomm x).mp (hEK hx) |>.1
  have hEcomm : IsMulCommutative E :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hEcard
  have hEpow : ∀ x : E, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    exact (mem_subgroupPrimeKernel_iff hAcomm (x : G)).mp (hEK x.2) |>.2
  have hEnoncyclic : ¬ IsCyclic E := by
    let : IsMulCommutative E := hEcomm
    exact not_isCyclic_of_natCard_eq_prime_sq_of_pow_eq_one hp hEcard hEpow
  exact ⟨E, hEnormal, hEA, hEcard, hEcomm, hEpow, hEnoncyclic⟩

/-- In a finite `p`-group, a noncentral normal subgroup of order `p ^ 2`
has centralizer of index exactly `p`. -/
theorem centralizer_index_eq_prime_of_normal_primeSquare_noncentral
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (E : Subgroup G) (hE : E.Normal) (hEcard : Nat.card E = p ^ 2)
    (hEnoncentral : ¬ E ≤ Subgroup.center G) :
    (Subgroup.centralizer (E : Set G)).index = p := by
  let : Fact p.Prime := ⟨hp⟩
  have hle := centralizer_index_le_prime_of_normal_natCard_eq_prime_sq
    hp hGp E hE hEcard
  obtain ⟨n, hn⟩ := hGp.index (Subgroup.centralizer (E : Set G))
  have hnne : n ≠ 0 := by
    intro hnzero
    have htop : Subgroup.centralizer (E : Set G) = ⊤ := by
      apply Subgroup.index_eq_one.mp
      simp only [hn, hnzero, pow_zero]
    exact hEnoncentral (Subgroup.centralizer_eq_top_iff_subset.mp htop)
  have hnle : n ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    simpa only [hn, pow_one] using hle
  have hnOne : n = 1 := by omega
  simpa only [hnOne, pow_one] using hn

/-- If the ambient center is cyclic, any normal noncyclic subgroup of
order `p ^ 2` supplies the index-`p` centralizer needed for induction. -/
theorem centralizer_index_eq_prime_of_normal_primeSquare_noncyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hCenter : IsCyclic (Subgroup.center G))
    (E : Subgroup G) (hE : E.Normal) (hEcard : Nat.card E = p ^ 2)
    (hEnoncyclic : ¬ IsCyclic E) :
    (Subgroup.centralizer (E : Set G)).index = p := by
  apply centralizer_index_eq_prime_of_normal_primeSquare_noncentral
    hp hGp E hE hEcard
  intro hEcenter
  let : IsCyclic (Subgroup.center G) := hCenter
  exact hEnoncyclic (Subgroup.isCyclic_of_le hEcenter)

/-- The prime-order layer of a normal cyclic subgroup of a finite
`p`-group is central in the ambient group. -/
theorem pow_prime_eq_one_mem_center_of_normal_cyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (A : Subgroup G) (hA : A.Normal) (hAcyclic : IsCyclic A)
    {x : G} (hxA : x ∈ A) (hxpow : x ^ p = 1) :
    x ∈ Subgroup.center G := by
  let : Fact p.Prime := ⟨hp⟩
  let : A.Normal := hA
  rw [Subgroup.mem_center_iff]
  intro g
  obtain ⟨s, hs⟩ := hGp.exists_orderOf_eq_pow g
  let c : G →* MulAut A := MulAut.conjNormal
  have hc : c g ^ (p ^ s) = 1 := by
    rw [← map_pow, ← hs, pow_orderOf_eq_one, map_one]
  have hfix := cyclicPGroup_aut_primeKernel_fixed_of_pow_primePower_eq_one
    hp (hGp.to_subgroup A) hAcyclic (c g) hc
    (⟨x, hxA⟩ : A) (Subtype.ext hxpow)
  have hconj : g * x * g⁻¹ = x := congrArg Subtype.val hfix
  exact mul_inv_eq_iff_eq_mul.mp hconj

/-- Adjoining one element to the center gives an abelian subgroup. -/
theorem center_sup_zpowers_isMulCommutative
    {G : Type*} [Group G] (x : G) :
    IsMulCommutative (Subgroup.center G ⊔ Subgroup.zpowers x : Subgroup G) := by
  refine ⟨⟨?_⟩⟩
  intro a b
  apply Subtype.ext
  obtain ⟨z, hz, u, hu, ha⟩ := Subgroup.mem_sup_of_normal_left.mp a.2
  obtain ⟨w, hw, v, hv, hb⟩ := Subgroup.mem_sup_of_normal_left.mp b.2
  change (a : G) * (b : G) = (b : G) * (a : G)
  rw [← ha, ← hb]
  have hzAll : ∀ t : G, Commute z t := by
    intro t
    exact (Subgroup.mem_center_iff.mp hz t).symm
  have huw : Commute u w := Subgroup.mem_center_iff.mp hw u
  have huv : Commute u v := setLike_mul_comm hu hv
  exact ((hzAll (w * v)).mul_left (huw.mul_right huv)).eq

/-- In a group of class at most two, adjoining one element to the center
gives a normal subgroup. -/
theorem center_sup_zpowers_normal_of_commutator_le_center
    {G : Type*} [Group G]
    (hclass : commutator G ≤ Subgroup.center G) (x : G) :
    (Subgroup.center G ⊔ Subgroup.zpowers x : Subgroup G).Normal := by
  let A : Subgroup G := Subgroup.center G ⊔ Subgroup.zpowers x
  refine ⟨?_⟩
  intro a ha g
  have hcomm : ⁅g, a⁆ ∈ A :=
    Subgroup.mem_sup_left (hclass (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top g) (Subgroup.mem_top a)))
  have heq : g * a * g⁻¹ = ⁅g, a⁆ * a := by
    simp only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one]
  rw [heq]
  exact A.mul_mem hcomm ha

private theorem isCyclic_of_normal_abelian_cyclic_of_primePower_mul
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hNormal : ∀ A : Subgroup G,
      A.Normal → IsMulCommutative A → IsCyclic A)
    (hclass : commutator G ≤ Subgroup.center G)
    (hPowCentral : ∀ x : G, x ^ p ∈ Subgroup.center G)
    (hPowMul : ∀ x y : G, (x * y) ^ p = x ^ p * y ^ p) :
    IsCyclic G := by
  let : IsCyclic (Subgroup.center G) :=
    hNormal (Subgroup.center G) inferInstance inferInstance
  let f : G →* Subgroup.center G :=
    { toFun := fun x ↦ ⟨x ^ p, hPowCentral x⟩
      map_one' := Subtype.ext (one_pow p)
      map_mul' := fun x y ↦ Subtype.ext (hPowMul x y) }
  have hfker : f.ker ≤ Subgroup.center G := by
    intro x hx
    have hxpow : x ^ p = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    let A : Subgroup G := Subgroup.center G ⊔ Subgroup.zpowers x
    have hAnormal : A.Normal :=
      center_sup_zpowers_normal_of_commutator_le_center hclass x
    have hAcomm : IsMulCommutative A := center_sup_zpowers_isMulCommutative x
    have hAcyclic : IsCyclic A := hNormal A hAnormal hAcomm
    exact pow_prime_eq_one_mem_center_of_normal_cyclic hp hGp A hAnormal hAcyclic
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)) hxpow
  let : IsMulCommutative G :=
    f.isMulCommutative_of_isCyclic_of_ker_le_center hfker
  have hTopCyclic : IsCyclic (⊤ : Subgroup G) :=
    hNormal ⊤ inferInstance inferInstance
  exact Subgroup.topEquiv.isCyclic.mp hTopCyclic

/-- The class-two product-power formula for a pair with central
commutator. -/
theorem mul_pow_eq_of_commutator_mem_center
    {G : Type*} [Group G] (x y : G)
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) (n : ℕ) :
    (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2) := by
  have hc (z : G) : Commute z ⁅y, x⁆ :=
    Subgroup.mem_center_iff.mp hcomm z
  have hswap (m : ℕ) :
      y ^ m * x = x * y ^ m * ⁅y, x⁆ ^ m := by
    have hpow := commutatorElement_pow_left_of_mem_center y x hcomm m
    calc
      y ^ m * x = ⁅y ^ m, x⁆ * x * y ^ m := by
        simp only [commutatorElement_def]
        group
      _ = ⁅y, x⁆ ^ m * x * y ^ m := by rw [hpow]
      _ = x * y ^ m * ⁅y, x⁆ ^ m := by
        rw [← ((hc x).pow_right m).eq]
        exact ((hc (y ^ m)).symm.pow_left m).right_comm x
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (x * y) ^ (n + 1) = (x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)) * (x * y) := by
        rw [pow_succ, ih]
      _ = (x ^ n * y ^ n) * (x * y) * ⁅y, x⁆ ^ (n.choose 2) := by
        rw [mul_assoc, ← ((hc (x * y)).pow_right (n.choose 2)).eq]
        simp only [mul_assoc]
      _ = x ^ n * (y ^ n * x) * y * ⁅y, x⁆ ^ (n.choose 2) := by
        simp only [mul_assoc]
      _ = x ^ n * (x * y ^ n * ⁅y, x⁆ ^ n) * y * ⁅y, x⁆ ^ (n.choose 2) := by rw [hswap]
      _ = x ^ (n + 1) * y ^ (n + 1) * ⁅y, x⁆ ^ (n + n.choose 2) := by
        rw [pow_succ, pow_succ, pow_add]
        simp only [mul_assoc]
        rw [((hc y).symm.pow_left n).left_comm]
      _ = x ^ (n + 1) * y ^ (n + 1) * ⁅y, x⁆ ^ ((n + 1).choose 2) := by
        rw [Nat.choose_succ_succ, Nat.choose_one_right]

/-- An odd power is multiplicative when the commutator is central and
annihilated by that power. -/
theorem mul_pow_eq_mul_pow_of_odd_of_commutator_mem_center
    {G : Type*} [Group G] (x y : G) {p : ℕ} (hpOdd : Odd p)
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G)
    (hpow : ⁅y, x⁆ ^ p = 1) :
    (x * y) ^ p = x ^ p * y ^ p := by
  rw [mul_pow_eq_of_commutator_mem_center x y hcomm]
  obtain ⟨k, hk⟩ := dvd_choose_two_of_odd hpOdd
  rw [hk, pow_mul, hpow, one_pow, mul_one]

/-- A finite odd `p`-group whose normal abelian subgroups are all cyclic
is cyclic. -/
theorem isCyclic_of_odd_of_normal_abelian_cyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hpOdd : Odd p) (hGp : IsPGroup p G)
    (hNormal : ∀ A : Subgroup G,
      A.Normal → IsMulCommutative A → IsCyclic A) :
    IsCyclic G := by
  have hHall : HasCyclicCharacteristicAbelianSubgroups G := by
    intro A hA hAcomm
    let : A.Characteristic := hA
    exact hNormal A inferInstance hAcomm
  have hPhiCyclic : IsCyclic (frattini G) :=
    hNormal (frattini G) inferInstance
      (hHall.frattini_isMulCommutative hp hGp)
  have hclass : commutator G ≤ Subgroup.center G :=
    commutator_le_center_of_odd_of_frattini_isCyclic hp hpOdd hGp hPhiCyclic
  apply isCyclic_of_normal_abelian_cyclic_of_primePower_mul hp hGp hNormal hclass
  · intro x
    exact frattini_le_center_of_odd_of_isCyclic hp hpOdd hGp hPhiCyclic
      (pow_prime_mem_frattini_of_isPGroup hp hGp x)
  · intro x y
    exact mul_pow_eq_mul_pow_of_odd_of_commutator_mem_center x y hpOdd
      (hclass (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top y) (Subgroup.mem_top x)))
      (basic_commutator_pow_prime_eq_one_of_odd_of_frattini_isCyclic
        hp hpOdd hGp hPhiCyclic y x)

/-- Every finite noncyclic odd `p`-group contains a normal noncyclic
abelian subgroup. -/
theorem exists_normal_noncyclic_abelian_of_odd
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hpOdd : Odd p) (hGp : IsPGroup p G)
    (hGnoncyclic : ¬ IsCyclic G) :
    ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧ ¬ IsCyclic A := by
  by_contra hnone
  apply hGnoncyclic
  apply isCyclic_of_odd_of_normal_abelian_cyclic hp hpOdd hGp
  intro A hA hAcomm
  by_contra hAnoncyclic
  exact hnone ⟨A, hA, hAcomm, hAnoncyclic⟩

/-- Every finite noncyclic odd `p`-group contains a normal elementary
abelian subgroup of order `p ^ 2`. -/
theorem exists_normal_primeSquare_of_odd_of_not_isCyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hpOdd : Odd p) (hGp : IsPGroup p G)
    (hGnoncyclic : ¬ IsCyclic G) :
    ∃ E : Subgroup G,
      E.Normal ∧ Nat.card E = p ^ 2 ∧ IsMulCommutative E ∧
        (∀ x : E, x ^ p = 1) ∧ ¬ IsCyclic E := by
  obtain ⟨A, hA, hAcomm, hAnoncyclic⟩ :=
    exists_normal_noncyclic_abelian_of_odd hp hpOdd hGp hGnoncyclic
  obtain ⟨E, hE, _hEA, hEcard, hEcomm, hEpow, hEnoncyclic⟩ :=
    exists_normal_primeSquare_of_normal_noncyclic_abelian
      hp hGp A hA hAcomm hAnoncyclic
  exact ⟨E, hE, hEcard, hEcomm, hEpow, hEnoncyclic⟩

/-- In the cyclic-center case, the normal elementary abelian subgroup
comes with the index-`p` centralizer used by the translated-regularity
induction. -/
theorem exists_normal_primeSquare_centralizer_index_prime_of_odd
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hpOdd : Odd p) (hGp : IsPGroup p G)
    (hGnoncyclic : ¬ IsCyclic G) (hCenter : IsCyclic (Subgroup.center G)) :
    ∃ E : Subgroup G,
      E.Normal ∧ Nat.card E = p ^ 2 ∧ IsMulCommutative E ∧
        (∀ x : E, x ^ p = 1) ∧
          (Subgroup.centralizer (E : Set G)).index = p := by
  obtain ⟨E, hE, hEcard, hEcomm, hEpow, hEnoncyclic⟩ :=
    exists_normal_primeSquare_of_odd_of_not_isCyclic hp hpOdd hGp hGnoncyclic
  exact ⟨E, hE, hEcard, hEcomm, hEpow,
    centralizer_index_eq_prime_of_normal_primeSquare_noncyclic
      hp hGp hCenter E hE hEcard hEnoncyclic⟩

end LisiSabatini
