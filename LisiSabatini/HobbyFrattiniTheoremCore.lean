module

public import LisiSabatini.NormalPrimeSquareCentralizer
public import LisiSabatini.NormalPGroupFlags
public import LisiSabatini.FrattiniQuotientEquality
public import LisiSabatini.ClassTwoFrattini
public import LisiSabatini.CyclicFrattiniOmega
public import LisiSabatini.HallPGroupStructure

/-!
# Proof core for Hobby's theorem on Frattini subgroups of finite p-groups

Charles Hobby proved that a noncommutative finite `p`-group with cyclic
center cannot occur as the Frattini subgroup of a finite `p`-group.  This
file develops the induction used in Theorem 1 of

* C. Hobby, *The Frattini subgroup of a p-group*, Pacific J. Math. 10
  (1960), 209--212.

The first section records a small index lemma used repeatedly in Hobby's
proof.  The second section formalizes Hobby's Lemma 4: a Frattini subgroup
of order `p ^ 3` is necessarily commutative.  The remaining induction is
built above these reusable statements.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open Subgroup

open scoped IsMulCommutative

theorem isMulCommutative_of_isCyclic
    {A : Type*} [Group A] (hA : IsCyclic A) : IsMulCommutative A := by
  let : IsCyclic A := hA
  exact IsCyclic.isMulCommutative

/-! ## The prime-order layer of a finite abelian p-group -/

private theorem primePowerKernel_card_le
    {p : ℕ} {A : Type*} [CommGroup A] [Finite A]
    (hker : Nat.card (powMonoidHom p : A →* A).ker ≤ p) :
    ∀ k : ℕ, Nat.card (powMonoidHom (p ^ k) : A →* A).ker ≤ p ^ k := by
  intro k
  induction k with
  | zero =>
      simp only [pow_zero]
      have hkerOne : (powMonoidHom 1 : A →* A).ker = ⊥ := by
        ext x
        simp
      rw [hkerOne, Subgroup.card_bot]
  | succ k ih =>
      let Ks : Subgroup A := (powMonoidHom (p ^ (k + 1)) : A →* A).ker
      let Kk : Subgroup A := (powMonoidHom (p ^ k) : A →* A).ker
      let f : Ks →* Kk :=
        ((powMonoidHom p : A →* A).domRestrict Ks).codRestrict Kk (by
          intro x
          rw [MonoidHom.mem_ker]
          change ((x : A) ^ p) ^ (p ^ k) = 1
          rw [← pow_mul]
          have hx : (x : A) ^ p ^ (k + 1) = 1 := by
            simpa only [Ks, MonoidHom.mem_ker, powMonoidHom_apply] using x.2
          simpa only [pow_succ, mul_comm] using hx)
      have hfkerCard : Nat.card f.ker ≤ p := by
        let kerToK1 : f.ker → (powMonoidHom p : A →* A).ker := fun x ↦
          ⟨(x : A), by
            rw [MonoidHom.mem_ker]
            exact congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)⟩
        have hinj : Function.Injective kerToK1 := by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          exact congrArg
            (fun z : (powMonoidHom p : A →* A).ker ↦ (z : A)) hxy
        exact (Nat.card_le_card_of_injective kerToK1 hinj).trans hker
      have hfrangeCard : Nat.card f.range ≤ p ^ k := by
        calc
          Nat.card f.range ≤ Nat.card (⊤ : Subgroup Kk) :=
            f.range.card_le_of_le le_top
          _ = Nat.card Kk := Subgroup.card_top
          _ = Nat.card (powMonoidHom (p ^ k) : A →* A).ker := rfl
          _ ≤ p ^ k := ih
      calc
        Nat.card (powMonoidHom (p ^ (k + 1)) : A →* A).ker =
            Nat.card f.ker * Nat.card f.range := by
          change Nat.card Ks = _
          rw [← Subgroup.index_ker f]
          exact f.ker.card_mul_index.symm
        _ ≤ p * p ^ k := Nat.mul_le_mul hfkerCard hfrangeCard
        _ = p ^ (k + 1) := by rw [pow_succ, mul_comm]

/-- A finite abelian `p`-group with at most `p` elements killed by the
`p`th-power map is cyclic. -/
theorem isCyclic_of_isPGroup_of_natCard_primeKernel_le_prime
    {p : ℕ} {A : Type*} [CommGroup A] [Finite A]
    (hp : p.Prime) (hAp : IsPGroup p A)
    (hker : Nat.card (powMonoidHom p : A →* A).ker ≤ p) :
    IsCyclic A := by
  let : Fact p.Prime := ⟨hp⟩
  classical
  let := Fintype.ofFinite A
  apply isCyclic_of_card_pow_eq_one_le
  intro n hn
  obtain ⟨s, hAcard⟩ := IsPGroup.iff_card.mp hAp
  obtain ⟨k, _hk, hgcd⟩ :=
    (Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right n (p ^ s))
  have hkerEq :
      (powMonoidHom n : A →* A).ker =
        (powMonoidHom (p ^ k) : A →* A).ker := by
    ext x
    simp only [MonoidHom.mem_ker, powMonoidHom_apply]
    rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_dvd_iff_pow_eq_one]
    constructor
    · intro hxn
      rw [← hgcd]
      apply Nat.dvd_gcd hxn
      rw [← hAcard]
      exact orderOf_dvd_natCard x
    · intro hxgcd
      exact hxgcd.trans (hgcd ▸ Nat.gcd_dvd_left n (p ^ s))
  let e : {a : A // a ^ n = 1} ≃
      (powMonoidHom n : A →* A).ker :=
    { toFun := fun a ↦ ⟨a.1, by
        change a.1 ^ n = 1
        exact a.2⟩
      invFun := fun a ↦ ⟨a.1, by exact a.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  calc
    ({a : A | a ^ n = 1} : Finset A).card =
        Fintype.card {a : A // a ^ n = 1} :=
      (Fintype.card_subtype _).symm
    _ = Nat.card (powMonoidHom n : A →* A).ker := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_congr e
    _ = Nat.card (powMonoidHom (p ^ k) : A →* A).ker := by rw [hkerEq]
    _ ≤ p ^ k := primePowerKernel_card_le hker k
    _ ≤ n := hgcd ▸ Nat.gcd_le_left (p ^ s) hn

/-- The `p`-torsion layer of a finite noncyclic abelian `p`-group has at
least `p ^ 2` elements.  This is the finite-abelian input in Hobby's
induction. -/
theorem prime_sq_le_natCard_powMonoidHom_ker_of_not_isCyclic
    {p : ℕ} {A : Type*} [CommGroup A] [Finite A]
    (hp : p.Prime) (hAp : IsPGroup p A) (hnot : ¬ IsCyclic A) :
    p ^ 2 ≤ Nat.card (powMonoidHom p : A →* A).ker := by
  let : Fact p.Prime := ⟨hp⟩
  let : Nontrivial A := Nontrivial.of_not_isCyclic hnot
  let K : Subgroup A := (powMonoidHom p : A →* A).ker
  obtain ⟨C, _hCnormal, _hCtop, hCcard, _hCcenter⟩ :=
    exists_normal_central_subgroup_card_prime_le
      hp hAp (⊤ : Subgroup A) inferInstance top_ne_bot
  have hCK : C ≤ K := by
    intro c hc
    rw [MonoidHom.mem_ker]
    have hcpow : (⟨c, hc⟩ : C) ^ p = 1 := by
      rw [← hCcard]
      exact pow_card_eq_one'
    exact congrArg Subtype.val hcpow
  have hpLeK : p ≤ Nat.card K := by
    rw [← hCcard]
    exact C.card_le_of_le hCK
  by_contra hlt
  have hKLt : Nat.card K < p ^ 2 := Nat.lt_of_not_ge hlt
  have hKp : IsPGroup p K := hAp.to_subgroup K
  obtain ⟨k, hkcard⟩ := IsPGroup.iff_card.mp hKp
  have hkOne : k = 1 := by
    have hkGe : 1 ≤ k := by
      apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
      simpa only [pow_one, ← hkcard] using hpLeK
    have hkLt : k < 2 := by
      apply (Nat.pow_lt_pow_iff_right hp.one_lt).mp
      simpa only [← hkcard] using hKLt
    omega
  apply hnot
  apply isCyclic_of_isPGroup_of_natCard_primeKernel_le_prime hp hAp
  rw [show (powMonoidHom p : A →* A).ker = K from rfl,
    hkcard, hkOne, pow_one]

/-! ## Subgroups of index at most p contain the Frattini subgroup -/

/-- In a finite `p`-group, every subgroup of index at most `p` contains the
Frattini subgroup.  If the subgroup is proper, its `p`-power index is exactly
`p`, hence it is maximal. -/
theorem frattini_le_of_index_le_prime
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (K : Subgroup G) (hindex : K.index ≤ p) :
    frattini G ≤ K := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hKtop : K = ⊤
  · simpa only [hKtop] using (show frattini G ≤ (⊤ : Subgroup G) from le_top)
  obtain ⟨n, hn⟩ := hGp.index K
  have hnpos : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hnzero
    apply hKtop
    apply Subgroup.index_eq_one.mp
    rw [hn, hnzero, pow_zero]
  have hnle : n ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right hp.one_lt).mp
    calc
      p ^ n = K.index := hn.symm
      _ ≤ p := hindex
      _ = p ^ 1 := (pow_one p).symm
  have hnOne : n = 1 := by omega
  have hKindex : K.index = p := by
    rw [hn, hnOne, pow_one]
  have hKcoatom : IsCoatom K := by
    refine ⟨hKtop, ?_⟩
    intro L hKL
    have hdiv : L.index ∣ p := by
      rw [← hKindex]
      exact Subgroup.index_dvd_of_le hKL.le
    rcases (Nat.dvd_prime hp).mp hdiv with hLindex | hLindex
    · exact Subgroup.index_eq_one.mp hLindex
    · have hcardEq : Nat.card K = Nat.card L := by
        have hKmul := K.card_mul_index
        have hLmul := L.card_mul_index
        rw [hKindex] at hKmul
        rw [hLindex] at hLmul
        exact Nat.mul_right_cancel hp.pos (hKmul.trans hLmul.symm)
      have hKLeq : K = L :=
        Subgroup.eq_of_le_of_card_ge hKL.le hcardEq.symm.le
      exact (hKL.ne hKLeq).elim
  exact frattini_le_coatom hKcoatom

/-! ## Cardinal preliminaries for Hobby's Lemma 3 -/

/-- The `p`-torsion layer of a cyclic subgroup of order `p ^ 2` has
cardinality exactly `p`. -/
theorem natCard_subgroupPrimeKernel_eq_prime_of_isCyclic_prime_sq
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (A : Subgroup G)
    (hAcyclic : IsCyclic A) (hAcard : Nat.card A = p ^ 2) :
    Nat.card
      (subgroupPrimeKernel p A (isMulCommutative_of_isCyclic hAcyclic)) = p := by
  let : IsCyclic A := hAcyclic
  let : IsMulCommutative A := isMulCommutative_of_isCyclic hAcyclic
  let K0 := (powMonoidHom p : A →* A).ker
  have hK0card : Nat.card K0 = p := by
    calc
      Nat.card K0 = (Nat.card A).gcd p :=
        IsCyclic.card_powMonoidHom_ker A p
      _ = (p ^ 2).gcd p := by rw [hAcard]
      _ = p := Nat.gcd_eq_right_iff_dvd.mpr
        (dvd_pow_self p (show 2 ≠ 0 by omega))
  change Nat.card (K0.map A.subtype) = p
  rw [Subgroup.card_map_of_injective A.subtype_injective, hK0card]

/-- If `A ≤ N` have orders `p ^ 2` and `p ^ 3`, respectively, then
the image of `N` in the quotient by the normal subgroup `A` has order `p`. -/
theorem natCard_map_quotient_eq_prime_of_prime_sq_prime_cube
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (A N : Subgroup G) (hAnormal : A.Normal)
    (hAN : A ≤ N) (hAcard : Nat.card A = p ^ 2)
    (hNcard : Nat.card N = p ^ 3) :
    Nat.card (N.map (QuotientGroup.mk' A)) = p := by
  let : A.Normal := hAnormal
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let f : N →* G ⧸ A := q.domRestrict N
  have hfker : f.ker = A.subgroupOf N := by
    change (q.ker.subgroupOf N) = A.subgroupOf N
    rw [show q.ker = A by
      simpa only [q] using (QuotientGroup.ker_mk' (G := G) (N := A))]
  have hfrange : f.range = N.map q := by
    change (q.domRestrict N).range = N.map q
    exact MonoidHom.domRestrict_range N q
  have hAsubCard : Nat.card (A.subgroupOf N) = p ^ 2 := by
    calc
      Nat.card (A.subgroupOf N) = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
      _ = p ^ 2 := hAcard
  have hmul : Nat.card f.ker * Nat.card f.range = Nat.card N := by
    rw [← Subgroup.index_ker f]
    exact f.ker.card_mul_index
  rw [hfker, hfrange, hAsubCard, hNcard] at hmul
  have hmul' : p ^ 2 * Nat.card (N.map q) = p ^ 2 * p := by
    simpa only [pow_succ] using hmul
  exact Nat.mul_left_cancel (pow_pos hp.pos 2) hmul'

/-- A commutative group of order `p ^ 2` in which every element is killed by
the `p`th-power map is noncyclic. -/
theorem not_isCyclic_of_natCard_eq_prime_sq_of_pow_eq_one
    {p : ℕ} {A : Type*} [CommGroup A] [Finite A]
    (hp : p.Prime) (hcard : Nat.card A = p ^ 2)
    (hexp : ∀ a : A, a ^ p = 1) :
    ¬ IsCyclic A := by
  intro hcyc
  let : IsCyclic A := hcyc
  have hkerCard := IsCyclic.card_powMonoidHom_ker A p
  have hkerTop : (powMonoidHom p : A →* A).ker = ⊤ := by
    ext a
    simp only [MonoidHom.mem_ker, powMonoidHom_apply, Subgroup.mem_top]
    constructor
    · intro _
      trivial
    · intro _
      exact hexp a
  rw [hkerTop, Subgroup.card_top, hcard] at hkerCard
  have hSqEqP : p ^ 2 = p := hkerCard.trans
    (Nat.gcd_eq_right_iff_dvd.mpr (dvd_pow_self p (by omega)))
  have : p < p ^ 2 := by
    simpa only [pow_one] using
      Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by omega)
  omega

/-! ## Hobby's Lemma 3 -/

/-- Hobby's Lemma 3, in a form stable under lifting from a central quotient.

Let `N = A ⋁ ⟨b⟩` be an ambient-normal commutative subgroup of order
`p ^ 3`, contained in `Φ(G)`, where `A` is an ambient-normal cyclic subgroup
of order `p ^ 2` already central in `Φ(G)` and `b ^ p` is ambient-central.
Then all of `N` is central in `Φ(G)`.  Hobby's direct-product statement is
the special case `b ^ p = 1`; the slightly stronger hypothesis used here is
what one obtains by lifting the `p`-torsion layer of a central quotient.

The quotient `N/A` is a normal subgroup of order `p` in `G/A`, hence is
central.  Consequently every conjugate of `b` differs from `b` by an element
of the `p`-torsion layer of `A`, a set of cardinality `p`.  The conjugacy
orbit of `b` therefore has cardinality at most `p`; its centralizer has index
at most `p` and so contains the Frattini subgroup. -/
theorem hobby_lemma_three
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (A N : Subgroup G) (hAnormal : A.Normal) (hNnormal : N.Normal)
    (hAN : A ≤ N) (hNPhi : N ≤ frattini G)
    (hAcard : Nat.card A = p ^ 2) (hNcard : Nat.card N = p ^ 3)
    (hAcyclic : IsCyclic A) (hNcomm : IsMulCommutative N)
    (hAcenter : A ≤ characteristicCenterImage (frattini G))
    (b : G) (hbN : b ∈ N) (hbpCenter : b ^ p ∈ Subgroup.center G)
    (hNgen : N = A ⊔ Subgroup.zpowers b) :
    N ≤ characteristicCenterImage (frattini G) := by
  let : Fact p.Prime := ⟨hp⟩
  let : A.Normal := hAnormal
  let : N.Normal := hNnormal
  let : IsMulCommutative N := hNcomm
  let hAcomm : IsMulCommutative A := isMulCommutative_of_isCyclic hAcyclic
  let K : Subgroup G := subgroupPrimeKernel p A hAcomm
  have hKcard : Nat.card K = p :=
    natCard_subgroupPrimeKernel_eq_prime_of_isCyclic_prime_sq
      A hAcyclic hAcard
  let q : G →* G ⧸ A := QuotientGroup.mk' A
  let Nbar : Subgroup (G ⧸ A) := N.map q
  have hNbarNormal : Nbar.Normal :=
    hNnormal.map q (QuotientGroup.mk'_surjective A)
  have hNbarCard : Nat.card Nbar = p := by
    exact natCard_map_quotient_eq_prime_of_prime_sq_prime_cube
      hp A N hAnormal hAN hAcard hNcard
  have hQp : IsPGroup p (G ⧸ A) := hGp.to_quotient A
  have hNbarCenter : Nbar ≤ Subgroup.center (G ⧸ A) :=
    normal_subgroup_le_center_of_natCard_eq_prime
      hp hQp Nbar hNbarNormal hNbarCard
  have hconjMod (g : G) :
      b⁻¹ * (g * b * g⁻¹) ∈ A := by
    rw [← QuotientGroup.eq_one_iff]
    have hbNbar : q b ∈ Nbar := Subgroup.mem_map_of_mem q hbN
    have hcomm : q g * q b = q b * q g :=
      Subgroup.mem_center_iff.mp (hNbarCenter hbNbar) (q g)
    change q b⁻¹ * (q g * q b * (q g)⁻¹) = 1
    rw [hcomm]
    simp [mul_assoc]
  let orbitConjugator (x : MulAction.orbit (ConjAct G) b) : ConjAct G :=
    Classical.choose (MulAction.mem_orbit_iff.mp x.2)
  have orbitConjugator_spec (x : MulAction.orbit (ConjAct G) b) :
      orbitConjugator x • b = x :=
    Classical.choose_spec (MulAction.mem_orbit_iff.mp x.2)
  let orbitToK : MulAction.orbit (ConjAct G) b → K := fun x ↦ by
    let g : ConjAct G := orbitConjugator x
    have hg : g • b = x := orbitConjugator_spec x
    have hxN : (x : G) ∈ N := by
      rw [← hg, ConjAct.smul_def]
      exact hNnormal.conj_mem b hbN (ConjAct.ofConjAct g)
    have hxpow : (x : G) ^ p = b ^ p := by
      rw [← hg, ConjAct.smul_def]
      calc
        (ConjAct.ofConjAct g * b * (ConjAct.ofConjAct g)⁻¹) ^ p =
            (MulAut.conj (ConjAct.ofConjAct g)) (b ^ p) :=
          (map_pow (MulAut.conj (ConjAct.ofConjAct g)) b p).symm
        _ = b ^ p := by
          change (ConjAct.ofConjAct g) * b ^ p *
              (ConjAct.ofConjAct g)⁻¹ = b ^ p
          exact mul_inv_eq_iff_eq_mul.mpr
            (Subgroup.mem_center_iff.mp hbpCenter (ConjAct.ofConjAct g))
    have hcommBx : Commute b (x : G) := by
      exact congrArg Subtype.val
        (mul_comm (⟨b, hbN⟩ : N) (⟨x, hxN⟩ : N))
    refine ⟨b⁻¹ * (x : G), ?_⟩
    apply (mem_subgroupPrimeKernel_iff hAcomm _).mpr
    refine ⟨?_, ?_⟩
    · rw [← hg, ConjAct.smul_def]
      exact hconjMod (ConjAct.ofConjAct g)
    · rw [hcommBx.inv_left.mul_pow, inv_pow, hxpow]
      simp
  have horbitToKInjective : Function.Injective orbitToK := by
    intro x y hxy
    apply Subtype.ext
    have hxy' := congrArg Subtype.val hxy
    dsimp only [orbitToK] at hxy'
    have hxy'' := congrArg (fun z : G ↦ b * z) hxy'
    simpa [mul_assoc] using hxy''
  have horbitCard :
      Nat.card (MulAction.orbit (ConjAct G) b) ≤ p := by
    calc
      Nat.card (MulAction.orbit (ConjAct G) b) ≤ Nat.card K :=
        Nat.card_le_card_of_injective orbitToK horbitToKInjective
      _ = p := hKcard
  have hcentralizerIndex : (Subgroup.centralizer ({b} : Set G)).index ≤ p := by
    have hindexComap :
        (Subgroup.comap ConjAct.toConjAct.toMonoidHom
          (MulAction.stabilizer (ConjAct G) b)).index =
          (MulAction.stabilizer (ConjAct G) b).index :=
      Subgroup.index_comap_of_surjective
        (H := MulAction.stabilizer (ConjAct G) b)
        ConjAct.toConjAct.surjective
    calc
      (Subgroup.centralizer ({b} : Set G)).index =
          (Subgroup.comap ConjAct.toConjAct.toMonoidHom
            (MulAction.stabilizer (ConjAct G) b)).index := by
        rw [Subgroup.centralizer_eq_comap_stabilizer]
      _ = (MulAction.stabilizer (ConjAct G) b).index := hindexComap
      _ = (MulAction.orbit (ConjAct G) b).ncard :=
        MulAction.index_stabilizer (ConjAct G) b
      _ = Nat.card (MulAction.orbit (ConjAct G) b) :=
        (Nat.card_coe_set_eq _).symm
      _ ≤ p := horbitCard
  have hPhiCentralizesB :
      frattini G ≤ Subgroup.centralizer ({b} : Set G) :=
    frattini_le_of_index_le_prime hp hGp _ hcentralizerIndex
  have hbCenter : b ∈ characteristicCenterImage (frattini G) := by
    rw [characteristicCenterImage_eq_inf_centralizer]
    refine ⟨hNPhi hbN, ?_⟩
    intro h hh
    exact (hPhiCentralizesB hh b (Set.mem_singleton b)).symm
  rw [hNgen]
  refine sup_le hAcenter ?_
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  exact (characteristicCenterImage (frattini G)).zpow_mem hbCenter n

/-! ## Hobby's theorem -/

/-- **Hobby's theorem.**  The Frattini subgroup of a finite `p`-group is
commutative whenever its center is cyclic.

The proof follows Hobby's minimal-counterexample induction.  Quotient by an
ambient-central subgroup `C` of order `p`.  The induction hypothesis forces
the center of the quotient Frattini subgroup to be noncyclic.  Its
`p`-torsion layer therefore contains an ambient-normal flag of orders `p`
and `p ^ 2`.  Lifting the flag gives `M ≤ N ≤ Φ(G)` of orders `p ^ 2`
and `p ^ 3`.  Lemma 1 makes `M` central in `Φ(G)`; cyclicity of the center
makes `M` cyclic, and `N / M` cyclic makes `N` commutative.  A generator
lift now satisfies the strengthened hypotheses of `hobby_lemma_three`, so
`N` is central in `Φ(G)`, contradicting the noncyclic order-`p ^ 2` image
of `N` in the quotient. -/
theorem frattini_isMulCommutative_of_center_isCyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hCenter : IsCyclic (Subgroup.center (frattini G))) :
    IsMulCommutative (frattini G) := by
  induction hn : Nat.card (frattini G) using Nat.strong_induction_on generalizing G with
  | h n ih =>
      let : Fact p.Prime := ⟨hp⟩
      by_contra hnotComm
      have hPhiNe : frattini G ≠ ⊥ := by
        intro hbot
        apply hnotComm
        rw [hbot]
        infer_instance
      obtain ⟨C, hCnormal, hCPhi, hCcard, hCcenter⟩ :=
        exists_normal_central_subgroup_card_prime_le
          hp hGp (frattini G) inferInstance hPhiNe
      let : C.Normal := hCnormal
      let q : G →* G ⧸ C := QuotientGroup.mk' C
      have hQp : IsPGroup p (G ⧸ C) := hGp.to_quotient C
      have hPhiMap :
          (frattini G).map q = frattini (G ⧸ C) := by
        simpa only [q] using map_frattini_quotient_eq_frattini C hCPhi
      have hPhiComap :
          (frattini (G ⧸ C)).comap q = frattini G := by
        simpa only [q] using comap_frattini_quotient_eq_frattini C hCPhi
      have hcardFactor :
          n = p * Nat.card (frattini (G ⧸ C)) := by
        calc
          n = Nat.card (frattini G) := hn.symm
          _ = Nat.card ((frattini (G ⧸ C)).comap q) := by rw [hPhiComap]
          _ = Nat.card C * Nat.card (frattini (G ⧸ C)) := by
            simpa only [q] using
              natCard_comap_quotient_eq_mul C hCnormal
                (frattini (G ⧸ C))
          _ = p * Nat.card (frattini (G ⧸ C)) := by rw [hCcard]
      have hcardLt : Nat.card (frattini (G ⧸ C)) < n := by
        rw [hcardFactor]
        exact lt_mul_of_one_lt_left Nat.card_pos hp.one_lt
      have hZbarNot :
          ¬ IsCyclic (Subgroup.center (frattini (G ⧸ C))) := by
        intro hZbarCyclic
        have hPhiQcomm : IsMulCommutative (frattini (G ⧸ C)) :=
          ih _ hcardLt hQp hZbarCyclic rfl
        let : IsMulCommutative (frattini (G ⧸ C)) := hPhiQcomm
        have hcenterTop :
            Subgroup.center (frattini (G ⧸ C)) = ⊤ := by
          ext x
          simp only [Subgroup.mem_center_iff, Subgroup.mem_top, iff_true]
          intro y
          exact (mul_comm x y).symm
        have hPhiQCyclic : IsCyclic (frattini (G ⧸ C)) := by
          rw [hcenterTop] at hZbarCyclic
          exact Subgroup.topEquiv.isCyclic.mp hZbarCyclic
        let r : frattini G →* G ⧸ C := q.domRestrict (frattini G)
        have hrange : r.range = frattini (G ⧸ C) := by
          simpa only [r] using
            (MonoidHom.domRestrict_range (frattini G) q).trans hPhiMap
        have hrangeCyclic : IsCyclic r.range := by
          rw [hrange]
          exact hPhiQCyclic
        let : IsCyclic r.range := hrangeCyclic
        have hkerCenter : r.rangeRestrict.ker ≤ Subgroup.center (frattini G) := by
          intro x hx
          have hxq := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
          change q (x : G) = 1 at hxq
          have hxC : (x : G) ∈ C :=
            (QuotientGroup.eq_one_iff (x : G)).mp hxq
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          exact Subgroup.mem_center_iff.mp (hCcenter hxC) y
        apply hnotComm
        exact MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
          r.rangeRestrict hkerCenter
      let Z : Subgroup (G ⧸ C) :=
        characteristicCenterImage (frattini (G ⧸ C))
      have hZcomm : IsMulCommutative Z :=
        characteristicCenterImage_isMulCommutative (frattini (G ⧸ C))
      let groupZ : Group Z := inferInstance
      let : CommGroup Z := { groupZ with mul_comm := hZcomm.1.1 }
      have hZNot : ¬ IsCyclic Z := by
        intro hZcyclic
        apply hZbarNot
        exact (Subgroup.equivMapOfInjective
          (Subgroup.center (frattini (G ⧸ C)))
          (frattini (G ⧸ C)).subtype
          Subtype.coe_injective).isCyclic.mpr hZcyclic
      let P : Subgroup (G ⧸ C) := subgroupPrimeKernel p Z hZcomm
      have hPchar : P.Characteristic := by
        let : Z.Characteristic :=
          characteristicCenterImage_characteristic (frattini (G ⧸ C))
        unfold P subgroupPrimeKernel
        apply characteristic_map_subtype
        exact powMonoidHom_ker_characteristic Z p
      have hPcard : p ^ 2 ≤ Nat.card P := by
        have hOmega := prime_sq_le_natCard_powMonoidHom_ker_of_not_isCyclic
          hp (hQp.to_subgroup Z) hZNot
        change p ^ 2 ≤ Nat.card
          (((powMonoidHom p : Z →* Z).ker).map Z.subtype)
        rw [Subgroup.card_map_of_injective Z.subtype_injective]
        exact hOmega
      let : P.Characteristic := hPchar
      obtain ⟨Mbar, Nbar, hMbarNormal, hNbarNormal, hMbarNbar,
          hNbarP, hMbarCard, hNbarCard, _hMbarCenter⟩ :=
        exists_normal_flag_card_prime_prime_sq_le
          hp hQp P (inferInstance : P.Normal) hPcard
      let M : Subgroup G := Mbar.comap q
      let N : Subgroup G := Nbar.comap q
      have hMnormal : M.Normal := hMbarNormal.comap q
      have hNnormal : N.Normal := hNbarNormal.comap q
      have hMN : M ≤ N := Subgroup.comap_mono hMbarNbar
      have hPZ : P ≤ Z := by
        intro x hx
        exact (mem_subgroupPrimeKernel_iff hZcomm x).mp hx |>.1
      have hZPhi : Z ≤ frattini (G ⧸ C) := by
        change characteristicCenterImage (frattini (G ⧸ C)) ≤
          frattini (G ⧸ C)
        rw [characteristicCenterImage_eq_inf_centralizer]
        exact inf_le_left
      have hNbarPhi : Nbar ≤ frattini (G ⧸ C) :=
        hNbarP.trans (hPZ.trans hZPhi)
      have hNPhi : N ≤ frattini G := by
        rw [← hPhiComap]
        exact Subgroup.comap_mono hNbarPhi
      have hMPhi : M ≤ frattini G := hMN.trans hNPhi
      have hMcard : Nat.card M = p ^ 2 := by
        calc
          Nat.card M = Nat.card C * Nat.card Mbar := by
            exact natCard_comap_quotient_eq_mul C hCnormal Mbar
          _ = p * p := by rw [hCcard, hMbarCard]
          _ = p ^ 2 := (pow_two p).symm
      have hNcard : Nat.card N = p ^ 3 := by
        calc
          Nat.card N = Nat.card C * Nat.card Nbar := by
            exact natCard_comap_quotient_eq_mul C hCnormal Nbar
          _ = p * p ^ 2 := by rw [hCcard, hNbarCard]
          _ = p ^ 3 := by ring
      have hcentIndex :
          (Subgroup.centralizer (M : Set G)).index ≤ p :=
        centralizer_index_le_prime_of_normal_natCard_eq_prime_sq
          hp hGp M hMnormal hMcard
      have hPhiCentralizesM :
          frattini G ≤ Subgroup.centralizer (M : Set G) :=
        frattini_le_of_index_le_prime hp hGp _ hcentIndex
      have hMcenter : M ≤ characteristicCenterImage (frattini G) := by
        rw [characteristicCenterImage_eq_inf_centralizer]
        refine le_inf hMPhi ?_
        intro m hm h hh
        exact (hPhiCentralizesM hh m hm).symm
      have hCenterImageCyclic :
          IsCyclic (characteristicCenterImage (frattini G)) :=
        (Subgroup.equivMapOfInjective
          (Subgroup.center (frattini G)) (frattini G).subtype
          Subtype.coe_injective).isCyclic.mp hCenter
      have hMcyclic : IsCyclic M := by
        let : IsCyclic (characteristicCenterImage (frattini G)) :=
          hCenterImageCyclic
        exact Subgroup.isCyclic_of_le hMcenter
      let Msub : Subgroup N := M.subgroupOf N
      have hMsubNormal : Msub.Normal := hMnormal.subgroupOf N
      let : Msub.Normal := hMsubNormal
      have hMsubCenter : Msub ≤ Subgroup.center N := by
        intro m hm
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        have hmCenter := hMcenter hm
        rw [characteristicCenterImage_eq_inf_centralizer] at hmCenter
        exact hmCenter.2 x (hNPhi x.2)
      have hMsubCard : Nat.card Msub = p ^ 2 := by
        calc
          Nat.card Msub = Nat.card M :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
          _ = p ^ 2 := hMcard
      have hMsubIndex : Msub.index = p := by
        have hmul := Msub.card_mul_index
        rw [hMsubCard, hNcard] at hmul
        have hmul' : p ^ 2 * Msub.index = p ^ 2 * p := by
          simpa only [pow_succ] using hmul
        exact Nat.mul_left_cancel (pow_pos hp.pos 2) hmul'
      have hquotCard : Nat.card (N ⧸ Msub) = p := by
        rw [← Msub.index_eq_card]
        exact hMsubIndex
      have hquotCyclic : IsCyclic (N ⧸ Msub) :=
        isCyclic_of_prime_card hquotCard
      let : IsCyclic (N ⧸ Msub) := hquotCyclic
      have hNcomm : IsMulCommutative N :=
        MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
          (QuotientGroup.mk' Msub)
          (by simpa only [QuotientGroup.ker_mk'] using hMsubCenter)
      have hNbarComm : IsMulCommutative Nbar := ⟨⟨fun x y ↦ by
        exact Subtype.ext (congrArg (fun z : Z ↦ (z : G ⧸ C))
          (hZcomm.1.1
            (⟨x, hPZ (hNbarP x.2)⟩ : Z)
            (⟨y, hPZ (hNbarP y.2)⟩ : Z)))⟩⟩
      let groupNbar : Group Nbar := inferInstance
      let : CommGroup Nbar := { groupNbar with mul_comm := hNbarComm.1.1 }
      have hNbarExp : ∀ x : Nbar, x ^ p = 1 := by
        intro x
        apply Subtype.ext
        exact (mem_subgroupPrimeKernel_iff hZcomm x).mp
          (hNbarP x.2) |>.2
      have hNbarNot : ¬ IsCyclic Nbar :=
        not_isCyclic_of_natCard_eq_prime_sq_of_pow_eq_one
          hp hNbarCard hNbarExp
      obtain ⟨bq, hbqGen⟩ :=
        IsCyclic.exists_generator (α := N ⧸ Msub)
      obtain ⟨bN, hbNlift⟩ :=
        QuotientGroup.mk'_surjective Msub bq
      let b : G := bN
      have hbN : b ∈ N := bN.2
      have hbqTop : Subgroup.zpowers bq = ⊤ :=
        (Subgroup.zpowers bq).eq_top_iff'.mpr hbqGen
      let S : Subgroup N := Msub ⊔ Subgroup.zpowers bN
      have hSmap : S.map (QuotientGroup.mk' Msub) = ⊤ := by
        dsimp only [S]
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, hbNlift, hbqTop]
        exact sup_eq_right.mpr le_top
      have hkerS : (QuotientGroup.mk' Msub).ker ≤ S := by
        rw [QuotientGroup.ker_mk']
        exact le_sup_left
      have hStop : S = ⊤ := by
        rw [← Subgroup.comap_map_eq_self hkerS, hSmap, Subgroup.comap_top]
      have hNgen : N = M ⊔ Subgroup.zpowers b := by
        rw [← N.range_subtype, MonoidHom.range_eq_map, ← hStop]
        dsimp only [S]
        rw [Subgroup.map_sup,
          Subgroup.map_subgroupOf_eq_of_le hMN,
          MonoidHom.map_zpowers]
        rfl
      have hqbNbar : q b ∈ Nbar := by
        change q (bN : G) ∈ Nbar
        exact bN.2
      have hqbp : (q b) ^ p = 1 :=
        (mem_subgroupPrimeKernel_iff hZcomm (q b)).mp
          (hNbarP hqbNbar) |>.2
      have hbpCenter : b ^ p ∈ Subgroup.center G := by
        apply hCcenter
        apply (QuotientGroup.eq_one_iff (b ^ p)).mp
        change q (b ^ p) = 1
        rw [map_pow]
        exact hqbp
      have hNcenter : N ≤ characteristicCenterImage (frattini G) :=
        hobby_lemma_three hp hGp M N hMnormal hNnormal hMN hNPhi
          hMcard hNcard hMcyclic hNcomm hMcenter b hbN hbpCenter hNgen
      have hNcyclic : IsCyclic N := by
        let : IsCyclic (characteristicCenterImage (frattini G)) :=
          hCenterImageCyclic
        exact Subgroup.isCyclic_of_le hNcenter
      let f : N →* Nbar :=
        (q.domRestrict N).codRestrict Nbar (fun x ↦ x.2)
      have hfsurj : Function.Surjective f := by
        intro y
        obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective C y.1
        have hgN : g ∈ N := by
          change q g ∈ Nbar
          simpa only [q] using hg.symm ▸ y.2
        refine ⟨⟨g, hgN⟩, ?_⟩
        apply Subtype.ext
        exact hg
      apply hNbarNot
      let : IsCyclic N := hNcyclic
      exact isCyclic_of_surjective f hfsurj

/-- Hall's cyclic-characteristic-abelian hypothesis supplies Hobby's cyclic
center assumption for the Frattini subgroup, so its Frattini subgroup is
commutative without any separate Hobby certificate. -/
theorem HasCyclicCharacteristicAbelianSubgroups.frattini_isMulCommutative
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hHall : HasCyclicCharacteristicAbelianSubgroups G)
    (hp : p.Prime) (hGp : IsPGroup p G) :
    IsMulCommutative (frattini G) :=
  frattini_isMulCommutative_of_center_isCyclic hp hGp
    (hHall.characteristic_center_isCyclic (frattini G))

end LisiSabatini
