module

public import LisiSabatini.AlternatingSylowCycleProfile
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Prime-cycle support in the iterated Sylow wreath product

This file proves the coefficient recurrence at the remaining genuine
group-theoretic source: the action of the iterated regular wreath
product on `p^k` points.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

/-- The additive cyclic group of order `p`, regarded multiplicatively. -/
abbrev PrimeCycleGroup (p : ℕ) :=
  Multiplicative (ZMod p)

theorem natCard_primeCycleGroup
    {p : ℕ} (hp : p.Prime) :
    Nat.card (PrimeCycleGroup p) = p := by
  let : Fact p.Prime := ⟨hp⟩
  simp [PrimeCycleGroup, ZMod.card]

/-- The cardinal recurrence for mathlib's iterated regular wreath
product agrees with `sylowTowerOrder`. -/
theorem natCard_iteratedWreathProduct_eq_sylowTowerOrder
    (G : Type*) [Group G] [Finite G] (k : ℕ) :
    Nat.card (IteratedWreathProduct G k) =
      sylowTowerOrder (Nat.card G) k := by
  induction k with
  | zero =>
      simp [sylowTowerOrder]
  | succ k ih =>
      rw [IteratedWreathProduct_succ,
        RegularWreathProduct.card, ih]
      simp [sylowTowerOrder, Nat.mul_comm]

theorem primeCycleGroup_pow_prime
    {p : ℕ} [Fact p.Prime]
    (q : PrimeCycleGroup p) :
    q ^ p = 1 := by
  apply Multiplicative.ext
  change p • q.toAdd = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

theorem cycleType_card_eq_card_support_div_prime
    {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℕ} [hp : Fact p.Prime]
    (σ : Equiv.Perm α) (hσ : σ ^ p = 1) :
    σ.cycleType.card = σ.support.card / p := by
  have hsum := σ.sum_cycleType
  rw [Equiv.Perm.cycleType_of_pow_prime_eq_one hσ,
    Multiset.sum_replicate, nsmul_eq_mul, Nat.cast_id] at hsum
  rw [← hsum, Nat.mul_div_cancel _ hp.out.pos]

theorem card_support_eq_cycleType_card_mul_prime
    {α : Type*} [Fintype α] [DecidableEq α]
    {p : ℕ} [Fact p.Prime]
    (σ : Equiv.Perm α) (hσ : σ ^ p = 1) :
    σ.support.card = σ.cycleType.card * p := by
  have hsum := σ.sum_cycleType
  rw [Equiv.Perm.cycleType_of_pow_prime_eq_one hσ,
    Multiset.sum_replicate, nsmul_eq_mul,
    Nat.cast_id] at hsum
  exact hsum.symm

theorem card_support_permCongr
    {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support.card = σ.support.card := by
  let E :
      {x : α // x ∈ σ.support} ≃
        {y : β // y ∈ (e.permCongr σ).support} :=
    {
    toFun x :=
      ⟨e x, by
        rw [Equiv.Perm.mem_support,
          Equiv.permCongr_apply, e.symm_apply_apply]
        have hx : σ x ≠ x :=
          Equiv.Perm.mem_support.mp x.property
        exact fun h ↦ hx (e.injective h)⟩
    invFun y :=
      ⟨e.symm y, by
        rw [Equiv.Perm.mem_support]
        intro h
        have hy :
            e.permCongr σ y ≠ y :=
          Equiv.Perm.mem_support.mp y.property
        apply hy
        simpa only [Equiv.permCongr_apply,
          e.apply_symm_apply] using congrArg e h⟩
    left_inv x := by
      apply Subtype.ext
      exact e.symm_apply_apply x
    right_inv y := by
      apply Subtype.ext
      exact e.apply_symm_apply y
    }
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr E).symm

@[simp]
theorem regularWreathToPerm_apply
    {D Q Λ : Type*} [Group D] [Group Q]
    [MulAction D Λ]
    (w : D ≀ᵣ Q) (x : Λ × Q) :
    RegularWreathProduct.toPerm D Q Λ w x =
      ((w.left (w.right * x.2)) • x.1,
        w.right * x.2) :=
  rfl

theorem card_support_regularWreathToPerm_of_right_ne_one
    {D Q Λ : Type*} [Group D] [Group Q]
    [MulAction D Λ] [Fintype Λ] [Fintype Q]
    [DecidableEq Λ] [DecidableEq Q]
    (w : D ≀ᵣ Q) (hw : w.right ≠ 1) :
    (RegularWreathProduct.toPerm D Q Λ w).support.card =
      Fintype.card Λ * Fintype.card Q := by
  have hs :
      (RegularWreathProduct.toPerm D Q Λ w).support =
        Finset.univ := by
    apply Finset.eq_univ_of_forall
    rintro ⟨x, q⟩
    rw [Equiv.Perm.mem_support]
    intro hfixed
    have hright : w.right * q = q :=
      congrArg Prod.snd hfixed
    apply hw
    exact mul_right_cancel (hright.trans (one_mul q).symm)
  rw [hs, Finset.card_univ, Fintype.card_prod]

theorem card_support_regularWreathToPerm_of_right_eq_one
    {D Q Λ : Type*} [Group D] [Group Q]
    [MulAction D Λ] [Fintype Λ] [Fintype Q]
    [DecidableEq Λ] [DecidableEq Q]
    (w : D ≀ᵣ Q) (hw : w.right = 1) :
    (RegularWreathProduct.toPerm D Q Λ w).support.card =
      ∑ q : Q,
        (MulAction.toPermHom D Λ (w.left q)).support.card := by
  have hmem (x : Λ) (q : Q) :
      (x, q) ∈
          (RegularWreathProduct.toPerm D Q Λ w).support ↔
        x ∈
          (MulAction.toPermHom D Λ (w.left q)).support := by
    rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support]
    simp only [regularWreathToPerm_apply, hw, one_mul,
      MulAction.toPermHom_apply, MulAction.toPerm_apply]
    change
      (w.left q • x, q) ≠ (x, q) ↔
        w.left q • x ≠ x
    constructor
    · intro hpair hfirst
      exact hpair (Prod.ext hfirst rfl)
    · intro hfirst hpair
      exact hfirst (congrArg Prod.fst hpair)
  let E :
      {z : Λ × Q //
        z ∈ (RegularWreathProduct.toPerm D Q Λ w).support} ≃
      (Σ q : Q,
        {x : Λ //
          x ∈ (MulAction.toPermHom D Λ
            (w.left q)).support}) :=
    {
      toFun z :=
        ⟨z.1.2, ⟨z.1.1, (hmem z.1.1 z.1.2).mp z.2⟩⟩
      invFun z :=
        ⟨(z.2.1, z.1), (hmem z.2.1 z.1).mpr z.2.2⟩
      left_inv z := by
        apply Subtype.ext
        rfl
      right_inv z := by
        exact
          Sigma.ext rfl
            (heq_of_eq (Subtype.ext rfl))
    }
  calc
    (RegularWreathProduct.toPerm D Q Λ w).support.card =
        Fintype.card
          (Σ q : Q,
            {x : Λ //
              x ∈ (MulAction.toPermHom D Λ
                (w.left q)).support}) := by
      simpa only [Fintype.card_coe] using
        Fintype.card_congr E
    _ =
        ∑ q : Q,
          (MulAction.toPermHom D Λ
            (w.left q)).support.card := by
      simp only [Fintype.card_sigma, Fintype.card_coe]

theorem card_support_iteratedWreathToPermHom_succ_of_right_ne_one
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (k : ℕ) (w : IteratedWreathProduct G (k + 1))
    (hw : w.right ≠ 1) :
    (iteratedWreathToPermHom G (k + 1) w).support.card =
      Nat.card G ^ k * Nat.card G := by
  classical
  let _ :=
    MulAction.compHom (Fin k → G)
      (iteratedWreathToPermHom G k)
  change
    (((Fin.succFunEquiv G k).symm.permCongr
      (RegularWreathProduct.toPerm
        (IteratedWreathProduct G k) G
        (Fin k → G) w)).support.card) =
      Nat.card G ^ k * Nat.card G
  rw [card_support_permCongr,
    card_support_regularWreathToPerm_of_right_ne_one
      w hw]
  simp

theorem card_support_iteratedWreathToPermHom_succ_of_right_eq_one
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    (k : ℕ) (w : IteratedWreathProduct G (k + 1))
    (hw : w.right = 1) :
    (iteratedWreathToPermHom G (k + 1) w).support.card =
      ∑ q : G,
        (iteratedWreathToPermHom G k
          (w.left q)).support.card := by
  let _ :=
    MulAction.compHom (Fin k → G)
      (iteratedWreathToPermHom G k)
  change
    (((Fin.succFunEquiv G k).symm.permCongr
      (RegularWreathProduct.toPerm
        (IteratedWreathProduct G k) G
        (Fin k → G) w)).support.card) =
      ∑ q : G,
        (iteratedWreathToPermHom G k
          (w.left q)).support.card
  rw [card_support_permCongr,
    card_support_regularWreathToPerm_of_right_eq_one
      w hw]
  rfl

theorem pow_left_of_right_eq_one
    {D Q : Type*} [Group D] [Group Q]
    (w : D ≀ᵣ Q) (hw : w.right = 1)
    (m : ℕ) (q : Q) :
    (w ^ m).left q = (w.left q) ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hright :
          (w ^ m).right = 1 := by
        change RegularWreathProduct.rightHom (w ^ m) = 1
        rw [map_pow, RegularWreathProduct.rightHom_eq_right,
          hw, one_pow]
      rw [pow_succ, RegularWreathProduct.mul_left]
      change
        (w ^ m).left q *
            w.left ((w ^ m).right⁻¹ * q) =
          (w.left q) ^ (m + 1)
      rw [ih, hright]
      simp [pow_succ]

theorem pow_eq_one_iff_left_pow_eq_one_of_right_eq_one
    {D Q : Type*} [Group D] [Group Q]
    (w : D ≀ᵣ Q) (hw : w.right = 1)
    (m : ℕ) :
    w ^ m = 1 ↔ ∀ q : Q, (w.left q) ^ m = 1 := by
  constructor
  · intro hpow q
    rw [← pow_left_of_right_eq_one w hw m q,
      hpow, RegularWreathProduct.one_left]
    rfl
  · intro hleft
    apply RegularWreathProduct.ext
    · funext q
      rw [pow_left_of_right_eq_one w hw m q,
        hleft q, RegularWreathProduct.one_left]
      rfl
    · change RegularWreathProduct.rightHom (w ^ m) = 1
      rw [map_pow, RegularWreathProduct.rightHom_eq_right,
        hw, one_pow]

theorem pow_eq_one_of_pow_left_one_of_right_pow_eq_one
    {D Q : Type*} [Group D] [Group Q]
    (w : D ≀ᵣ Q) (m : ℕ)
    (hright : w.right ^ m = 1)
    (hleft : (w ^ m).left 1 = 1)
    (hgenerate :
      ∀ x : Q, x ∈ Submonoid.powers w.right) :
    w ^ m = 1 := by
  have hvright : (w ^ m).right = 1 := by
    change RegularWreathProduct.rightHom (w ^ m) = 1
    rw [map_pow, RegularWreathProduct.rightHom_eq_right,
      hright]
  have hcomm :
      w ^ m * w = w * w ^ m :=
    (pow_succ w m).symm.trans (pow_succ' w m)
  apply RegularWreathProduct.ext
  · funext x
    obtain ⟨n, rfl⟩ :=
      (Submonoid.mem_powers_iff x w.right).mp
        (hgenerate x)
    induction n with
    | zero =>
        simpa using hleft
    | succ n ih =>
        have hcoord :=
          congrArg
            (fun z : D ≀ᵣ Q ↦
              z.left (w.right ^ (n + 1)))
            hcomm
        change
          (w ^ m).left (w.right ^ (n + 1)) *
              w.left
                ((w ^ m).right⁻¹ *
                  w.right ^ (n + 1)) =
            w.left (w.right ^ (n + 1)) *
              (w ^ m).left
                (w.right⁻¹ *
                  w.right ^ (n + 1)) at hcoord
        rw [hvright] at hcoord
        have horbit :
            w.right⁻¹ * w.right ^ (n + 1) =
              w.right ^ n := by
          rw [pow_succ']
          simp
        simp only [inv_one, one_mul, horbit, ih,
          RegularWreathProduct.one_left, Pi.one_apply,
          mul_one] at hcoord
        exact
          mul_right_cancel
            (hcoord.trans
              (one_mul
                (w.left
                  (w.right ^ (n + 1)))).symm)
  · exact hvright

theorem primeCycleWreath_pow_eq_one_iff_pow_left_one
    {D : Type*} [Group D]
    {p : ℕ} [hp : Fact p.Prime]
    (f : PrimeCycleGroup p → D)
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    (⟨f, q⟩ : D ≀ᵣ PrimeCycleGroup p) ^ p = 1 ↔
      ((⟨f, q⟩ : D ≀ᵣ PrimeCycleGroup p) ^ p).left 1 =
        1 := by
  constructor
  · intro hpow
    rw [hpow, RegularWreathProduct.one_left]
    rfl
  · intro hleft
    apply
      pow_eq_one_of_pow_left_one_of_right_pow_eq_one
        (⟨f, q⟩ : D ≀ᵣ PrimeCycleGroup p) p
        (primeCycleGroup_pow_prime q) hleft
    intro x
    exact
      mem_powers_of_prime_card
        (natCard_primeCycleGroup hp.out) hq

/-- Ordered (and therefore noncommutative) product of a finite
sequence. -/
def orderedFinProduct
    {D : Type*} [Group D] {n : ℕ}
    (a : Fin n → D) : D :=
  (List.ofFn a).prod

theorem orderedFinProduct_succ
    {D : Type*} [Group D] {n : ℕ}
    (a : Fin (n + 1) → D) :
    orderedFinProduct a =
      orderedFinProduct
          (fun i : Fin n ↦ a i.castSucc) *
        a (Fin.last n) := by
  rw [orderedFinProduct, List.ofFn_succ',
    List.prod_concat]
  rfl

/-- Complete a finite sequence by the unique last entry making its
ordered product equal to one. -/
def completeOrderedProductOne
    {D : Type*} [Group D] {n : ℕ}
    (a : Fin n → D) :
    Fin (n + 1) → D :=
  Fin.lastCases (orderedFinProduct a)⁻¹ a

@[simp]
theorem completeOrderedProductOne_castSucc
    {D : Type*} [Group D] {n : ℕ}
    (a : Fin n → D) (i : Fin n) :
    completeOrderedProductOne a i.castSucc = a i := by
  simp [completeOrderedProductOne]

@[simp]
theorem completeOrderedProductOne_last
    {D : Type*} [Group D] {n : ℕ}
    (a : Fin n → D) :
    completeOrderedProductOne a (Fin.last n) =
      (orderedFinProduct a)⁻¹ := by
  simp [completeOrderedProductOne]

theorem orderedFinProduct_completeOrderedProductOne
    {D : Type*} [Group D] {n : ℕ}
    (a : Fin n → D) :
    orderedFinProduct (completeOrderedProductOne a) = 1 := by
  rw [orderedFinProduct_succ]
  simp

/-- Sequences of length `n+1` with ordered product one are equivalent
to their first `n` entries. -/
def orderedProductOneEquivPrefix
    (D : Type*) [Group D] (n : ℕ) :
    {a : Fin (n + 1) → D //
      orderedFinProduct a = 1} ≃
      (Fin n → D) where
  toFun a i := a.1 i.castSucc
  invFun a :=
    ⟨completeOrderedProductOne a,
      orderedFinProduct_completeOrderedProductOne a⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · have hprod :
          orderedFinProduct
                (fun j : Fin n ↦ a.1 j.castSucc) *
              a.1 (Fin.last n) =
            1 := by
        rw [← orderedFinProduct_succ]
        exact a.2
      change
        completeOrderedProductOne
            (fun j : Fin n ↦ a.1 j.castSucc)
            (Fin.last n) =
          a.1 (Fin.last n)
      rw [completeOrderedProductOne_last]
      exact inv_eq_of_mul_eq_one_right hprod
    · simp
  right_inv a := by
    funext i
    simp

/-- Transport the length of a product-one sequence. -/
def orderedProductOneEquivCongr
    (D : Type*) [Group D] {m n : ℕ} (h : m = n) :
    {a : Fin m → D // orderedFinProduct a = 1} ≃
      {a : Fin n → D // orderedFinProduct a = 1} := by
  subst n
  exact Equiv.refl _

theorem wreath_pow_left_eq_orderedFinProduct
    {D Q : Type*} [Group D] [Group Q]
    (f : Q → D) (q x : Q) (m : ℕ) :
    ((⟨f, q⟩ : D ≀ᵣ Q) ^ m).left x =
      orderedFinProduct
        (fun i : Fin m ↦
          f ((q ^ (i : ℕ))⁻¹ * x)) := by
  induction m with
  | zero =>
      simp [orderedFinProduct]
  | succ m ih =>
      have hright :
          ((⟨f, q⟩ : D ≀ᵣ Q) ^ m).right =
            q ^ m := by
        change
          RegularWreathProduct.rightHom
              ((⟨f, q⟩ : D ≀ᵣ Q) ^ m) =
            q ^ m
        rw [map_pow]
        rfl
      rw [pow_succ, RegularWreathProduct.mul_left]
      change
        ((⟨f, q⟩ : D ≀ᵣ Q) ^ m).left x *
            f ((((⟨f, q⟩ : D ≀ᵣ Q) ^ m).right)⁻¹ *
              x) =
          orderedFinProduct
            (fun i : Fin (m + 1) ↦
              f ((q ^ (i : ℕ))⁻¹ * x))
      rw [ih, hright, orderedFinProduct_succ]
      rfl

/-- The inverse powers of a nonidentity element list the prime cyclic
group exactly once. -/
noncomputable def primeCycleInversePowersEquiv
    {p : ℕ} [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    Fin p ≃ PrimeCycleGroup p := by
  let orbit :
      Fin p → PrimeCycleGroup p :=
    fun i ↦ (q ^ (i : ℕ))⁻¹
  have horder : orderOf q = p :=
    orderOf_eq_prime (primeCycleGroup_pow_prime q) hq
  apply Equiv.ofBijective orbit
  constructor
  · intro i j hij
    apply Fin.ext
    apply pow_injOn_Iio_orderOf (x := q)
    · simpa only [Set.mem_Iio, horder] using i.isLt
    · simpa only [Set.mem_Iio, horder] using j.isLt
    · exact inv_injective hij
  · intro x
    have hxpow :
        x⁻¹ ∈ Submonoid.powers q :=
      mem_powers_of_prime_card
        (natCard_primeCycleGroup hp.out) hq
    obtain ⟨n, hn⟩ :=
      (Submonoid.mem_powers_iff x⁻¹ q).mp hxpow
    refine
      ⟨⟨n % p, Nat.mod_lt _ hp.out.pos⟩, ?_⟩
    change (q ^ (n % p))⁻¹ = x
    have hmod :
        n % p = n % orderOf q :=
      congrArg (n % ·) horder.symm
    rw [hmod, pow_mod_orderOf, hn, inv_inv]

@[simp]
theorem primeCycleInversePowersEquiv_apply
    {p : ℕ} [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1)
    (i : Fin p) :
    primeCycleInversePowersEquiv q hq i =
      (q ^ (i : ℕ))⁻¹ :=
  rfl

/-- Reindex functions on the prime cyclic group by the inverse-power
ordering. -/
noncomputable def primeCycleInversePowersFunctionEquiv
    (D : Type*) {p : ℕ} [Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    (PrimeCycleGroup p → D) ≃ (Fin p → D) :=
  ((primeCycleInversePowersEquiv q hq).arrowCongr
    (Equiv.refl D)).symm

@[simp]
theorem primeCycleInversePowersFunctionEquiv_apply
    (D : Type*) {p : ℕ} [Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1)
    (f : PrimeCycleGroup p → D) (i : Fin p) :
    primeCycleInversePowersFunctionEquiv D q hq f i =
      f ((q ^ (i : ℕ))⁻¹) :=
  rfl

/-- Above a nontrivial top coordinate, the `p`-torsion condition is
exactly one ordered product equation. -/
noncomputable def primeCycleWreathTorsionEquivProductOne
    (D : Type*) [Group D]
    {p : ℕ} [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    {f : PrimeCycleGroup p → D //
      (⟨f, q⟩ : D ≀ᵣ PrimeCycleGroup p) ^ p = 1} ≃
      {a : Fin p → D // orderedFinProduct a = 1} :=
  Equiv.subtypeEquiv
    (primeCycleInversePowersFunctionEquiv D q hq)
    (fun f ↦ by
      rw [primeCycleWreath_pow_eq_one_iff_pow_left_one
        f q hq,
        wreath_pow_left_eq_orderedFinProduct f q 1 p]
      have hseq :
          (fun i : Fin p ↦
              f ((q ^ (i : ℕ))⁻¹ * 1)) =
            primeCycleInversePowersFunctionEquiv
              D q hq f := by
        funext i
        simp
      rw [hseq])

/-- Product-one sequences of prime length are freely determined by
their first `p-1` entries. -/
noncomputable def orderedProductOneEquivPred
    (D : Type*) [Group D]
    (p : ℕ) (hp : 0 < p) :
    {a : Fin p → D // orderedFinProduct a = 1} ≃
      (Fin (p - 1) → D) :=
  (orderedProductOneEquivCongr D
      (Nat.sub_add_cancel hp).symm).trans
    (orderedProductOneEquivPrefix D (p - 1))

/-- Hence the base tuples giving `p`-torsion above a nontrivial top
coordinate are freely parametrized by `p-1` group elements. -/
noncomputable def primeCycleWreathTorsionEquivPrefix
    (D : Type*) [Group D]
    {p : ℕ} [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    {f : PrimeCycleGroup p → D //
      (⟨f, q⟩ : D ≀ᵣ PrimeCycleGroup p) ^ p = 1} ≃
      (Fin (p - 1) → D) :=
  (primeCycleWreathTorsionEquivProductOne
      D q hq).trans
    (orderedProductOneEquivPred D p hp.out.pos)

theorem cycleType_card_iteratedWreath_succ_of_right_eq_one
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {p : ℕ} [hp : Fact p.Prime]
    (k : ℕ) (w : IteratedWreathProduct G (k + 1))
    (hw : w.right = 1) (hpow : w ^ p = 1) :
    (iteratedWreathToPermHom G (k + 1) w).cycleType.card =
      ∑ q : G,
        (iteratedWreathToPermHom G k
          (w.left q)).cycleType.card := by
  have hpermPow :
      (iteratedWreathToPermHom G (k + 1) w) ^ p = 1 := by
    rw [← map_pow, hpow, map_one]
  have hleft :
      ∀ q : G, (w.left q) ^ p = 1 :=
    (pow_eq_one_iff_left_pow_eq_one_of_right_eq_one
      w hw p).mp hpow
  have hleftPerm (q : G) :
      (iteratedWreathToPermHom G k
        (w.left q)) ^ p = 1 := by
    rw [← map_pow, hleft q, map_one]
  rw [cycleType_card_eq_card_support_div_prime
    _ hpermPow,
    card_support_iteratedWreathToPermHom_succ_of_right_eq_one
      k w hw]
  calc
    (∑ q : G,
          (iteratedWreathToPermHom G k
            (w.left q)).support.card) / p =
        (∑ q : G,
          (iteratedWreathToPermHom G k
            (w.left q)).cycleType.card * p) / p := by
      congr 1
      apply Finset.sum_congr rfl
      intro q _hq
      exact
        card_support_eq_cycleType_card_mul_prime
          _ (hleftPerm q)
    _ =
        ((∑ q : G,
          (iteratedWreathToPermHom G k
            (w.left q)).cycleType.card) * p) / p := by
      rw [Finset.sum_mul]
    _ =
        ∑ q : G,
          (iteratedWreathToPermHom G k
            (w.left q)).cycleType.card :=
      Nat.mul_div_cancel _ hp.out.pos

theorem cycleType_card_iteratedWreath_succ_of_right_ne_one
    {G : Type*} [Group G] [Fintype G] [DecidableEq G]
    {p : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p)
    (k : ℕ) (w : IteratedWreathProduct G (k + 1))
    (hw : w.right ≠ 1) (hpow : w ^ p = 1) :
    (iteratedWreathToPermHom G (k + 1) w).cycleType.card =
      p ^ k := by
  have hpermPow :
      (iteratedWreathToPermHom G (k + 1) w) ^ p = 1 := by
    rw [← map_pow, hpow, map_one]
  rw [cycleType_card_eq_card_support_div_prime
      _ hpermPow,
    card_support_iteratedWreathToPermHom_succ_of_right_ne_one
      k w hw,
    hG,
    Nat.mul_div_cancel _ hp.out.pos]

/-- The monomial contributed by one element of the iterated wreath
product, or zero when that element is not `p`-torsion. -/
def iteratedWreathCycleWeight
    (p k : ℕ) [Fact p.Prime]
    (w : IteratedWreathProduct (PrimeCycleGroup p) k) :
    Polynomial ℕ := by
  classical
  exact
    if w ^ p = 1 then
      Polynomial.X ^
        (iteratedWreathToPermHom
          (PrimeCycleGroup p) k w).cycleType.card
    else 0

/-- Cycle-profile enumerator of the `p`-torsion elements in the
canonical action of the `k`-fold regular wreath product. -/
def iteratedWreathCycleProfile (p k : ℕ) [Fact p.Prime] :
    Polynomial ℕ :=
  by
    classical
    letI : Fintype (IteratedWreathProduct (PrimeCycleGroup p) k) :=
      Fintype.ofFinite _
    exact
      ∑ w : IteratedWreathProduct (PrimeCycleGroup p) k,
        iteratedWreathCycleWeight p k w

/-- The part of the successor profile with prescribed top
coordinate. -/
def iteratedWreathCycleProfileFiber
    (p k : ℕ) [Fact p.Prime]
    (q : PrimeCycleGroup p) :
    Polynomial ℕ := by
  classical
  letI : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
    Fintype.ofFinite _
  letI : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) (k + 1)) :=
    Fintype.ofFinite _
  exact
    ∑ f : PrimeCycleGroup p →
        IteratedWreathProduct (PrimeCycleGroup p) k,
      iteratedWreathCycleWeight p (k + 1)
        (⟨f, q⟩ :
          IteratedWreathProduct
            (PrimeCycleGroup p) (k + 1))

/-- Base tuples producing a `p`-torsion element above a prescribed
nontrivial top coordinate. -/
def nontrivialTopTorsionBase
    (p k : ℕ) [Fact p.Prime]
    (q : PrimeCycleGroup p) :
    Finset
      (PrimeCycleGroup p →
        IteratedWreathProduct (PrimeCycleGroup p) k) := by
  classical
  letI : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
    Fintype.ofFinite _
  exact
    Finset.univ.filter fun f ↦
      (⟨f, q⟩ :
        IteratedWreathProduct
          (PrimeCycleGroup p) (k + 1)) ^ p = 1

/-- The concrete finite fiber is the product-one fiber parametrized
above. -/
noncomputable def nontrivialTopTorsionBaseEquivPrefix
    (p k : ℕ) [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    {f : PrimeCycleGroup p →
          IteratedWreathProduct (PrimeCycleGroup p) k //
      f ∈ nontrivialTopTorsionBase p k q} ≃
      (Fin (p - 1) →
        IteratedWreathProduct (PrimeCycleGroup p) k) :=
  (Equiv.subtypeEquiv
      (Equiv.refl
        (PrimeCycleGroup p →
          IteratedWreathProduct (PrimeCycleGroup p) k))
      (fun f ↦ by
        simp [nontrivialTopTorsionBase])).trans
    (primeCycleWreathTorsionEquivPrefix
      (IteratedWreathProduct (PrimeCycleGroup p) k)
      q hq)

theorem card_nontrivialTopTorsionBase
    (p k : ℕ) [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    (nontrivialTopTorsionBase p k q).card =
      Nat.card
          (IteratedWreathProduct
            (PrimeCycleGroup p) k) ^ (p - 1) := by
  classical
  let : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
    Fintype.ofFinite _
  calc
    (nontrivialTopTorsionBase p k q).card =
        Fintype.card
          {f : PrimeCycleGroup p →
                IteratedWreathProduct
                  (PrimeCycleGroup p) k //
            f ∈ nontrivialTopTorsionBase p k q} := by
      rw [Fintype.card_coe]
    _ =
        Fintype.card
          (Fin (p - 1) →
            IteratedWreathProduct
              (PrimeCycleGroup p) k) :=
      Fintype.card_congr
        (nontrivialTopTorsionBaseEquivPrefix
          p k q hq)
    _ =
        Nat.card
            (IteratedWreathProduct
              (PrimeCycleGroup p) k) ^ (p - 1) := by
      rw [Fintype.card_fun, Fintype.card_fin,
        Nat.card_eq_fintype_card]

theorem iteratedWreathCycleWeight_mk_one
    (p k : ℕ) [hp : Fact p.Prime]
    (f : PrimeCycleGroup p →
      IteratedWreathProduct (PrimeCycleGroup p) k) :
    iteratedWreathCycleWeight p (k + 1)
        (⟨f, 1⟩ :
          IteratedWreathProduct
            (PrimeCycleGroup p) (k + 1)) =
      ∏ q : PrimeCycleGroup p,
        iteratedWreathCycleWeight p k (f q) := by
  classical
  let : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
    Fintype.ofFinite _
  let w :
      IteratedWreathProduct
        (PrimeCycleGroup p) (k + 1) :=
    ⟨f, 1⟩
  have hw : w.right = 1 := rfl
  by_cases hall :
      ∀ q : PrimeCycleGroup p, (f q) ^ p = 1
  · have hpow : w ^ p = 1 :=
      (pow_eq_one_iff_left_pow_eq_one_of_right_eq_one
        w hw p).mpr hall
    unfold iteratedWreathCycleWeight
    rw [ite_eq_left hpow]
    simp_rw [ite_eq_left (hall _)]
    change
      (Polynomial.X : Polynomial ℕ) ^
          (iteratedWreathToPermHom
            (PrimeCycleGroup p) (k + 1) w).cycleType.card =
        ∏ q : PrimeCycleGroup p,
          (Polynomial.X : Polynomial ℕ) ^
            (iteratedWreathToPermHom
              (PrimeCycleGroup p) k
              (f q)).cycleType.card
    rw [cycleType_card_iteratedWreath_succ_of_right_eq_one
      k w hw hpow]
    exact
      (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun q : PrimeCycleGroup p ↦
          (iteratedWreathToPermHom
            (PrimeCycleGroup p) k
            (f q)).cycleType.card)
        (Polynomial.X : Polynomial ℕ)).symm
  · obtain ⟨q, hq⟩ := Classical.not_forall.mp hall
    have hnotPow : w ^ p ≠ 1 := by
      intro hpow
      exact hq
        ((pow_eq_one_iff_left_pow_eq_one_of_right_eq_one
          w hw p).mp hpow q)
    unfold iteratedWreathCycleWeight
    rw [ite_eq_right hnotPow]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ q)
    rw [ite_eq_right hq]

theorem iteratedWreathCycleProfileFiber_one
    (p k : ℕ) [hp : Fact p.Prime] :
    iteratedWreathCycleProfileFiber p k 1 =
      iteratedWreathCycleProfile p k ^ p := by
  classical
  let : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
    Fintype.ofFinite _
  rw [iteratedWreathCycleProfileFiber]
  simp_rw [iteratedWreathCycleWeight_mk_one]
  calc
    (∑ f : PrimeCycleGroup p →
          IteratedWreathProduct (PrimeCycleGroup p) k,
        ∏ q : PrimeCycleGroup p,
          iteratedWreathCycleWeight p k (f q)) =
        ∏ q : PrimeCycleGroup p,
          ∑ w : IteratedWreathProduct
              (PrimeCycleGroup p) k,
            iteratedWreathCycleWeight p k w :=
      (Fintype.prod_sum
        (fun _q : PrimeCycleGroup p ↦
          fun w : IteratedWreathProduct
              (PrimeCycleGroup p) k ↦
            iteratedWreathCycleWeight p k w)).symm
    _ =
        ∏ _q : PrimeCycleGroup p,
          iteratedWreathCycleProfile p k := by
      simp only [iteratedWreathCycleProfile]
    _ =
        iteratedWreathCycleProfile p k ^
          Fintype.card (PrimeCycleGroup p) := by
      rw [Finset.prod_const, Finset.card_univ]
    _ =
        iteratedWreathCycleProfile p k ^ p := by
      rw [← Nat.card_eq_fintype_card,
        natCard_primeCycleGroup hp.out]

theorem iteratedWreathCycleProfileFiber_ne_one
    (p k : ℕ) [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    iteratedWreathCycleProfileFiber p k q =
      Polynomial.C
          (nontrivialTopTorsionBase p k q).card *
        Polynomial.X ^ (p ^ k) := by
  classical
  let : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
    Fintype.ofFinite _
  rw [iteratedWreathCycleProfileFiber]
  simp only [iteratedWreathCycleWeight]
  rw [← Finset.sum_filter]
  change
    (∑ f ∈ nontrivialTopTorsionBase p k q,
      Polynomial.X ^
        (iteratedWreathToPermHom
          (PrimeCycleGroup p) (k + 1)
          (⟨f, q⟩ :
            IteratedWreathProduct
              (PrimeCycleGroup p) (k + 1))).cycleType.card) =
      Polynomial.C
          (nontrivialTopTorsionBase p k q).card *
        Polynomial.X ^ (p ^ k)
  calc
    (∑ f ∈ nontrivialTopTorsionBase p k q,
        Polynomial.X ^
          (iteratedWreathToPermHom
            (PrimeCycleGroup p) (k + 1)
            (⟨f, q⟩ :
              IteratedWreathProduct
                (PrimeCycleGroup p) (k + 1))).cycleType.card) =
        ∑ _f ∈ nontrivialTopTorsionBase p k q,
          Polynomial.X ^ (p ^ k) := by
      apply Finset.sum_congr rfl
      intro f hf
      have hpow :
          (⟨f, q⟩ :
            IteratedWreathProduct
              (PrimeCycleGroup p) (k + 1)) ^ p = 1 :=
        (Finset.mem_filter.mp hf).2
      rw [cycleType_card_iteratedWreath_succ_of_right_ne_one
        (natCard_primeCycleGroup hp.out) k
        (⟨f, q⟩ :
          IteratedWreathProduct
            (PrimeCycleGroup p) (k + 1))
        hq hpow]
    _ =
        (nontrivialTopTorsionBase p k q).card •
          (Polynomial.X ^ (p ^ k) : Polynomial ℕ) := by
      rw [Finset.sum_const]
    _ =
        Polynomial.C
            (nontrivialTopTorsionBase p k q).card *
          Polynomial.X ^ (p ^ k) := by
      simpa only [← Polynomial.C_eq_natCast, Nat.cast_id] using
        (Polynomial.natCast_mul
          (R := ℕ)
          (nontrivialTopTorsionBase p k q).card
          (Polynomial.X ^ (p ^ k))).symm

theorem iteratedWreathCycleProfileFiber_ne_one_exact
    (p k : ℕ) [hp : Fact p.Prime]
    (q : PrimeCycleGroup p) (hq : q ≠ 1) :
    iteratedWreathCycleProfileFiber p k q =
      Polynomial.C
          (sylowTowerOrder p k ^ (p - 1)) *
        Polynomial.X ^ (p ^ k) := by
  rw [iteratedWreathCycleProfileFiber_ne_one
      p k q hq,
    card_nontrivialTopTorsionBase p k q hq,
    natCard_iteratedWreathProduct_eq_sylowTowerOrder,
    natCard_primeCycleGroup hp.out]

theorem iteratedWreathCycleProfile_succ_eq_sum_fibers
    (p k : ℕ) [Fact p.Prime] :
    iteratedWreathCycleProfile p (k + 1) =
      ∑ q : PrimeCycleGroup p,
        iteratedWreathCycleProfileFiber p k q := by
  classical
  let : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
    Fintype.ofFinite _
  let : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) (k + 1)) :=
    Fintype.ofFinite _
  let lower :=
    IteratedWreathProduct (PrimeCycleGroup p) k
  let : Fintype
      (lower ≀ᵣ PrimeCycleGroup p) :=
    Fintype.ofFinite _
  calc
    iteratedWreathCycleProfile p (k + 1) =
        ∑ z :
            (PrimeCycleGroup p → lower) ×
              PrimeCycleGroup p,
          iteratedWreathCycleWeight p (k + 1)
            (⟨z.1, z.2⟩ :
              IteratedWreathProduct
                (PrimeCycleGroup p) (k + 1)) := by
      rw [iteratedWreathCycleProfile]
      exact
        Fintype.sum_equiv
          (RegularWreathProduct.equivProd
            lower (PrimeCycleGroup p))
          _ _ (fun _w ↦ rfl)
    _ =
        ∑ f : PrimeCycleGroup p → lower,
          ∑ q : PrimeCycleGroup p,
            iteratedWreathCycleWeight p (k + 1)
              (⟨f, q⟩ :
                IteratedWreathProduct
                  (PrimeCycleGroup p) (k + 1)) := by
      rw [Fintype.sum_prod_type]
    _ =
        ∑ q : PrimeCycleGroup p,
          ∑ f : PrimeCycleGroup p → lower,
            iteratedWreathCycleWeight p (k + 1)
              (⟨f, q⟩ :
                IteratedWreathProduct
                  (PrimeCycleGroup p) (k + 1)) := by
      rw [Finset.sum_comm]
    _ =
        ∑ q : PrimeCycleGroup p,
          iteratedWreathCycleProfileFiber p k q := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [iteratedWreathCycleProfileFiber]

theorem sum_iteratedWreathCycleProfileFiber_ne_one
    (p k : ℕ) [hp : Fact p.Prime] :
    (∑ q ∈
        (Finset.univ :
          Finset (PrimeCycleGroup p)).erase 1,
      iteratedWreathCycleProfileFiber p k q) =
        Polynomial.C
            ((p - 1) *
              sylowTowerOrder p k ^ (p - 1)) *
          Polynomial.X ^ (p ^ k) := by
  classical
  let a := sylowTowerOrder p k ^ (p - 1)
  have hcard :
      ((Finset.univ :
        Finset (PrimeCycleGroup p)).erase 1).card =
          p - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1),
      Finset.card_univ,
      ← Nat.card_eq_fintype_card,
      natCard_primeCycleGroup hp.out]
  calc
    (∑ q ∈
        (Finset.univ :
          Finset (PrimeCycleGroup p)).erase 1,
      iteratedWreathCycleProfileFiber p k q) =
        ∑ _q ∈
            (Finset.univ :
              Finset (PrimeCycleGroup p)).erase 1,
          Polynomial.C a *
            Polynomial.X ^ (p ^ k) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [iteratedWreathCycleProfileFiber_ne_one_exact
        p k q (Finset.mem_erase.mp hq).1]
    _ =
        (p - 1) •
          (Polynomial.C a *
            Polynomial.X ^ (p ^ k) : Polynomial ℕ) := by
      rw [Finset.sum_const, hcard]
    _ =
        Polynomial.C ((p - 1) * a) *
          Polynomial.X ^ (p ^ k) := by
      calc
        (p - 1) •
            (Polynomial.C a *
              Polynomial.X ^ (p ^ k) : Polynomial ℕ) =
            ((p - 1 : ℕ) : Polynomial ℕ) *
              (Polynomial.C a *
                Polynomial.X ^ (p ^ k)) :=
          (Polynomial.natCast_mul
            (R := ℕ) (p - 1)
            (Polynomial.C a *
              Polynomial.X ^ (p ^ k))).symm
        _ =
            Polynomial.C (p - 1) *
              (Polynomial.C a *
                Polynomial.X ^ (p ^ k)) := by
          rw [← Polynomial.C_eq_natCast
            (R := ℕ) (p - 1)]
          simp only [Nat.cast_id]
        _ =
            Polynomial.C ((p - 1) * a) *
              Polynomial.X ^ (p ^ k) := by
          rw [← mul_assoc, ← Polynomial.C_mul]

/-- Closed exact recurrence for the canonical iterated wreath
profile. -/
theorem iteratedWreathCycleProfile_succ
    (p k : ℕ) [hp : Fact p.Prime] :
    iteratedWreathCycleProfile p (k + 1) =
      iteratedWreathCycleProfile p k ^ p +
        Polynomial.C
            ((p - 1) *
              sylowTowerOrder p k ^ (p - 1)) *
          Polynomial.X ^ (p ^ k) := by
  classical
  rw [iteratedWreathCycleProfile_succ_eq_sum_fibers]
  calc
    (∑ q : PrimeCycleGroup p,
        iteratedWreathCycleProfileFiber p k q) =
        iteratedWreathCycleProfileFiber p k 1 +
          ∑ q ∈
              (Finset.univ :
                Finset (PrimeCycleGroup p)).erase 1,
            iteratedWreathCycleProfileFiber p k q :=
      (Finset.add_sum_erase
        (Finset.univ :
          Finset (PrimeCycleGroup p))
        (iteratedWreathCycleProfileFiber p k)
        (Finset.mem_univ 1)).symm
    _ =
        iteratedWreathCycleProfile p k ^ p +
          Polynomial.C
              ((p - 1) *
                sylowTowerOrder p k ^ (p - 1)) *
            Polynomial.X ^ (p ^ k) := by
      rw [iteratedWreathCycleProfileFiber_one,
        sum_iteratedWreathCycleProfileFiber_ne_one]

theorem iteratedWreathCycleProfile_zero
    (p : ℕ) [Fact p.Prime] :
    iteratedWreathCycleProfile p 0 = 1 := by
  classical
  let : Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) 0) :=
    Fintype.ofFinite _
  let : Unique
      (IteratedWreathProduct (PrimeCycleGroup p) 0) := by
    change Unique PUnit
    infer_instance
  simp only [iteratedWreathCycleProfile,
    iteratedWreathCycleWeight]
  rw [Fintype.sum_unique]
  rw [ite_eq_left (Subsingleton.elim _ _)]
  have hperm :
      iteratedWreathToPermHom
        (PrimeCycleGroup p) 0 default = 1 :=
    Subsingleton.elim _ _
  rw [hperm]
  simp

/-- The genuine wreath-product enumerator is the arithmetic tower
profile used by the finite audit. -/
theorem iteratedWreathCycleProfile_eq_sylowTowerCycleProfile
    (p k : ℕ) [hp : Fact p.Prime] :
    iteratedWreathCycleProfile p k =
      sylowTowerCycleProfile p k := by
  induction k with
  | zero =>
      rw [iteratedWreathCycleProfile_zero,
        sylowTowerCycleProfile_zero]
  | succ k ih =>
      rw [iteratedWreathCycleProfile_succ,
        sylowTowerCycleProfile_succ, ih]

end LisiSabatini
