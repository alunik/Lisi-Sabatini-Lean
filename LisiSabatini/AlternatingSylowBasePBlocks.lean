import LisiSabatini.AlternatingSylowWreathSupport
import LisiSabatini.AlternatingSylowCoefficientBridge
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Indexes
import Mathlib.GroupTheory.Perm.Subgroup

/-!
# Base-`p` block assembly for symmetric Sylow subgroups

The canonical Sylow `p`-subgroup on `n` letters is the direct product
of one iterated regular wreath product for every occurrence of a
nonzero base-`p` digit of `n`.  This file realizes that product as a
faithful permutation group on the corresponding disjoint union of
prime-power blocks.
-/

noncomputable section

open scoped BigOperators Polynomial

namespace LisiSabatini

/-- The occurrences of the base-`p` digits of `n`, with their place
remembered. -/
abbrev BasePBlockIndex (n p : ℕ) :=
  Σ k : Fin (n + 1), Fin (basePDigit n p k)

/-- The point set of the block indexed by `i`. -/
abbrev BasePBlockPoints (p : ℕ) {n : ℕ}
    (i : BasePBlockIndex n p) :=
  Fin (i.1 : ℕ) → PrimeCycleGroup p

/-- The disjoint union of all base-`p` blocks. -/
abbrev BasePBlockPointSum (n p : ℕ) :=
  Σ i : BasePBlockIndex n p, BasePBlockPoints p i

/-- The direct product of the iterated wreath groups belonging to the
base-`p` blocks. -/
abbrev BasePBlockWreathProduct (n p : ℕ) :=
  ∀ i : BasePBlockIndex n p,
    IteratedWreathProduct (PrimeCycleGroup p) (i.1 : ℕ)

local instance primeCycleNeZero
    (p : ℕ) [hp : Fact p.Prime] : NeZero p :=
  ⟨hp.out.ne_zero⟩

noncomputable local instance iteratedPrimeCycleFintype
    (p k : ℕ) [Fact p.Prime] :
    Fintype
      (IteratedWreathProduct (PrimeCycleGroup p) k) :=
  Fintype.ofFinite _

noncomputable local instance basePBlockWreathProductDecidableEq
    (n p : ℕ) [Fact p.Prime] :
    DecidableEq (BasePBlockWreathProduct n p) :=
  Classical.decEq _

theorem length_digits_le_succ
    (n p : ℕ) (hp : 2 ≤ p) :
    (p.digits n).length ≤ n + 1 := by
  by_cases hn : n = 0
  · subst n
    simp
  · rw [Nat.length_digits p n hp hn]
    exact Nat.succ_le_succ (Nat.log_le_self p n)

theorem sum_basePDigit_mul_pow
    (n p : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ Finset.range (n + 1),
        basePDigit n p k * p ^ k = n := by
  let L := p.digits n
  have hlen : L.length ≤ n + 1 :=
    length_digits_le_succ n p hp
  have hsmall :
      ∑ k ∈ Finset.range L.length,
          L.getD k 0 * p ^ k = n := by
    calc
      ∑ k ∈ Finset.range L.length,
          L.getD k 0 * p ^ k =
          ∑ i : Fin L.length,
            L.get i * p ^ (i : ℕ) := by
        rw [← Fin.sum_univ_eq_sum_range]
        apply Finset.sum_congr rfl
        intro k hk
        rw [List.getD_eq_get L 0 k]
      _ = (L.mapIdx fun i a ↦ a * p ^ i).sum := by
        rw [List.mapIdx_eq_ofFn, List.sum_ofFn]
      _ = Nat.ofDigits p L := by
        rw [Nat.ofDigits_eq_sum_mapIdx]
      _ = n := Nat.ofDigits_digits p n
  calc
    ∑ k ∈ Finset.range (n + 1),
        basePDigit n p k * p ^ k =
        ∑ k ∈ Finset.range (n + 1),
          L.getD k 0 * p ^ k := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Nat.getD_digits n k hp]
      rfl
    _ =
        ∑ k ∈ Finset.range L.length,
          L.getD k 0 * p ^ k := by
      symm
      apply Finset.sum_subset
        (Finset.range_mono hlen)
      intro k hkBig hkSmall
      have hkLen : L.length ≤ k := by
        simpa only [Finset.mem_range, not_lt] using hkSmall
      rw [List.getD_eq_default _ _ hkLen, zero_mul]
    _ = n := hsmall

theorem sum_basePDigit
    (n p : ℕ) (hp : 2 ≤ p) :
    ∑ k ∈ Finset.range (n + 1), basePDigit n p k =
      (p.digits n).sum := by
  let L := p.digits n
  have hlen : L.length ≤ n + 1 :=
    length_digits_le_succ n p hp
  calc
    ∑ k ∈ Finset.range (n + 1), basePDigit n p k =
        ∑ k ∈ Finset.range (n + 1), L.getD k 0 := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [Nat.getD_digits n k hp]
      rfl
    _ = ∑ k ∈ Finset.range L.length, L.getD k 0 := by
      symm
      apply Finset.sum_subset (Finset.range_mono hlen)
      intro k _hkBig hkSmall
      have hkLen : L.length ≤ k := by
        simpa only [Finset.mem_range, not_lt] using hkSmall
      rw [List.getD_eq_default _ _ hkLen]
    _ = ∑ i : Fin L.length, L.get i := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [List.getD_eq_get L 0 i]
    _ = L.sum := by
      rw [← List.sum_ofFn, List.ofFn_get]

theorem sum_basePBlock_pow
    {n p : ℕ} (hp : p.Prime) [NeZero p] :
    ∑ i : BasePBlockIndex n p, p ^ (i.1 : ℕ) = n := by
  calc
    ∑ i : BasePBlockIndex n p, p ^ (i.1 : ℕ) =
        ∑ k : Fin (n + 1),
          ∑ _r : Fin (basePDigit n p k), p ^ (k : ℕ) := by
      rw [Fintype.sum_sigma]
    _ =
        ∑ k ∈ Finset.range (n + 1),
          basePDigit n p k * p ^ k := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _hk
      simp
    _ = n :=
      sum_basePDigit_mul_pow n p hp.two_le

theorem card_basePBlockIndex_eq_sum_digits
    (n p : ℕ) (hp : 2 ≤ p) :
    Fintype.card (BasePBlockIndex n p) =
      (p.digits n).sum := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_eq_sum_range]
  exact sum_basePDigit n p hp

/-- Exponent of `p` in the direct product of the tower groups. -/
def basePBlockExponent (n p : ℕ) : ℕ :=
  ∑ i : BasePBlockIndex n p,
    ∑ r ∈ Finset.range (i.1 : ℕ), p ^ r

theorem pred_mul_geom_sum
    {p k : ℕ} (hp : 2 ≤ p) :
    (p - 1) * (∑ r ∈ Finset.range k, p ^ r) =
      p ^ k - 1 := by
  have h :=
    geom_sum_mul_add (R := ℕ) (p - 1) k
  rw [Nat.sub_add_cancel (by omega : 1 ≤ p)] at h
  rw [Nat.mul_comm]
  omega

theorem basePBlockExponent_eq_factorization_factorial
    {n p : ℕ} (hp : p.Prime) :
    basePBlockExponent n p = n.factorial.factorization p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply Nat.mul_left_cancel (Nat.sub_pos_of_lt hp.one_lt)
  calc
    (p - 1) * basePBlockExponent n p =
        ∑ i : BasePBlockIndex n p,
          (p - 1) *
            (∑ r ∈ Finset.range (i.1 : ℕ), p ^ r) := by
      simp only [basePBlockExponent, Finset.mul_sum]
    _ =
        ∑ i : BasePBlockIndex n p, (p ^ (i.1 : ℕ) - 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [pred_mul_geom_sum hp.two_le]
    _ =
        (∑ i : BasePBlockIndex n p, p ^ (i.1 : ℕ)) -
          ∑ _i : BasePBlockIndex n p, 1 := by
      apply Finset.sum_tsub_distrib
      intro i _hi
      exact (pow_pos hp.pos _)
    _ = n - (p.digits n).sum := by
      rw [sum_basePBlock_pow hp]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_univ, Nat.cast_id,
        card_basePBlockIndex_eq_sum_digits n p hp.two_le]
    _ = (p - 1) * n.factorial.factorization p := by
      rw [Nat.sub_one_mul_factorization_factorial hp]

theorem card_basePBlockIndex
    (n p : ℕ) :
    Fintype.card (BasePBlockIndex n p) =
      ∑ k ∈ Finset.range (n + 1), basePDigit n p k := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, Fin.sum_univ_eq_sum_range]

theorem card_basePBlockPointSum
    {n p : ℕ} (hp : p.Prime) [NeZero p] :
    Fintype.card (BasePBlockPointSum n p) = n := by
  classical
  calc
    Fintype.card (BasePBlockPointSum n p) =
        ∑ i : BasePBlockIndex n p,
          Fintype.card (BasePBlockPoints p i) := by
      rw [Fintype.card_sigma]
    _ =
        ∑ i : BasePBlockIndex n p, p ^ (i.1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Fintype.card_fun, Fintype.card_fin,
        ← Nat.card_eq_fintype_card,
        natCard_primeCycleGroup hp]
    _ =
        ∑ k : Fin (n + 1),
          ∑ _r : Fin (basePDigit n p k), p ^ (k : ℕ) := by
      rw [Fintype.sum_sigma]
    _ =
        ∑ k ∈ Finset.range (n + 1),
          basePDigit n p k * p ^ k := by
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro k _hk
      simp
    _ = n :=
      sum_basePDigit_mul_pow n p hp.two_le

/-- The canonical identification of the disjoint block point set with
`Fin n`. -/
noncomputable def basePBlockPointEquivFin
    {n p : ℕ} (hp : p.Prime) :
    BasePBlockPointSum n p ≃ Fin n :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  Fintype.equivOfCardEq (by
    rw [card_basePBlockPointSum hp, Fintype.card_fin])

/-! ## The faithful block action -/

/-- Apply the canonical iterated-wreath action in every block. -/
def basePBlockComponentPermHom (n p : ℕ) :
    BasePBlockWreathProduct n p →*
      (∀ i : BasePBlockIndex n p,
        Equiv.Perm (BasePBlockPoints p i)) where
  toFun w i :=
    iteratedWreathToPermHom
      (PrimeCycleGroup p) (i.1 : ℕ) (w i)
  map_one' := by
    funext i
    exact
      (iteratedWreathToPermHom
        (PrimeCycleGroup p) (i.1 : ℕ)).map_one
  map_mul' x y := by
    funext i
    exact
      (iteratedWreathToPermHom
        (PrimeCycleGroup p) (i.1 : ℕ)).map_mul (x i) (y i)

/-- The action on the disjoint union of the blocks. -/
def basePBlockPointSumPermHom (n p : ℕ) :
    BasePBlockWreathProduct n p →*
      Equiv.Perm (BasePBlockPointSum n p) :=
  (Equiv.Perm.sigmaCongrRightHom
      (BasePBlockPoints p :
        BasePBlockIndex n p → Type)).comp
    (basePBlockComponentPermHom n p)

theorem basePBlockComponentPermHom_injective
    (n p : ℕ) :
    Function.Injective (basePBlockComponentPermHom n p) := by
  intro x y hxy
  funext i
  apply iteratedWreathToPermHomInj
  exact congrFun hxy i

theorem basePBlockPointSumPermHom_injective
    (n p : ℕ) :
    Function.Injective (basePBlockPointSumPermHom n p) :=
  (Equiv.Perm.sigmaCongrRightHom_injective.comp
    (basePBlockComponentPermHom_injective n p))

/-- The same block action, transported to the standard `n`-point set. -/
def basePBlockPermHom
    (n p : ℕ) (hp : p.Prime) :
    BasePBlockWreathProduct n p →*
      Equiv.Perm (Fin n) :=
  letI : NeZero p := ⟨hp.ne_zero⟩
  (basePBlockPointEquivFin hp).permCongrHom.toMonoidHom.comp
    (basePBlockPointSumPermHom n p)

theorem basePBlockPermHom_injective
    (n p : ℕ) (hp : p.Prime) :
    Function.Injective (basePBlockPermHom n p hp) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  exact
    ((basePBlockPointEquivFin hp).permCongrHom.comp_injective
      (basePBlockPointSumPermHom n p)).mpr
        (basePBlockPointSumPermHom_injective n p)

/-- The embedded base-`p` block subgroup of `S_n`. -/
def basePBlockSubgroup
    (n p : ℕ) (hp : p.Prime) :
    Subgroup (Equiv.Perm (Fin n)) :=
  (basePBlockPermHom n p hp).range

theorem natCard_basePBlockWreathProduct
    (n p : ℕ) (hp : p.Prime) :
    Nat.card (BasePBlockWreathProduct n p) =
      p ^ n.factorial.factorization p := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  classical
  calc
    Nat.card (BasePBlockWreathProduct n p) =
        ∏ i : BasePBlockIndex n p,
          Nat.card
            (IteratedWreathProduct
              (PrimeCycleGroup p) (i.1 : ℕ)) := by
      rw [Nat.card_pi]
    _ =
        ∏ i : BasePBlockIndex n p,
          p ^ (∑ r ∈ Finset.range (i.1 : ℕ), p ^ r) := by
      apply Finset.prod_congr rfl
      intro i _hi
      rw [IteratedWreathProduct.card,
        natCard_primeCycleGroup hp]
    _ = p ^ basePBlockExponent n p := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl
    _ = p ^ n.factorial.factorization p := by
      rw [basePBlockExponent_eq_factorization_factorial hp]

theorem natCard_basePBlockSubgroup
    (n p : ℕ) (hp : p.Prime) :
    Nat.card (basePBlockSubgroup n p hp) =
      p ^ n.factorial.factorization p := by
  calc
    Nat.card (basePBlockSubgroup n p hp) =
        Nat.card (BasePBlockWreathProduct n p) := by
      exact
        (Nat.card_congr
          (MonoidHom.ofInjective
            (basePBlockPermHom_injective n p hp)).toEquiv).symm
    _ = p ^ n.factorial.factorization p :=
      natCard_basePBlockWreathProduct n p hp

theorem natCard_perm_fin
    (n : ℕ) :
    Nat.card (Equiv.Perm (Fin n)) = n.factorial := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm,
    Fintype.card_fin]

/-- The actual Sylow subgroup furnished by the base-`p` block
construction. -/
def basePBlockSylow
    (n p : ℕ) (hp : p.Prime) :
    Sylow p (Equiv.Perm (Fin n)) :=
  letI : Fact p.Prime := ⟨hp⟩
  Sylow.ofCard (basePBlockSubgroup n p hp) (by
    rw [natCard_basePBlockSubgroup n p hp,
      natCard_perm_fin])

@[simp]
theorem coe_basePBlockSylow
    (n p : ℕ) (hp : p.Prime) :
    (basePBlockSylow n p hp :
      Subgroup (Equiv.Perm (Fin n))) =
        basePBlockSubgroup n p hp := by
  letI : Fact p.Prime := ⟨hp⟩
  rfl

/-! ## Multiplication of the block cycle profiles -/

/-- The number of prime cycles contributed by all block components. -/
def basePBlockCycleCount
    (n p : ℕ) [Fact p.Prime]
    (w : BasePBlockWreathProduct n p) : ℕ :=
  ∑ i : BasePBlockIndex n p,
    (iteratedWreathToPermHom
      (PrimeCycleGroup p) (i.1 : ℕ) (w i)).cycleType.card

/-- Enumerator obtained by multiplying the individual block weights
before summing over the direct product. -/
def basePBlockCycleProfile
    (n p : ℕ) [hp : Fact p.Prime] :
    Polynomial ℕ := by
  classical
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  letI (i : BasePBlockIndex n p) :
      Fintype
        (IteratedWreathProduct
          (PrimeCycleGroup p) (i.1 : ℕ)) :=
    Fintype.ofFinite _
  exact
    ∑ w : BasePBlockWreathProduct n p,
      ∏ i : BasePBlockIndex n p,
        iteratedWreathCycleWeight p (i.1 : ℕ) (w i)

theorem basePBlockCycleProfile_eq_prod
    (n p : ℕ) [hp : Fact p.Prime] :
    basePBlockCycleProfile n p =
      ∏ i : BasePBlockIndex n p,
        iteratedWreathCycleProfile p (i.1 : ℕ) := by
  classical
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  letI (i : BasePBlockIndex n p) :
      Fintype
        (IteratedWreathProduct
          (PrimeCycleGroup p) (i.1 : ℕ)) :=
    Fintype.ofFinite _
  rw [basePBlockCycleProfile]
  rw [← Fintype.prod_sum]
  apply Finset.prod_congr rfl
  intro i _hi
  rfl

theorem basePBlockCycleProfile_eq_sylowCycleProfile
    (n p : ℕ) [hp : Fact p.Prime] :
    basePBlockCycleProfile n p =
      sylowCycleProfile n p := by
  classical
  rw [basePBlockCycleProfile_eq_prod]
  simp_rw [
    iteratedWreathCycleProfile_eq_sylowTowerCycleProfile]
  rw [Fintype.prod_sigma]
  calc
    (∏ k : Fin (n + 1),
        ∏ _r : Fin (basePDigit n p k),
          sylowTowerCycleProfile p (k : ℕ)) =
        ∏ k : Fin (n + 1),
          sylowTowerCycleProfile p (k : ℕ) ^
            basePDigit n p k := by
      apply Finset.prod_congr rfl
      intro k _hk
      simp
    _ =
        ∏ k ∈ Finset.range (n + 1),
          sylowTowerCycleProfile p k ^
            basePDigit n p k := by
      simpa using
        (Fin.prod_univ_eq_prod_range
          (fun k ↦
            sylowTowerCycleProfile p k ^
              basePDigit n p k) (n + 1))
    _ = sylowCycleProfile n p := by
      rw [sylowCycleProfile]
      apply Finset.prod_congr rfl
      intro k _hk
      by_cases hk0 : basePDigit n p k = 0
      · simp [hk0]
      · simp [hk0]

theorem prod_iteratedWreathCycleWeight_eq
    (n p : ℕ) [hp : Fact p.Prime]
    (w : BasePBlockWreathProduct n p) :
    (∏ i : BasePBlockIndex n p,
      iteratedWreathCycleWeight p (i.1 : ℕ) (w i)) =
        if w ^ p = 1 then
          Polynomial.X ^ basePBlockCycleCount n p w
        else 0 := by
  classical
  by_cases hw : w ^ p = 1
  · rw [if_pos hw]
    have hwi :
        ∀ i : BasePBlockIndex n p, (w i) ^ p = 1 := by
      intro i
      exact congrFun hw i
    simp_rw [iteratedWreathCycleWeight, if_pos (hwi _)]
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  · rw [if_neg hw]
    have hnotall :
        ¬ ∀ i : BasePBlockIndex n p, (w i) ^ p = 1 := by
      intro hall
      apply hw
      funext i
      exact hall i
    push Not at hnotall
    obtain ⟨i, hi⟩ := hnotall
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [iteratedWreathCycleWeight, hi]

theorem basePBlockCycleProfile_eq_sum_monomials
    (n p : ℕ) [hp : Fact p.Prime] :
    basePBlockCycleProfile n p =
      ∑ w : BasePBlockWreathProduct n p,
        if w ^ p = 1 then
          Polynomial.X ^ basePBlockCycleCount n p w
        else 0 := by
  classical
  letI : NeZero p := ⟨hp.out.ne_zero⟩
  letI (i : BasePBlockIndex n p) :
      Fintype
        (IteratedWreathProduct
          (PrimeCycleGroup p) (i.1 : ℕ)) :=
    Fintype.ofFinite _
  rw [basePBlockCycleProfile]
  apply Finset.sum_congr rfl
  intro w _hw
  exact prod_iteratedWreathCycleWeight_eq n p w

/-! ## Cycle count of the disjoint-union action -/

theorem card_support_sigmaCongrRight
    {ι : Type*} {β : ι → Type*}
    [Fintype ι] [∀ i, Fintype (β i)]
    [DecidableEq ι] [∀ i, DecidableEq (β i)]
    (f : ∀ i, Equiv.Perm (β i)) :
    (Equiv.Perm.sigmaCongrRight f).support.card =
      ∑ i : ι, (f i).support.card := by
  have hmem (i : ι) (x : β i) :
      (⟨i, x⟩ : Σ i, β i) ∈
          (Equiv.Perm.sigmaCongrRight f).support ↔
        x ∈ (f i).support := by
    rw [Equiv.Perm.mem_support, Equiv.Perm.mem_support,
      Equiv.sigmaCongrRight_apply]
    constructor
    · intro hpair hfixed
      exact hpair (Sigma.ext rfl (heq_of_eq hfixed))
    · intro hfixed hpair
      exact hfixed (eq_of_heq (Sigma.mk.inj_iff.mp hpair).2)
  let E :
      {z : Σ i, β i //
        z ∈ (Equiv.Perm.sigmaCongrRight f).support} ≃
        (Σ i : ι, {x : β i // x ∈ (f i).support}) :=
    {
      toFun z :=
        ⟨z.1.1, ⟨z.1.2, (hmem z.1.1 z.1.2).mp z.2⟩⟩
      invFun z :=
        ⟨⟨z.1, z.2.1⟩, (hmem z.1 z.2.1).mpr z.2.2⟩
      left_inv z := by
        apply Subtype.ext
        rfl
      right_inv z := by
        exact Sigma.ext rfl (heq_of_eq (Subtype.ext rfl))
    }
  calc
    (Equiv.Perm.sigmaCongrRight f).support.card =
        Fintype.card
          (Σ i : ι, {x : β i // x ∈ (f i).support}) := by
      simpa only [Fintype.card_coe] using
        Fintype.card_congr E
    _ = ∑ i : ι, (f i).support.card := by
      simp only [Fintype.card_sigma, Fintype.card_coe]

theorem card_support_basePBlockPointSumPermHom
    (n p : ℕ) [Fact p.Prime]
    (w : BasePBlockWreathProduct n p) :
    (basePBlockPointSumPermHom n p w).support.card =
      ∑ i : BasePBlockIndex n p,
        (iteratedWreathToPermHom
          (PrimeCycleGroup p) (i.1 : ℕ) (w i)).support.card := by
  classical
  exact
    card_support_sigmaCongrRight
      (fun i ↦
        iteratedWreathToPermHom
          (PrimeCycleGroup p) (i.1 : ℕ) (w i))

theorem cycleType_card_basePBlockPointSumPermHom
    (n p : ℕ) [hp : Fact p.Prime]
    (w : BasePBlockWreathProduct n p)
    (hw : w ^ p = 1) :
    (basePBlockPointSumPermHom n p w).cycleType.card =
      basePBlockCycleCount n p w := by
  classical
  have hwi :
      ∀ i : BasePBlockIndex n p, (w i) ^ p = 1 := by
    intro i
    exact congrFun hw i
  have hcomponent :
      ∀ i : BasePBlockIndex n p,
        (iteratedWreathToPermHom
          (PrimeCycleGroup p) (i.1 : ℕ) (w i)) ^ p = 1 := by
    intro i
    rw [← map_pow, hwi i, map_one]
  have htotal :
      (basePBlockPointSumPermHom n p w) ^ p = 1 := by
    rw [← map_pow, hw, map_one]
  calc
    (basePBlockPointSumPermHom n p w).cycleType.card =
        (basePBlockPointSumPermHom n p w).support.card / p :=
      cycleType_card_eq_card_support_div_prime _ htotal
    _ =
        (∑ i : BasePBlockIndex n p,
          (iteratedWreathToPermHom
            (PrimeCycleGroup p) (i.1 : ℕ)
              (w i)).support.card) / p := by
      rw [card_support_basePBlockPointSumPermHom]
    _ =
        (∑ i : BasePBlockIndex n p,
          (iteratedWreathToPermHom
            (PrimeCycleGroup p) (i.1 : ℕ)
              (w i)).cycleType.card * p) / p := by
      apply congrArg (· / p)
      apply Finset.sum_congr rfl
      intro i _hi
      rw [card_support_eq_cycleType_card_mul_prime
        _ (hcomponent i)]
    _ =
        ((∑ i : BasePBlockIndex n p,
          (iteratedWreathToPermHom
            (PrimeCycleGroup p) (i.1 : ℕ)
              (w i)).cycleType.card) * p) / p := by
      rw [Finset.sum_mul]
    _ = basePBlockCycleCount n p w := by
      rw [Nat.mul_div_cancel _ hp.out.pos]
      rfl

theorem cycleType_card_basePBlockPermHom
    (n p : ℕ) [hp : Fact p.Prime]
    (w : BasePBlockWreathProduct n p)
    (hw : w ^ p = 1) :
    (basePBlockPermHom n p hp.out w).cycleType.card =
      basePBlockCycleCount n p w := by
  classical
  have hsource :
      (basePBlockPointSumPermHom n p w) ^ p = 1 := by
    rw [← map_pow, hw, map_one]
  have htarget :
      (basePBlockPermHom n p hp.out w) ^ p = 1 := by
    rw [← map_pow, hw, map_one]
  calc
    (basePBlockPermHom n p hp.out w).cycleType.card =
        (basePBlockPermHom n p hp.out w).support.card / p :=
      cycleType_card_eq_card_support_div_prime _ htarget
    _ =
        (basePBlockPointSumPermHom n p w).support.card / p := by
      rw [basePBlockPermHom]
      exact congrArg (· / p)
        (card_support_permCongr
          (basePBlockPointEquivFin hp.out)
          (basePBlockPointSumPermHom n p w))
    _ =
        (basePBlockPointSumPermHom n p w).cycleType.card :=
      (cycleType_card_eq_card_support_div_prime _ hsource).symm
    _ = basePBlockCycleCount n p w :=
      cycleType_card_basePBlockPointSumPermHom n p w hw

/-! ## Coefficients and the Sylow row -/

/-- Direct-product elements of exponent dividing `p` with exactly `j`
prime cycles in the block action. -/
def basePBlockCycleCountFinset
    (n p j : ℕ) [Fact p.Prime] :
    Finset (BasePBlockWreathProduct n p) :=
  Finset.univ.filter fun w ↦
    w ^ p = 1 ∧ basePBlockCycleCount n p w = j

theorem coeff_basePBlockCycleProfile
    (n p j : ℕ) [hp : Fact p.Prime] :
    (basePBlockCycleProfile n p).coeff j =
      (basePBlockCycleCountFinset n p j).card := by
  classical
  rw [basePBlockCycleProfile_eq_sum_monomials]
  simp only [Polynomial.finset_sum_coeff]
  calc
    (∑ w : BasePBlockWreathProduct n p,
      (if w ^ p = 1 then
        Polynomial.X ^ basePBlockCycleCount n p w
      else 0).coeff j) =
        ∑ w : BasePBlockWreathProduct n p,
          if w ^ p = 1 ∧ basePBlockCycleCount n p w = j
          then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro w _hw
      by_cases hpow : w ^ p = 1
      · by_cases hcount : basePBlockCycleCount n p w = j
        · simp [hpow, hcount, Polynomial.coeff_X_pow]
        · have hcount' :
              j ≠ basePBlockCycleCount n p w :=
            Ne.symm hcount
          simp [hpow, hcount, hcount',
            Polynomial.coeff_X_pow]
      · simp [hpow]
    _ = (basePBlockCycleCountFinset n p j).card := by
      rw [Finset.sum_boole]
      rfl

theorem cycleType_basePBlockPermHom_eq_replicate_iff
    (n p j : ℕ) [hp : Fact p.Prime]
    (w : BasePBlockWreathProduct n p) :
    (basePBlockPermHom n p hp.out w).cycleType =
        Multiset.replicate j p ↔
      w ^ p = 1 ∧ basePBlockCycleCount n p w = j := by
  classical
  constructor
  · intro hcycle
    have htarget :
        (basePBlockPermHom n p hp.out w) ^ p = 1 := by
      apply Equiv.Perm.pow_prime_eq_one_iff.mpr
      intro c hc
      rw [hcycle] at hc
      exact Multiset.eq_of_mem_replicate hc
    have hw : w ^ p = 1 := by
      apply basePBlockPermHom_injective n p hp.out
      simpa only [map_pow, map_one] using htarget
    refine ⟨hw, ?_⟩
    rw [← cycleType_card_basePBlockPermHom n p w hw,
      hcycle, Multiset.card_replicate]
  · rintro ⟨hw, hcount⟩
    have htarget :
        (basePBlockPermHom n p hp.out w) ^ p = 1 := by
      rw [← map_pow, hw, map_one]
    rw [Equiv.Perm.cycleType_of_pow_prime_eq_one htarget,
      cycleType_card_basePBlockPermHom n p w hw,
      hcount]

theorem mem_primeCycleTypeSylowRow_basePBlockPermHom_iff
    (n p j : ℕ) [hp : Fact p.Prime]
    (w : BasePBlockWreathProduct n p) :
    basePBlockPermHom n p hp.out w ∈
        primeCycleTypeSylowRow n p j
          (basePBlockSylow n p hp.out) ↔
      w ∈ basePBlockCycleCountFinset n p j := by
  classical
  rw [basePBlockCycleCountFinset, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  simp only [primeCycleTypeSylowRow, primeCycleTypeFinset,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcycle, _hmem⟩
    exact
      (cycleType_basePBlockPermHom_eq_replicate_iff
        n p j w).mp hcycle
  · intro hw
    refine
      ⟨(cycleType_basePBlockPermHom_eq_replicate_iff
          n p j w).mpr hw, ?_⟩
    have hmem :
        basePBlockPermHom n p hp.out w ∈
          basePBlockSubgroup n p hp.out :=
      ⟨w, rfl⟩
    simpa only [coe_basePBlockSylow] using hmem

theorem card_primeCycleTypeSylowRow_basePBlockSylow
    (n p j : ℕ) [hp : Fact p.Prime] :
    (primeCycleTypeSylowRow n p j
      (basePBlockSylow n p hp.out)).card =
      (basePBlockCycleCountFinset n p j).card := by
  classical
  let F :
      {w : BasePBlockWreathProduct n p //
        w ∈ basePBlockCycleCountFinset n p j} →
      {g : Equiv.Perm (Fin n) //
        g ∈ primeCycleTypeSylowRow n p j
          (basePBlockSylow n p hp.out)} :=
    fun w ↦
      ⟨basePBlockPermHom n p hp.out w.1,
        (mem_primeCycleTypeSylowRow_basePBlockPermHom_iff
          n p j w.1).mpr w.2⟩
  have hFInjective : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply basePBlockPermHom_injective n p hp.out
    exact congrArg Subtype.val hxy
  have hFSurjective : Function.Surjective F := by
    intro g
    have hg := g.2
    simp only [primeCycleTypeSylowRow, primeCycleTypeFinset,
      Finset.mem_filter, Finset.mem_univ, true_and] at hg
    have hgP := hg.2
    have hgP' :
        g.1 ∈ basePBlockSubgroup n p hp.out := by
      change
        g.1 ∈
          (basePBlockSylow n p hp.out :
            Subgroup (Equiv.Perm (Fin n))) at hgP
      simpa only [coe_basePBlockSylow] using hgP
    rw [basePBlockSubgroup, MonoidHom.mem_range] at hgP'
    obtain ⟨w, hwImage⟩ := hgP'
    have hwMem :
        w ∈ basePBlockCycleCountFinset n p j := by
      apply
        (mem_primeCycleTypeSylowRow_basePBlockPermHom_iff
          n p j w).mp
      rw [hwImage]
      exact g.2
    refine ⟨⟨w, hwMem⟩, ?_⟩
    apply Subtype.ext
    exact hwImage
  let E :=
    Equiv.ofBijective F ⟨hFInjective, hFSurjective⟩
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr E).symm

theorem card_primeCycleTypeSylowRow_eq_coeff
    (n p j : ℕ) [hp : Fact p.Prime] :
    (primeCycleTypeSylowRow n p j
      (basePBlockSylow n p hp.out)).card =
        (sylowCycleProfile n p).coeff j := by
  rw [card_primeCycleTypeSylowRow_basePBlockSylow,
    ← coeff_basePBlockCycleProfile,
    basePBlockCycleProfile_eq_sylowCycleProfile]

/-- The exact symmetric Sylow coefficient formula holds in every
degree. -/
theorem hasSymmetricSylowCycleProfileCoefficients
    (n p : ℕ) (hp : p.Prime) :
    HasSymmetricSylowCycleProfileCoefficients n p := by
  letI : Fact p.Prime := ⟨hp⟩
  refine ⟨basePBlockSylow n p hp, ?_⟩
  intro j _hj
  exact card_primeCycleTypeSylowRow_eq_coeff n p j

end LisiSabatini
