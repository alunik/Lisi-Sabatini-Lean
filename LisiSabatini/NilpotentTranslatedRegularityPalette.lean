module

public import LisiSabatini.FixedPointFreePalette
public import LisiSabatini.FiniteLinearOrbit
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Palettes preserving a distinguished stabilizer

These elementary lemmas support the translated-regularity proof for
nilpotent groups. A finite palette can preserve the stabilizer of a
distinguished component while avoiding the exceptional points of
fixed-point-free components and one marked orbit.

The cardinality and commuting-palette hypotheses are explicit. This file
does not assert the full nilpotent translated-regularity proposition.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uV uS

/-- If neither of two equivalence relations is universal, some pair is
inequivalent for both. Applying this to a subtype retains any common
conditions imposed on the available vectors. -/
theorem exists_pair_inequivalent_for_two_setoids
    {X : Type*} (R S : Setoid X)
    (hR : ∃ x y, ¬ R.r x y)
    (hS : ∃ x y, ¬ S.r x y) :
    ∃ x y, ¬ R.r x y ∧ ¬ S.r x y := by
  obtain ⟨x, y, hRxy⟩ := hR
  by_cases hSxy : S.r x y
  · obtain ⟨u, v, hSuv⟩ := hS
    have hz : ∃ z, ¬ S.r x z := by
      by_cases hSxu : S.r x u
      · refine ⟨v, fun hSxv ↦ hSuv (S.trans (S.symm hSxu) hSxv)⟩
      · exact ⟨u, hSxu⟩
    obtain ⟨z, hSxz⟩ := hz
    by_cases hRxz : R.r x z
    · refine ⟨y, z, ?_, ?_⟩
      · exact fun hRyz ↦ hRxy (R.trans hRxz (R.symm hRyz))
      · exact fun hSyz ↦ hSxz (S.trans hSxy hSyz)
    · exact ⟨x, z, hRxz, hSxz⟩
  · exact ⟨x, y, hRxy, hSxy⟩

/-- Injectively parametrized candidates cannot have more inverse images
of a finite bad locus than the locus has points. -/
theorem ncard_preimage_le_of_injective
    {S : Type uS} {V : Type uV} [Finite S] [Finite V]
    (f : S → V) (hf : Function.Injective f) (B : Set V) :
    (f ⁻¹' B).ncard ≤ B.ncard := by
  rw [← Set.ncard_image_of_injective (f ⁻¹' B) hf]
  exact Set.ncard_le_ncard (Set.image_preimage_subset f B) (Set.toFinite B)

/-- An injective finite palette can avoid a specified point for each
index and one orbit, provided the corresponding counting budget holds. -/
theorem exists_palette_avoiding_points_and_orbit
    {I : Type uI} {S : Type uS} {R : Type uR} {V : Type uV}
    [Fintype I] [Finite S] [Finite V]
    [Semiring R] [AddCommGroup V] [Module R V]
    (f : S → V) (hf : Function.Injective f)
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (points : I → V) (t c : V)
    (hcard : Fintype.card I + Nat.card H < Nat.card S) :
    ∃ s : S, (∀ i, f s ≠ points i) ∧
      f s + t ∉ MulAction.orbit H c := by
  classical
  let g : S → V := fun s ↦ f s + t
  have hg : Function.Injective g := by
    intro x y hxy
    exact hf (add_right_cancel hxy)
  let bad : Option I → Set S
    | none => g ⁻¹' MulAction.orbit H c
    | some i => f ⁻¹' {points i}
  have hpoint (i : I) : (bad (some i)).ncard ≤ 1 := by
    simpa only [bad, Set.ncard_singleton] using
      ncard_preimage_le_of_injective f hf {points i}
  have horbit : (bad none).ncard ≤ Nat.card H :=
    (ncard_preimage_le_of_injective g hg (MulAction.orbit H c)).trans
      (ncard_orbit_le_natCard H c)
  have hbad : (∑ i, (bad i).ncard) < Nat.card S := by
    rw [Fintype.sum_option]
    have hsum : (∑ i : I, (bad (some i)).ncard) ≤ Fintype.card I := by
      simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) ↦ hpoint i)
    exact (Nat.add_le_add horbit hsum).trans_lt (by omega)
  obtain ⟨s, hs⟩ := exists_avoids_of_sum_ncard_lt bad hbad
  refine ⟨s, ?_, ?_⟩
  · intro i
    simpa only [bad, Set.mem_preimage, Set.mem_singleton_iff] using hs (some i)
  · exact hs none

/-- An invertible linear map commuting with a component preserves its
literal point stabilizer, not merely its order. -/
theorem stabilizer_smul_eq_of_commute
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommGroup V] [Module R V]
    (T : Subgroup (LinearMap.GeneralLinearGroup R V))
    (s : LinearMap.GeneralLinearGroup R V)
    (hcomm : ∀ g : T, Commute (g : LinearMap.GeneralLinearGroup R V) s)
    (a : V) :
    MulAction.stabilizer T (s • a) = MulAction.stabilizer T a := by
  ext g
  simp only [MulAction.mem_stabilizer_iff]
  have hswap : g • (s • a) = s • (g • a) := by
    change (g : LinearMap.GeneralLinearGroup R V) • (s • a) =
      s • ((g : LinearMap.GeneralLinearGroup R V) • a)
    rw [← mul_smul, (hcomm g).eq, mul_smul]
  rw [hswap]
  exact (MulAction.injective s).eq_iff

/-- The orbit of a nonzero vector under a fixed-point-free linear group
is an injectively indexed palette. -/
theorem smul_injective_of_fixedPointFreeOffZero
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommGroup V] [Module R V]
    (S : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hS : FixedPointFreeOffZero S) {a : V} (ha : a ≠ 0) :
    Function.Injective (fun s : S ↦ s • a) := by
  intro s t hst
  change s • a = t • a at hst
  have hfix : (t⁻¹ * s) • a = a := by
    rw [mul_smul, hst, inv_smul_smul]
  have heq : t⁻¹ * s = 1 := by
    by_contra hne
    exact ha (hS (t⁻¹ * s) hne a hfix)
  exact (inv_mul_eq_one.mp heq).symm

/-- A commuting fixed-point-free palette simultaneously preserves a
distinguished stabilizer, makes all fixed-point-free translated rows
regular, and avoids any one orbit of a marked row.

The intended nilpotent scalar leaf takes `S = ⟨-Id, A⟩`, where `A` is
the central odd Hall subgroup. Constructing that palette and establishing
its cardinality are separate structural obligations. -/
theorem exists_regular_translates_preserving_stabilizer_of_commuting_palette
    {I : Type uI} {R : Type uR} {V : Type uV}
    [Fintype I] [Finite V]
    [Semiring R] [AddCommGroup V] [Module R V]
    (T S : Subgroup (LinearMap.GeneralLinearGroup R V)) [Finite S]
    (hS : FixedPointFreeOffZero S)
    (hcomm : ∀ g : T, ∀ s : S,
      Commute (g : LinearMap.GeneralLinearGroup R V)
        (s : LinearMap.GeneralLinearGroup R V))
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : ∀ i, FixedPointFreeOffZero (H i))
    (a : V) (ha : a ≠ 0) (b : V) (t : I → V) (k : I) (c : V)
    (hcard : Fintype.card I + Nat.card (H k) < Nat.card S) :
    ∃ v : V,
      MulAction.stabilizer T (v + b) = MulAction.stabilizer T a ∧
      (∀ i, MulAction.stabilizer (H i) (v + t i) = ⊥) ∧
      v + t k ∉ MulAction.orbit (H k) c := by
  let f : S → V := fun s ↦ s • a - b
  have hf : Function.Injective f := by
    intro s u hsu
    exact smul_injective_of_fixedPointFreeOffZero S hS ha
      (sub_left_inj.mp hsu)
  obtain ⟨s, hs, horbit⟩ := exists_palette_avoiding_points_and_orbit
    f hf (H k) (fun i ↦ -t i) (t k) c hcard
  refine ⟨f s, ?_, ?_, horbit⟩
  · change MulAction.stabilizer T
        ((s : LinearMap.GeneralLinearGroup R V) • a - b + b) = _
    rw [sub_add_cancel]
    exact stabilizer_smul_eq_of_commute T s (fun g ↦ hcomm g s) a
  · intro i
    apply stabilizer_eq_bot_of_fixedPointFreeOffZero_of_ne_zero (H i) (hH i)
    exact fun hzero ↦ hs i (add_eq_zero_iff_eq_neg.mp hzero)

/-- An element of an odd-order group which squares to one is trivial. -/
theorem eq_one_of_sq_eq_one_of_odd_card
    {G : Type*} [Group G] (hodd : Odd (Nat.card G))
    (g : G) (hg : g ^ 2 = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hodd
  have hcard : g ^ Nat.card G = 1 := pow_card_eq_one'
  simpa [hk, pow_add, pow_mul, hg] using hcard

/-- A fixed-point-free group of odd order cannot carry a vector to its
negative unless that vector is already equal to its negative. -/
theorem smul_ne_neg_of_fixedPointFreeOffZero_of_odd
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommGroup V] [Module R V]
    (A : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hA : FixedPointFreeOffZero A) (hodd : Odd (Nat.card A))
    {a : V} (ha : a ≠ 0) (haNeg : a ≠ -a) (g : A) :
    g • a ≠ -a := by
  intro hga
  have hfix : (g ^ 2) • a = a := by
    rw [pow_two, mul_smul, hga, smul_neg, hga, neg_neg]
  have hsq : g ^ 2 = 1 := by
    by_contra hne
    exact ha (hA (g ^ 2) hne a hfix)
  have hg := eq_one_of_sq_eq_one_of_odd_card hodd g hsq
  rw [hg, one_smul] at hga
  exact haNeg hga

/-- The positive and negative copies of a nonzero regular orbit of an
odd-order fixed-point-free group are disjoint. -/
theorem smul_ne_neg_smul_of_fixedPointFreeOffZero_of_odd
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommGroup V] [Module R V]
    (A : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hA : FixedPointFreeOffZero A) (hodd : Odd (Nat.card A))
    {a : V} (ha : a ≠ 0) (haNeg : a ≠ -a) (g h : A) :
    g • a ≠ -(h • a) := by
  intro hgh
  apply smul_ne_neg_of_fixedPointFreeOffZero_of_odd A hA hodd ha haNeg (h⁻¹ * g)
  rw [mul_smul, hgh, smul_neg, inv_smul_smul]

/-- Signed copies of a regular orbit form a palette of size twice the
order of the odd group. -/
theorem signed_smul_injective_of_fixedPointFreeOffZero_of_odd
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommGroup V] [Module R V]
    (A : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hA : FixedPointFreeOffZero A) (hodd : Odd (Nat.card A))
    {a : V} (ha : a ≠ 0) (haNeg : a ≠ -a) :
    Function.Injective
      (fun s : Bool × A ↦ if s.1 then -(s.2 • a) else s.2 • a) := by
  rintro ⟨b, g⟩ ⟨d, h⟩ hgh
  cases b <;> cases d
  · have heq := smul_injective_of_fixedPointFreeOffZero A hA ha hgh
    exact congrArg (fun x : A ↦ (false, x)) heq
  · exact False.elim
      (smul_ne_neg_smul_of_fixedPointFreeOffZero_of_odd A hA hodd ha haNeg g h hgh)
  · exact False.elim
      (smul_ne_neg_smul_of_fixedPointFreeOffZero_of_odd A hA hodd ha haNeg h g hgh.symm)
  · have heq := smul_injective_of_fixedPointFreeOffZero A hA ha (neg_injective hgh)
    exact congrArg (fun x : A ↦ (true, x)) heq

/-- Negating a vector preserves its literal point stabilizer. -/
theorem stabilizer_neg_eq
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommGroup V] [Module R V]
    (T : Subgroup (LinearMap.GeneralLinearGroup R V)) (a : V) :
    MulAction.stabilizer T (-a) = MulAction.stabilizer T a := by
  ext g
  simp only [MulAction.mem_stabilizer_iff, smul_neg, neg_inj]

/-- The signed scalar palette supplies the missing odd-characteristic
base case: regular translated rows and an arbitrary marked orbit reserve
coexist with the exact stabilizer of a distinguished commuting component.

For the nilpotent application `A` is the central odd Hall subgroup. The
inequality and `a ≠ -a` are explicit, so the statement is also reusable
over other scalar rings whenever these conditions hold. -/
theorem exists_regular_translates_preserving_stabilizer_of_signed_palette
    {I : Type uI} {R : Type uR} {V : Type uV}
    [Fintype I] [Finite V]
    [Semiring R] [AddCommGroup V] [Module R V]
    (T A : Subgroup (LinearMap.GeneralLinearGroup R V)) [Finite A]
    (hA : FixedPointFreeOffZero A) (hodd : Odd (Nat.card A))
    (hcomm : ∀ g : T, ∀ s : A,
      Commute (g : LinearMap.GeneralLinearGroup R V)
        (s : LinearMap.GeneralLinearGroup R V))
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : ∀ i, FixedPointFreeOffZero (H i))
    (a : V) (ha : a ≠ 0) (haNeg : a ≠ -a)
    (b : V) (t : I → V) (k : I) (c : V)
    (hcard : Fintype.card I + Nat.card (H k) < 2 * Nat.card A) :
    ∃ v : V,
      MulAction.stabilizer T (v + b) = MulAction.stabilizer T a ∧
      (∀ i, MulAction.stabilizer (H i) (v + t i) = ⊥) ∧
      v + t k ∉ MulAction.orbit (H k) c := by
  let f : Bool × A → V := fun s ↦
    (if s.1 then -(s.2 • a) else s.2 • a) - b
  have hf : Function.Injective f := by
    intro s u hsu
    exact signed_smul_injective_of_fixedPointFreeOffZero_of_odd A hA hodd ha haNeg
      (sub_left_inj.mp hsu)
  have hbudget : Fintype.card I + Nat.card (H k) < Nat.card (Bool × A) := by
    simpa only [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] using hcard
  obtain ⟨s, hs, horbit⟩ := exists_palette_avoiding_points_and_orbit
    f hf (H k) (fun i ↦ -t i) (t k) c hbudget
  refine ⟨f s, ?_, ?_, horbit⟩
  · change MulAction.stabilizer T
        ((if s.1 then -(s.2 • a) else s.2 • a) - b + b) = _
    rw [sub_add_cancel]
    have hstab : MulAction.stabilizer T (s.2 • a) = MulAction.stabilizer T a :=
      stabilizer_smul_eq_of_commute T s.2 (fun g ↦ hcomm g s.2) a
    split_ifs
    · rw [stabilizer_neg_eq, hstab]
    · exact hstab
  · intro i
    apply stabilizer_eq_bot_of_fixedPointFreeOffZero_of_ne_zero (H i) (hH i)
    exact fun hzero ↦ hs i (add_eq_zero_iff_eq_neg.mp hzero)

end LisiSabatini
