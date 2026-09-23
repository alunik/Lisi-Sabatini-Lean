module

public import LisiSabatini.CoprimeNormal
public import Mathlib.Data.Finset.Card

/-!
# Self-centralizing normal prime subgroups

This file isolates the elementary top-component argument used in imprimitive
reductions.  Suppose that `A` is a normal `q`-subgroup of an ambient group
`T` and that its centralizer is contained in `A`.  Every normal `p`-subgroup
with `p ≠ q` centralizes `A`, because normal subgroups of distinct prime
power order commute.  It is therefore contained in `A`; coprime disjointness
then forces it to be trivial.

The final results apply this observation to a family of normal subgroups with
distinct prime labels.  Every nontrivial member must have prime label `q`, so
there is at most one nontrivial member.  No finiteness assumption on the
ambient group is needed; finiteness enters only in the final `Finset` count.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uT uI

variable {T : Type uT} [Group T]

/-! ## The direct self-centralizing argument -/

/-- Elementwise reformulation of the self-centralizing hypothesis
`C_T(A) ≤ A`. -/
theorem centralizer_le_iff_forall_commuting_mem
    (A : Subgroup T) :
    Subgroup.centralizer (A : Set T) ≤ A ↔
      ∀ x : T, (∀ a : T, a ∈ A → a * x = x * a) → x ∈ A := by
  constructor
  · intro h x hx
    apply h
    rw [Subgroup.mem_centralizer_iff]
    exact hx
  · intro h x hx
    exact h x (Subgroup.mem_centralizer_iff.mp hx)

/-- A normal `p`-subgroup at a prime different from a self-centralizing
normal `q`-subgroup is trivial.

This is the abstract top-component lemma.  It does not require the ambient
group to be finite. -/
theorem normalPSubgroup_eq_bot_of_selfCentralizing
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (A H : Subgroup T)
    (hAn : A.Normal) (hAq : IsPGroup q A)
    (hself : Subgroup.centralizer (A : Set T) ≤ A)
    (hHn : H.Normal) (hHp : IsPGroup p H) :
    H = ⊥ := by
  let : Fact (Nat.Prime p) := ⟨hp⟩
  let : Fact (Nat.Prime q) := ⟨hq⟩
  have hHcentralizesA : H ≤ Subgroup.centralizer (A : Set T) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (normalPSubgroups_commute_of_ne hpq hHp hHn hAq hAn hx ha).eq.symm
  have hHA : H ≤ A := hHcentralizesA.trans hself
  have hdisjoint : Disjoint H A :=
    pSubgroups_disjoint_of_ne hpq hHp hAq
  apply (Subgroup.eq_bot_iff_forall H).mpr
  intro x hx
  exact Subgroup.disjoint_def.mp hdisjoint hx (hHA hx)

/-! ## A reusable top-component certificate -/

/-- A normal `q`-subgroup supplied with the self-centralizing condition
`C_T(A) ≤ A`. -/
structure SelfCentralizingNormalPSubgroup (q : ℕ) (T : Type uT) [Group T] where
  subgroup : Subgroup T
  normal : subgroup.Normal
  isPGroup : IsPGroup q subgroup
  centralizer_le : Subgroup.centralizer (subgroup : Set T) ≤ subgroup

namespace SelfCentralizingNormalPSubgroup

variable {q : ℕ} (A : SelfCentralizingNormalPSubgroup q T)

include A

/-- Certificate form of
`normalPSubgroup_eq_bot_of_selfCentralizing`. -/
theorem normalPSubgroup_eq_bot_of_ne
    (hq : Nat.Prime q) {p : ℕ} (hp : Nat.Prime p) (hpq : p ≠ q)
    (H : Subgroup T) (hHn : H.Normal) (hHp : IsPGroup p H) :
    H = ⊥ :=
  normalPSubgroup_eq_bot_of_selfCentralizing hp hq hpq
    A.subgroup H A.normal A.isPGroup A.centralizer_le hHn hHp

/-! ## Families with distinct prime labels -/

/-- In any family of normal prime subgroups, all components whose prime is
different from the self-centralizing prime are trivial. -/
theorem normalPrimeFamily_eq_bot_of_ne
    (hq : Nat.Prime q)
    {I : Type uI} (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (H : I → Subgroup T) (hHn : ∀ i, (H i).Normal)
    (hHp : ∀ i, IsPGroup (p i) (H i))
    (i : I) (hi : p i ≠ q) :
    H i = ⊥ :=
  A.normalPSubgroup_eq_bot_of_ne hq (hp i) hi (H i) (hHn i) (hHp i)

/-- Equivalently, every nontrivial component in a normal prime family has
the distinguished prime label `q`. -/
theorem normalPrimeFamily_prime_eq_of_ne_bot
    (hq : Nat.Prime q)
    {I : Type uI} (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (H : I → Subgroup T) (hHn : ∀ i, (H i).Normal)
    (hHp : ∀ i, IsPGroup (p i) (H i))
    (i : I) (hi : H i ≠ ⊥) :
    p i = q := by
  by_contra hpq
  exact hi (A.normalPrimeFamily_eq_bot_of_ne hq p hp H hHn hHp i hpq)

/-- If the prime labels are injective, the set of indices carrying
nontrivial normal subgroups is subsingleton.  This form does not require the
index type to be finite. -/
theorem normalPrimeFamily_nontrivialIndices_subsingleton
    (hq : Nat.Prime q)
    {I : Type uI} (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p)
    (H : I → Subgroup T) (hHn : ∀ i, (H i).Normal)
    (hHp : ∀ i, IsPGroup (p i) (H i)) :
    ({i : I | H i ≠ ⊥} : Set I).Subsingleton := by
  intro i hi j hj
  apply hinj
  have hiq : p i = q :=
    A.normalPrimeFamily_prime_eq_of_ne_bot hq p hp H hHn hHp i hi
  have hjq : p j = q :=
    A.normalPrimeFamily_prime_eq_of_ne_bot hq p hp H hHn hHp j hj
  exact hiq.trans hjq.symm

open Classical in
/-- Finite-family form: among normal subgroups with pairwise distinct prime
labels, at most one can be nontrivial.  The only possible nontrivial member
is the one whose prime label is `q`. -/
theorem normalPrimeFamily_nontrivial_card_le_one
    (hq : Nat.Prime q)
    {I : Type uI} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p)
    (H : I → Subgroup T) (hHn : ∀ i, (H i).Normal)
    (hHp : ∀ i, IsPGroup (p i) (H i)) :
    (Finset.univ.filter fun i ↦ H i ≠ ⊥).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  have hi' : H i ≠ ⊥ := (Finset.mem_filter.mp hi).2
  have hj' : H j ≠ ⊥ := (Finset.mem_filter.mp hj).2
  exact A.normalPrimeFamily_nontrivialIndices_subsingleton
    hq p hp hinj H hHn hHp hi' hj'

end SelfCentralizingNormalPSubgroup

end LisiSabatini
