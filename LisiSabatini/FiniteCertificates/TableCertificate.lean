module

public import LisiSabatini.Basic
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Data.Finset.Card

/-!
# Sound finite certificates for self-intersections

These Boolean checks use concrete group operations and finite tables.
Generation may happen outside Lean, but every accepted table is checked by
the kernel. In particular, this interface contains no native evaluation
or external computation axiom.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates

variable {G : Type*} [Group G] [DecidableEq G]

/-- A finite carrier contains the identity and is closed under inverses and
products. -/
def subgroupCheck (s : Finset G) : Bool :=
  decide (1 ∈ s ∧ ∀ x ∈ s, x⁻¹ ∈ s ∧ ∀ y ∈ s, x * y ∈ s)

/-- An accepted carrier defines a genuine subgroup of the original group. -/
def checkedSubgroup (s : Finset G) (h : subgroupCheck s = true) : Subgroup G where
  carrier := s
  one_mem' := (of_decide_eq_true h).1
  mul_mem' := fun hx hy ↦ ((of_decide_eq_true h).2 _ hx).2 _ hy
  inv_mem' := fun hx ↦ ((of_decide_eq_true h).2 _ hx).1

@[simp]
theorem mem_checkedSubgroup (s : Finset G) (h : subgroupCheck s = true) (x : G) :
    x ∈ checkedSubgroup s h ↔ x ∈ s := Iff.rfl

/-- The certificate's table length is the actual subgroup order. -/
theorem card_checkedSubgroup (s : Finset G) (h : subgroupCheck s = true) :
    Nat.card (checkedSubgroup s h) = s.card := by
  change Nat.card {x : G // x ∈ s} = s.card
  simp

/-- A cardinality-certified finite carrier is a Sylow subgroup. -/
noncomputable def checkedSylow [Finite G] {p : ℕ} [Fact p.Prime]
    (s : Finset G) (h : subgroupCheck s = true)
    (hcard : s.card = p ^ (Nat.card G).factorization p) : Sylow p G :=
  Sylow.ofCard (checkedSubgroup s h) ((card_checkedSubgroup s h).trans hcard)

/-- A self-intersection is trivial when no nonidentity table entry returns
to the table after inverse conjugation. -/
def goodCheck (s : Finset G) (x : G) : Bool :=
  decide (∀ y ∈ s, y = 1 ∨ x⁻¹ * y * x ∉ s)

/-- Soundness of a checked good conjugator, before Sylow maximality is used. -/
theorem goodCheck_sound
    (s : Finset G) (hs : subgroupCheck s = true) (x : G)
    (hx : goodCheck s x = true) :
    checkedSubgroup s hs ⊓ (checkedSubgroup s hs).map (MulAut.conj x).toMonoidHom = ⊥ := by
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨hyS, z, hzS, hzy⟩ := hy
  have hcheck := (of_decide_eq_true hx) y hyS
  have hconj : x⁻¹ * y * x = z := by
    rw [← hzy]
    change x⁻¹ * (x * z * x⁻¹) * x = z
    group
  have hmem : x⁻¹ * y * x ∈ s := by rwa [hconj]
  have hyone : y = 1 := hcheck.resolve_right (not_not.mpr hmem)
  exact hyone

/-- The Boolean good test certifies the actual Sylow self-intersection. -/
theorem checkedSylow_good [Finite G] {p : ℕ} [Fact p.Prime]
    (s : Finset G) (hs : subgroupCheck s = true)
    (hcard : s.card = p ^ (Nat.card G).factorization p)
    (x : G) (hx : goodCheck s x = true) :
    sylowInter (checkedSylow s hs hcard) x = ⊥ := by
  exact goodCheck_sound s hs x hx

attribute [local instance] Classical.propDecidable

/-- The complement of the checked good entries is a rigorous upper bound
on the bad self-intersections. A generator need not identify bad entries
exactly. -/
theorem bad_card_le_unchecked_card [Finite G] {p : ℕ} [Fact p.Prime]
    (s : Finset G) (hs : subgroupCheck s = true)
    (hcard : s.card = p ^ (Nat.card G).factorization p) (C : Finset G) :
    (C.filter fun x ↦ sylowInter (checkedSylow s hs hcard) x ≠ ⊥).card ≤
      (C.filter fun x ↦ goodCheck s x = false).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxC, hxBad⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxC, ?_⟩
  cases h : goodCheck s x
  · rfl
  · exact (hxBad (checkedSylow_good s hs hcard x h)).elim

end LisiSabatini.FiniteCertificates
