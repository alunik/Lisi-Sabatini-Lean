module

public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.List.GetD

/-!
# One-sided block-preservation certificates for permutation subgroups

A list of comparisons between image blocks need only be necessary for the
listed subgroup elements. A single failed comparison then certifies
nonmembership. The index of that comparison may be supplied by an external
generator, but its failure is checked using the actual permutation action.

These helpers are generic in the permutation degree and are shared by the
S8 transversal and the higher-degree double-coset certificates.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates

/-- Compare the blocks containing two point images. -/
structure PermutationBlockComparison (n : ℕ) where
  a : Fin n
  b : Fin n
  modulus : ℕ
  deriving DecidableEq

/-- The actual quotient comparison specified by a certificate entry. -/
def blockComparisonCheck {n : ℕ} (c : PermutationBlockComparison n)
    (g : Equiv.Perm (Fin n)) : Bool :=
  decide ((g c.a).val / c.modulus = (g c.b).val / c.modulus)

/-- Every listed comparison is satisfied by this permutation. -/
def permutationBlockCheck {n : ℕ} (cs : List (PermutationBlockComparison n))
    (g : Equiv.Perm (Fin n)) : Bool :=
  cs.all fun c ↦ blockComparisonCheck c g

/-- Passing the full test entails each listed comparison. -/
theorem blockComparisonCheck_of_permutationBlockCheck
    {n : ℕ} {cs : List (PermutationBlockComparison n)}
    {g : Equiv.Perm (Fin n)}
    (h : permutationBlockCheck cs g = true)
    {c : PermutationBlockComparison n} (hc : c ∈ cs) :
    blockComparisonCheck c g = true :=
  List.all_eq_true.mp h c hc

/-- A failed necessary comparison rules out membership in the carrier. -/
theorem not_mem_of_failed_blockComparison
    {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (cs : List (PermutationBlockComparison n))
    (hrow : ∀ y ∈ s, permutationBlockCheck cs y = true)
    (g : Equiv.Perm (Fin n))
    (c : PermutationBlockComparison n) (hc : c ∈ cs)
    (hbad : blockComparisonCheck c g = false) : g ∉ s := by
  intro hg
  have hgood := blockComparisonCheck_of_permutationBlockCheck (hrow g hg) hc
  rw [hbad] at hgood
  contradiction

/-- Verify just the indexed comparison proposed as a failure witness. -/
def indexedBlockFailureCheck {n : ℕ}
    (cs : List (PermutationBlockComparison n))
    (i : Fin cs.length) (g : Equiv.Perm (Fin n)) : Bool :=
  !(blockComparisonCheck (cs.get i) g)

/-- The indexed failure checker has the same one-sided soundness contract. -/
theorem not_mem_of_indexedBlockFailureCheck
    {n : ℕ} (s : Finset (Equiv.Perm (Fin n)))
    (cs : List (PermutationBlockComparison n))
    (hrow : ∀ y ∈ s, permutationBlockCheck cs y = true)
    (g : Equiv.Perm (Fin n)) (i : Fin cs.length)
    (hbad : indexedBlockFailureCheck cs i g = true) : g ∉ s := by
  apply not_mem_of_failed_blockComparison s cs hrow g (cs.get i)
  · exact List.mem_iff_get.mpr ⟨i, rfl⟩
  · change Bool.not (blockComparisonCheck (cs.get i) g) = true at hbad
    cases h : blockComparisonCheck (cs.get i) g with
    | false => rfl
    | true => rw [h] at hbad; contradiction

end LisiSabatini.FiniteCertificates
