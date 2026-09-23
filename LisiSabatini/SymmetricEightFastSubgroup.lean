module

public import LisiSabatini.SymmetricEightCertificates.FastChecks
public import LisiSabatini.SymmetricEightFastClosure

/-!
# The order-128 Sylow subgroup from generator and spanning-tree checks

Three generator actions on the 128 entries and 127 spanning-tree edges
certify the entire subgroup. This avoids checking all 16,384 ordered
products while preserving the same explicit permutation row.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini.SymmetricEightFastSubgroup

open FiniteCertificates SymmetricEightCertificates SymmetricEightCertificates.FastData

local instance : DecidableEq G := permutationCodeDecidableEq_fin8
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

/-- The three literal generators used by the spanning tree. -/
def generators : Set G := Set.range genAt

/-- The checked spanning tree reaches every row element from the identity. -/
theorem row_mem_closure_generators :
    ∀ x ∈ row, x ∈ Subgroup.closure generators := by
  have hbfs := indexed_bfs_mem_closure (n := 127)
    (fun k ↦ rowAt (bfsAt k)) generators bfsParent (fun k ↦ genAt (bfsGen k))
    (by rw [bfsAt_zero, FastData.rowAt_zero]) bfs_parent_lt
    (fun k _ ↦ Set.mem_range_self (bfsGen k)) bfs_edge_checked
  intro x hx
  obtain ⟨i, rfl⟩ := (mem_row_iff x).mp hx
  have h := hbfs (bfsInverse i)
  simpa only [bfs_cover] using h

/-- The sparse generator certificate verifies the complete subgroup law. -/
theorem row_closed : subgroupCheck row = true := by
  apply subgroupCheck_of_generator_invariance_and_reachability row generators
  · rw [← FastData.rowAt_zero]
    exact rowAt_mem 0
  · intro a ha x hx
    obtain ⟨j, rfl⟩ := ha
    obtain ⟨i, rfl⟩ := (mem_row_iff x).mp hx
    rw [action_checked]
    exact rowAt_mem _
  · exact row_mem_closure_generators

/-- The ambient permutation group has its standard order. -/
theorem card_G : Nat.card G = 40320 := by
  simp [G, Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The table realizes the full two-part of the ambient group order. -/
theorem row_card_factorization : row.card = 2 ^ (Nat.card G).factorization 2 := by
  rw [row_card, card_G]
  decide +kernel

/-- The actual Sylow subgroup represented by the original 128-entry row. -/
def sylow2 : Sylow 2 G :=
  checkedSylow row row_closed row_card_factorization

/-- The certified subgroup has order 128. -/
theorem card_sylow2 : Nat.card sylow2 = 128 :=
  (card_checkedSubgroup row row_closed).trans row_card

/-- Membership is exactly membership in the original explicit row. -/
@[simp] theorem mem_sylow2_iff (g : G) : g ∈ sylow2 ↔ g ∈ row := Iff.rfl

end LisiSabatini.SymmetricEightFastSubgroup
