module

public import LisiSabatini.SymmetricFiniteCertificates.Counting

/-!
# Explicit list scans for finite subgroup and intersection certificates

The computational predicates use only `List.any` and `List.all` over the
supplied carrier. Ambient-group enumeration does not occur in these scans.
Their correctness is connected separately to actual subgroup intersections.
-/

@[expose] public section

namespace LisiSabatini.SymmetricFiniteCertificates

open LisiSabatini.FiniteCertificates

variable {G : Type*} [DecidableEq G]

/-- Membership tested by an explicit scan of the supplied list. -/
def listContains (row : List G) (x : G) : Bool :=
  row.any (fun y ↦ decide (x = y))

@[simp]
theorem listContains_eq_true (row : List G) (x : G) :
    listContains row x = true ↔ x ∈ row := by
  simp [listContains, List.any_eq_true]

variable [Group G]

/-- Identity, inverse and product closure, scanning only the carrier list. -/
def listSubgroupCheck (row : List G) : Bool :=
  listContains row 1 && row.all (fun x ↦
    listContains row x⁻¹ && row.all (fun y ↦ listContains row (x * y)))

theorem listSubgroupCheck_eq_true_iff (row : List G) :
    listSubgroupCheck row = true ↔
      1 ∈ row ∧ ∀ x ∈ row, x⁻¹ ∈ row ∧ ∀ y ∈ row, x * y ∈ row := by
  simp [listSubgroupCheck, List.all_eq_true]

/-- An explicitly scanned carrier satisfies the existing subgroup predicate. -/
theorem listSubgroupCheck_sound (s : Finset G) (row : List G)
    (hrow : ∀ x, x ∈ s ↔ x ∈ row)
    (hcheck : listSubgroupCheck row = true) : subgroupCheck s = true := by
  apply decide_eq_true
  obtain ⟨h1, hclosed⟩ := (listSubgroupCheck_eq_true_iff row).mp hcheck
  refine ⟨(hrow 1).mpr h1, fun x hx ↦ ?_⟩
  obtain ⟨hinv, hmul⟩ := hclosed x ((hrow x).mp hx)
  exact ⟨(hrow _).mpr hinv, fun y hy ↦ (hrow _).mpr (hmul y ((hrow y).mp hy))⟩

/-- The self-intersection test, scanning only the supplied subgroup list. -/
def listGoodCheck (row : List G) (x : G) : Bool :=
  row.all (fun y ↦ decide (y = 1) || !(listContains row (x⁻¹ * y * x)))

theorem listGoodCheck_eq_true_iff (row : List G) (x : G) :
    listGoodCheck row x = true ↔
      ∀ y ∈ row, y = 1 ∨ x⁻¹ * y * x ∉ row := by
  simp [listGoodCheck, List.all_eq_true, Bool.eq_false_iff]

/-- A successful list scan implies the existing sound intersection test. -/
theorem listGoodCheck_sound (s : Finset G) (row : List G)
    (hrow : ∀ y, y ∈ s ↔ y ∈ row) (x : G)
    (hcheck : listGoodCheck row x = true) : goodCheck s x = true := by
  apply decide_eq_true
  intro y hy
  rcases (listGoodCheck_eq_true_iff row x).mp hcheck y ((hrow y).mp hy) with h | h
  · exact Or.inl h
  · exact Or.inr (fun hmem ↦ h ((hrow _).mp hmem))

/-- Count the sample entries rejected by the explicitly scanned test. -/
def listUncheckedCount (row sample : List G) : ℕ :=
  (sample.filter fun x ↦ listGoodCheck row x = false).length

theorem listUncheckedCount_append (row a b : List G) :
    listUncheckedCount row (a ++ b) =
      listUncheckedCount row a + listUncheckedCount row b := by
  simp only [listUncheckedCount, List.filter_append, List.length_append]

/-- The rejected list count bounds the actual bad conjugators in a
duplicate-free sample. -/
theorem bad_card_le_listUncheckedCount [Finite G] {p : ℕ} [Fact p.Prime]
    (s : Finset G) (row : List G) (hrow : ∀ x, x ∈ s ↔ x ∈ row)
    (hs : subgroupCheck s = true)
    (hcard : s.card = p ^ (Nat.card G).factorization p)
    (sample : List G) (hnodup : sample.Nodup) :
    (sampleBadConjugators (finsetOfNodupList sample hnodup)
      (checkedSylow s hs hcard)).card ≤ listUncheckedCount row sample := by
  classical
  change (sampleBadConjugators (finsetOfNodupList sample hnodup)
      (checkedSylow s hs hcard)).card ≤
    ((finsetOfNodupList sample hnodup).filter fun x ↦ listGoodCheck row x = false).card
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxsample, hxbad⟩ :=
    (mem_sampleBadConjugators_iff _ (checkedSylow s hs hcard) x).mp hx
  refine Finset.mem_filter.mpr ⟨hxsample, ?_⟩
  cases h : listGoodCheck row x
  · rfl
  · exact (hxbad (checkedSylow_good s hs hcard x
      (listGoodCheck_sound s row hrow x h))).elim

end LisiSabatini.SymmetricFiniteCertificates
