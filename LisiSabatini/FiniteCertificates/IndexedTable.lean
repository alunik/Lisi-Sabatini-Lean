module

public import LisiSabatini.FiniteCertificates.TableCertificate
public import LisiSabatini.FiniteCertificates.PermutationTable
public import Mathlib.Data.List.Basic

/-!
# Indexed multiplication-table certificates

Each inverse and product comes with its proposed row index. Verification
checks the resulting equality directly instead of searching the carrier
for the answer. A row of length `m` requires one identity equality, `m`
inverse equalities, and `m²` product equalities.

The soundness lemmas recover the existing `subgroupCheck` proposition for
the actual finite carrier, so cardinality-certified `checkedSylow` can use
the indexed certificate without changing its mathematical meaning.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates

variable {G : Type*} [Group G] [DecidableEq G]

/-- Direct indexed closure checks. The index functions can themselves use
literal arrays, so the checker never performs a membership search. -/
def indexedClosureCheck (m : ℕ) (row : Fin m → G) (oneIndex : Fin m)
    (invIndex : Fin m → Fin m) (mulIndex : Fin m → Fin m → Fin m) : Bool :=
  decide (row oneIndex = 1 ∧ ∀ i,
    row (invIndex i) = (row i)⁻¹ ∧ ∀ j, row (mulIndex i j) = row i * row j)

/-- Soundness for any actual finite carrier whose elements are exactly
the indexed row values. No injectivity assumption is needed for closure. -/
theorem subgroupCheck_of_indexedClosureCheck
    {m : ℕ} (row : Fin m → G) (oneIndex : Fin m)
    (invIndex : Fin m → Fin m) (mulIndex : Fin m → Fin m → Fin m)
    (s : Finset G) (hcarrier : ∀ x, x ∈ s ↔ ∃ i, row i = x)
    (hcheck : indexedClosureCheck m row oneIndex invIndex mulIndex = true) :
    subgroupCheck s = true := by
  have h : row oneIndex = 1 ∧ ∀ i,
      row (invIndex i) = (row i)⁻¹ ∧ ∀ j, row (mulIndex i j) = row i * row j :=
    of_decide_eq_true hcheck
  apply decide_eq_true
  refine ⟨(hcarrier 1).mpr ⟨oneIndex, h.1⟩, ?_⟩
  intro x hx
  obtain ⟨i, rfl⟩ := (hcarrier x).mp hx
  refine ⟨(hcarrier _).mpr ⟨invIndex i, (h.2 i).1⟩, ?_⟩
  intro y hy
  obtain ⟨j, rfl⟩ := (hcarrier y).mp hy
  exact (hcarrier _).mpr ⟨mulIndex i j, (h.2 i).2 j⟩

/-- List indexing directly certifies the original duplicate-free carrier. -/
theorem subgroupCheck_finsetOfNodupList_of_indexedClosureCheck
    (row : List G) (hnodup : row.Nodup) (oneIndex : Fin row.length)
    (invIndex : Fin row.length → Fin row.length)
    (mulIndex : Fin row.length → Fin row.length → Fin row.length)
    (hcheck : indexedClosureCheck row.length row.get oneIndex invIndex mulIndex = true) :
    subgroupCheck (finsetOfNodupList row hnodup) = true := by
  apply subgroupCheck_of_indexedClosureCheck row.get oneIndex invIndex mulIndex
    (finsetOfNodupList row hnodup) ?_ hcheck
  intro x
  exact List.mem_iff_get

/-- Array lookup certifies the finite set whose actual carrier is the
array's list, retaining its duplicate-free proof. -/
theorem subgroupCheck_finsetOfArray_of_indexedClosureCheck
    (row : Array G) (hnodup : row.toList.Nodup) (oneIndex : Fin row.size)
    (invIndex : Fin row.size → Fin row.size)
    (mulIndex : Fin row.size → Fin row.size → Fin row.size)
    (hcheck : indexedClosureCheck row.size (fun i ↦ row[i])
      oneIndex invIndex mulIndex = true) :
    subgroupCheck (finsetOfNodupList row.toList hnodup) = true := by
  apply subgroupCheck_of_indexedClosureCheck (fun i : Fin row.size ↦ row[i])
    oneIndex invIndex mulIndex (finsetOfNodupList row.toList hnodup) ?_ hcheck
  intro x
  change x ∈ row.toList ↔ ∃ i : Fin row.size, row[i] = x
  constructor
  · intro hx
    obtain ⟨i, hi, hix⟩ := Array.getElem_of_mem (show x ∈ row from by simpa using hx)
    exact ⟨⟨i, hi⟩, hix⟩
  · rintro ⟨i, rfl⟩
    simp

/-- The list carrier can be retained while the checker uses array lookup.
This is the adapter for generated literal lists and their `toArray` view. -/
theorem subgroupCheck_finsetOfNodupList_of_arrayIndexedClosureCheck
    (row : List G) (hnodup : row.Nodup) (oneIndex : Fin row.toArray.size)
    (invIndex : Fin row.toArray.size → Fin row.toArray.size)
    (mulIndex : Fin row.toArray.size → Fin row.toArray.size → Fin row.toArray.size)
    (hcheck : indexedClosureCheck row.toArray.size (fun i ↦ row.toArray[i])
      oneIndex invIndex mulIndex = true) :
    subgroupCheck (finsetOfNodupList row hnodup) = true := by
  have h := subgroupCheck_finsetOfArray_of_indexedClosureCheck
    row.toArray (by simpa using hnodup) oneIndex invIndex mulIndex hcheck
  simpa using h

end LisiSabatini.FiniteCertificates
