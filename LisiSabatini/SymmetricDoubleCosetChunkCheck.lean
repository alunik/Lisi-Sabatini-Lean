module

public import Mathlib.Data.List.FinRange

/-!
# Assembly of checked finite Boolean chunks

Each chunk stores a proof for its own list of indices. Assembly checks
only that concatenating those lists covers `List.finRange N`; it retrieves
the stored proofs without evaluating the Boolean function again.
-/

@[expose] public section

namespace LisiSabatini

/-- A separately checked list of indices for a finite Boolean test. -/
structure IndexedBooleanCheckChunk {N : ℕ} (f : Fin N → Bool) where
  indices : List (Fin N)
  checked : indices.all f = true

/-- Assemble checked chunks into a complete finite Boolean check using
only their index-list coverage and their previously established proofs. -/
theorem all_finRange_of_checked_chunks {N : ℕ} (f : Fin N → Bool)
    (chunks : List (IndexedBooleanCheckChunk f))
    (hlabels : chunks.flatMap (fun c ↦ c.indices) = List.finRange N) :
    (List.finRange N).all f = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hmem : i ∈ chunks.flatMap (fun c ↦ c.indices) := by
    rw [hlabels]
    exact hi
  obtain ⟨chunk, _, hichunk⟩ := List.mem_flatMap.mp hmem
  exact List.all_eq_true.mp chunk.checked i hichunk

end LisiSabatini
