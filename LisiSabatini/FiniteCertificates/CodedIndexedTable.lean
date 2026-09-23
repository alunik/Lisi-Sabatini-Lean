module

public import LisiSabatini.FiniteCertificates.IndexedTable

/-!
# Arithmetic checks for indexed multiplication tables

The executable checker below uses only cached natural-number codes and a
natural-number multiplication procedure. Injectivity and compatibility with
the actual group operation transfer its accepted equations back to the group.
Inverse entries are checked through their left-inverse products, so no separate
arithmetic implementation of inversion is needed.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates

/-- Pure natural-number checks for a proposed indexed subgroup table. -/
def codedIndexedClosureCheck (m : ℕ) (codeOne : ℕ) (mulCode : ℕ → ℕ → ℕ)
    (cached : Fin m → ℕ) (oneIndex : Fin m)
    (invIndex : Fin m → Fin m) (mulIndex : Fin m → Fin m → Fin m) : Bool :=
  decide (cached oneIndex = codeOne) &&
    (List.finRange m).all (fun i ↦
      decide (mulCode (cached (invIndex i)) (cached i) = codeOne) &&
        (List.finRange m).all (fun j ↦
          decide (cached (mulIndex i j) = mulCode (cached i) (cached j))))

variable {G : Type*} [Group G] [DecidableEq G]

/-- Arithmetic acceptance implies the original indexed group equations. -/
theorem indexedClosureCheck_of_codedIndexedClosureCheck
    (code : G → ℕ) (hinj : Function.Injective code)
    (mulCode : ℕ → ℕ → ℕ)
    (hmul : ∀ x y, code (x * y) = mulCode (code x) (code y))
    {m : ℕ} (row : Fin m → G) (cached : Fin m → ℕ)
    (hrow : ∀ i, code (row i) = cached i)
    (oneIndex : Fin m) (invIndex : Fin m → Fin m)
    (mulIndex : Fin m → Fin m → Fin m)
    (hcheck : codedIndexedClosureCheck m (code 1) mulCode cached
      oneIndex invIndex mulIndex = true) :
    indexedClosureCheck m row oneIndex invIndex mulIndex = true := by
  have hbool := Bool.and_eq_true_iff.mp hcheck
  have h : cached oneIndex = code 1 ∧ ∀ i,
      mulCode (cached (invIndex i)) (cached i) = code 1 ∧
        ∀ j, cached (mulIndex i j) = mulCode (cached i) (cached j) := by
    refine ⟨of_decide_eq_true hbool.1, fun i ↦ ?_⟩
    have hi := Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp hbool.2 i (by simp))
    refine ⟨of_decide_eq_true hi.1, fun j ↦ ?_⟩
    exact of_decide_eq_true (List.all_eq_true.mp hi.2 j (by simp))
  apply decide_eq_true
  refine ⟨hinj ((hrow oneIndex).trans h.1), fun i ↦ ⟨?_, fun j ↦ ?_⟩⟩
  · apply eq_inv_iff_mul_eq_one.mpr
    apply hinj
    rw [hmul, hrow, hrow]
    exact (h.2 i).1
  · apply hinj
    rw [hmul, hrow, hrow, hrow]
    exact (h.2 i).2 j

end LisiSabatini.FiniteCertificates
