module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.Finset.Card
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Tactic.FinCases

/-!
# Efficient finite permutation tables

Strictly increasing numerical codes certify that a literal list has no
duplicates. Only adjacent comparisons need computation. The resulting finite
set uses the list directly, without running a duplicate-removal algorithm.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates

/-- A strictly increasing code along adjacent list entries rules out duplicates.
The code need not be injective away from this particular list. -/
theorem nodup_of_code_isChain {α β : Type*} [Preorder β] (code : α → β)
    {l : List α} (h : l.IsChain (fun a b ↦ code a < code b)) : l.Nodup := by
  have : Trans (fun a b : α ↦ code a < code b)
      (fun a b : α ↦ code a < code b)
      (fun a b : α ↦ code a < code b) :=
    ⟨fun hab hbc ↦ lt_trans hab hbc⟩
  exact h.pairwise.imp (fun hab heq ↦ (ne_of_lt hab) (congrArg code heq))

/-- A direct finite-set carrier, retaining the list and its distinctness proof. -/
def finsetOfNodupList {α : Type*} (l : List α) (h : l.Nodup) : Finset α :=
  ⟨(l : Multiset α), h⟩

@[simp]
theorem mem_finsetOfNodupList {α : Type*} (l : List α) (h : l.Nodup) (a : α) :
    a ∈ finsetOfNodupList l h ↔ a ∈ l := Iff.rfl

@[simp]
theorem card_finsetOfNodupList {α : Type*} (l : List α) (h : l.Nodup) :
    (finsetOfNodupList l h).card = l.length := rfl

/-- The base-`n` code of the images of a permutation of `Fin n`.
It is used only for strict comparisons within an explicitly supplied list. -/
def permutationCode {n : ℕ} (g : Equiv.Perm (Fin n)) : ℕ :=
  (List.ofFn fun i : Fin n ↦ (g i).val).foldl (fun acc digit ↦ acc * n + digit) 0

/-- Eight base-8 digits determine a permutation of eight points.
This permits numeric equality tests in larger finite certificates. -/
theorem permutationCode_injective_fin8 :
    Function.Injective (permutationCode (n := 8)) := by
  intro g h heq
  have g0 := (g 0).isLt
  have g1 := (g 1).isLt
  have g2 := (g 2).isLt
  have g3 := (g 3).isLt
  have g4 := (g 4).isLt
  have g5 := (g 5).isLt
  have g6 := (g 6).isLt
  have g7 := (g 7).isLt
  have h0 := (h 0).isLt
  have h1 := (h 1).isLt
  have h2 := (h 2).isLt
  have h3 := (h 3).isLt
  have h4 := (h 4).isLt
  have h5 := (h 5).isLt
  have h6 := (h 6).isLt
  have h7 := (h 7).isLt
  simp [permutationCode, List.ofFn_succ] at heq
  ext i
  fin_cases i <;> dsimp at * <;> omega

/-- Numeric equality for permutations of eight points. Install this locally
when checking a large literal table. -/
def permutationCodeDecidableEq_fin8 : DecidableEq (Equiv.Perm (Fin 8)) :=
  fun g h ↦
    if heq : permutationCode g = permutationCode h then
      isTrue (permutationCode_injective_fin8 heq)
    else
      isFalse (fun heq' ↦ heq (congrArg permutationCode heq'))

/-- Numeric equality for elements of A8, with correctness proved by code
injectivity. This is a named procedure, not a new global instance. -/
def alternatingCodeDecidableEq_fin8 : DecidableEq (alternatingGroup (Fin 8)) :=
  fun g h ↦
    if heq : permutationCode g.val = permutationCode h.val then
      isTrue (Subtype.ext (permutationCode_injective_fin8 heq))
    else
      isFalse (fun heq' ↦ heq (congrArg (fun x : alternatingGroup (Fin 8) ↦
        permutationCode x.val) heq'))

end LisiSabatini.FiniteCertificates
