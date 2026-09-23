module

public import LisiSabatini.SymmetricDoubleCosetBound

/-!
# Constant-time rejection witnesses for double-coset certificates

Each necessary test holds on every actual subgroup element. A candidate
with one failed test is therefore outside the subgroup. The checker is
agnostic about the tests; the symmetric-group application uses one failed
dyadic-block comparison for each product. No hash lookup or ambient-group
enumeration is needed.
-/

@[expose] public section

namespace LisiSabatini

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Check every indexed subgroup element against every necessary test. -/
def doubleCosetNecessaryCheck {N L : ℕ}
    (row : Fin N → G) (tests : Fin L → G → Bool) : Bool :=
  (List.finRange N).all fun i ↦ (List.finRange L).all fun j ↦ tests j (row i)

/-- Reject every nonidentity conjugated row using its supplied failed test. -/
def doubleCosetGoodCheck {N L : ℕ}
    (row : Fin N → G) (oneIndex : Fin N) (tests : Fin L → G → Bool)
    (witness : Fin N → Fin L) (g : G) : Bool :=
  (List.finRange N).all fun i ↦
    if i = oneIndex then true else !(tests (witness i) (g⁻¹ * row i * g))

/-- Reject every cross-product row using its supplied failed test. -/
def doubleCosetSeparationCheck {N L : ℕ}
    (row : Fin N → G) (tests : Fin L → G → Bool)
    (witness : Fin N → Fin L) (g h : G) : Bool :=
  (List.finRange N).all fun i ↦ !(tests (witness i) (g⁻¹ * row i * h))

/-- Accepted tests hold throughout the actual subgroup. -/
theorem doubleCosetNecessaryCheck_sound {N L : ℕ}
    (P : Subgroup G) (row : Fin N → G) (tests : Fin L → G → Bool)
    (hcover : ∀ a ∈ P, ∃ i, row i = a)
    (hcheck : doubleCosetNecessaryCheck row tests = true) :
    ∀ a ∈ P, ∀ j, tests j a = true := by
  intro a ha j
  obtain ⟨i, rfl⟩ := hcover a ha
  exact List.all_eq_true.mp (List.all_eq_true.mp hcheck i (by simp)) j (by simp)

/-- A failed necessary test certifies nonmembership in the original subgroup. -/
theorem not_mem_of_failed_doubleCoset_test {L : ℕ}
    (P : Subgroup G) (tests : Fin L → G → Bool)
    (htests : ∀ a ∈ P, ∀ j, tests j a = true)
    (a : G) (j : Fin L) (hfalse : tests j a = false) : a ∉ P := by
  intro ha
  have htrue := htests a ha j
  rw [hfalse] at htrue
  exact Bool.false_ne_true htrue

/-- Soundness of an accepted good-conjugator certificate. -/
theorem doubleCosetGoodCheck_sound {N L : ℕ} {p : ℕ}
    (P : Sylow p G) (row : Fin N → G) (oneIndex : Fin N)
    (hcover : ∀ a ∈ (P : Subgroup G), ∃ i, row i = a)
    (hone : row oneIndex = 1) (tests : Fin L → G → Bool)
    (htests : ∀ a ∈ (P : Subgroup G), ∀ j, tests j a = true)
    (witness : Fin N → Fin L) (g : G)
    (hcheck : doubleCosetGoodCheck row oneIndex tests witness g = true) :
    mixedSylowInter P P g = ⊥ := by
  apply le_antisymm _ bot_le
  intro a ha
  obtain ⟨i, rfl⟩ := hcover a ha.1
  apply Subgroup.mem_bot.mpr
  by_cases hi : i = oneIndex
  · simpa only [hi] using hone
  have hchecki := List.all_eq_true.mp hcheck i (by simp)
  have hfalse : tests (witness i) (g⁻¹ * row i * g) = false := by
    simpa only [ite_eq_right hi, Bool.not_eq_true'] using hchecki
  have hnot := not_mem_of_failed_doubleCoset_test (P : Subgroup G) tests htests
    (g⁻¹ * row i * g) (witness i) hfalse
  apply False.elim (hnot ?_)
  have hmem := ha.2
  rw [Sylow.coe_subgroup_smul] at hmem
  change row i ∈ MulAut.conj g • (P : Subgroup G) at hmem
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hmem
  exact hmem

/-- Soundness of an accepted separation certificate. -/
theorem doubleCosetSeparationCheck_sound {N L : ℕ}
    (P : Subgroup G) (row : Fin N → G)
    (hcover : ∀ a ∈ P, ∃ i, row i = a)
    (tests : Fin L → G → Bool) (htests : ∀ a ∈ P, ∀ j, tests j a = true)
    (witness : Fin N → Fin L) (g h : G)
    (hcheck : doubleCosetSeparationCheck row tests witness g h = true) :
    ∀ a ∈ P, g⁻¹ * a * h ∉ P := by
  intro a ha
  obtain ⟨i, rfl⟩ := hcover a ha
  have hfalse : tests (witness i) (g⁻¹ * row i * h) = false := by
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp hcheck i (by simp)
  exact not_mem_of_failed_doubleCoset_test P tests htests _ (witness i) hfalse

/-- The separation condition is symmetric, since subgroup membership is
preserved by inversion. Thus unordered pairs suffice in the literal data. -/
theorem doubleCoset_separation_symm (P : Subgroup G) (g h : G)
    (hsep : ∀ a ∈ P, g⁻¹ * a * h ∉ P) :
    ∀ a ∈ P, h⁻¹ * a * g ∉ P := by
  intro a ha hmem
  have hcontra := hsep a⁻¹ (P.inv_mem ha)
  apply hcontra
  have hinv := P.inv_mem hmem
  simpa only [mul_inv_rev, inv_inv, mul_assoc] using hinv

end LisiSabatini
