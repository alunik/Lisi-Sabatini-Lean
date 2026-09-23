module

public import LisiSabatini.SymmetricDoubleCosetCheck

/-!
# Checking good binary double cosets through involutions only

A nontrivial intersection of two Sylow 2-subgroups contains an involution.
A one-time full-row check certifies that the selected indices contain every
nonidentity element with square one. Every good-conjugator check can then
restrict its failed-test witnesses to those selected indices.

The executable checks use row indices and equality of supplied elements;
they never enumerate the ambient group or its subgroups.
-/

@[expose] public section

namespace LisiSabatini

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Certify completeness of a proposed list of involution indices.
The distinguished identity row is skipped. Extra indices and repetitions
are harmless: the subsequent good check still tests every listed index. -/
def doubleCosetInvolutionIndicesCheck [DecidableEq G] {N : ℕ}
    (row : Fin N → G) (oneIndex : Fin N) (indices : List (Fin N)) : Bool :=
  (List.finRange N).all fun i ↦
    if i = oneIndex then true
    else if row i * row i = 1 then decide (i ∈ indices) else true

/-- Check rejection witnesses only for the supplied involution indices. -/
def doubleCosetInvolutionGoodCheck {N L : ℕ}
    (row : Fin N → G) (indices : List (Fin N))
    (tests : Fin L → G → Bool) (witness : Fin N → Fin L) (g : G) : Bool :=
  indices.all fun i ↦ !(tests (witness i) (g⁻¹ * row i * g))

/-- An accepted completeness check includes every nonidentity square-one row. -/
theorem doubleCosetInvolutionIndicesCheck_sound [DecidableEq G] {N : ℕ}
    (row : Fin N → G) (oneIndex : Fin N) (hone : row oneIndex = 1)
    (indices : List (Fin N))
    (hcheck : doubleCosetInvolutionIndicesCheck row oneIndex indices = true) :
    ∀ i, row i ≠ 1 → (row i) ^ 2 = 1 → i ∈ indices := by
  intro i hne hsq
  have hi : i ≠ oneIndex := by
    intro hi
    apply hne
    simpa only [hi] using hone
  have hmul : row i * row i = 1 := by
    simpa only [pow_two] using hsq
  have hchecki := List.all_eq_true.mp hcheck i (by simp)
  simpa only [ite_eq_right hi, ite_eq_left hmul, decide_eq_true_eq] using hchecki

/-- Complete involution coverage is sufficient for a sound good-conjugator
check. No involution enumeration or Sylow membership decision is assumed. -/
theorem doubleCosetInvolutionGoodCheck_sound_of_complete [Finite G] {N L : ℕ}
    (P : Sylow 2 G) (row : Fin N → G) (indices : List (Fin N))
    (hcover : ∀ a ∈ (P : Subgroup G), ∃ i, row i = a)
    (hcomplete : ∀ i, row i ≠ 1 → (row i) ^ 2 = 1 → i ∈ indices)
    (tests : Fin L → G → Bool)
    (htests : ∀ a ∈ (P : Subgroup G), ∀ j, tests j a = true)
    (witness : Fin N → Fin L) (g : G)
    (hcheck : doubleCosetInvolutionGoodCheck row indices tests witness g = true) :
    mixedSylowInter P P g = ⊥ := by
  by_contra hbad
  obtain ⟨a, horder, haP, hagP⟩ :=
    (mixedSylowInter_ne_bot_iff_exists_primeOrder_mem P P g).mp hbad
  obtain ⟨i, rfl⟩ := hcover a haP
  have hne : row i ≠ 1 := by
    intro hone
    rw [hone, orderOf_one] at horder
    exact (by decide : (1 : ℕ) ≠ 2) horder
  have hsq : (row i) ^ 2 = 1 := by
    simpa only [horder] using pow_orderOf_eq_one (row i)
  have hi : i ∈ indices := hcomplete i hne hsq
  have hfalse : tests (witness i) (g⁻¹ * row i * g) = false := by
    simpa only [Bool.not_eq_true'] using List.all_eq_true.mp hcheck i hi
  have hnot := not_mem_of_failed_doubleCoset_test (P : Subgroup G) tests htests
    (g⁻¹ * row i * g) (witness i) hfalse
  apply hnot
  rw [Sylow.coe_subgroup_smul] at hagP
  change row i ∈ MulAut.conj g • (P : Subgroup G) at hagP
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hagP
  exact hagP

/-- End-to-end soundness from the Boolean completeness and selected-row
rejection certificates. The full row is scanned only for completeness. -/
theorem doubleCosetInvolutionGoodCheck_sound [Finite G] [DecidableEq G] {N L : ℕ}
    (P : Sylow 2 G) (row : Fin N → G) (oneIndex : Fin N)
    (hone : row oneIndex = 1) (indices : List (Fin N))
    (hcover : ∀ a ∈ (P : Subgroup G), ∃ i, row i = a)
    (hindices : doubleCosetInvolutionIndicesCheck row oneIndex indices = true)
    (tests : Fin L → G → Bool)
    (htests : ∀ a ∈ (P : Subgroup G), ∀ j, tests j a = true)
    (witness : Fin N → Fin L) (g : G)
    (hcheck : doubleCosetInvolutionGoodCheck row indices tests witness g = true) :
    mixedSylowInter P P g = ⊥ :=
  doubleCosetInvolutionGoodCheck_sound_of_complete P row indices hcover
    (doubleCosetInvolutionIndicesCheck_sound row oneIndex hone indices hindices)
    tests htests witness g hcheck

/-- One independently checked good representative using selected involutions. -/
structure DoubleCosetInvolutionGoodCertificate {N L M : ℕ}
    (row : Fin N → G) (indices : List (Fin N)) (tests : Fin L → G → Bool)
    (representatives : Fin M → G) where
  index : Fin M
  witness : Fin N → Fin L
  checked : doubleCosetInvolutionGoodCheck row indices tests witness
    (representatives index) = true

/-- Read only representative labels when checking shard coverage. -/
def doubleCosetInvolutionGoodCertificateIndices {N L M : ℕ}
    {row : Fin N → G} {indices : List (Fin N)} {tests : Fin L → G → Bool}
    {representatives : Fin M → G}
    (shards : List (List (DoubleCosetInvolutionGoodCertificate
      row indices tests representatives))) : List (Fin M) :=
  shards.flatten.map (fun c ↦ c.index)

/-- Complete label coverage assembles selected-involution proof records into
actual goodness for every representative. The one-time completeness proof
is shared by all records. -/
theorem doubleCosetInvolutionGoodCertificates_sound [Finite G] [DecidableEq G]
    {N L M : ℕ} (P : Sylow 2 G) (row : Fin N → G) (oneIndex : Fin N)
    (hcover : ∀ a ∈ (P : Subgroup G), ∃ i, row i = a)
    (hone : row oneIndex = 1) (indices : List (Fin N))
    (hindices : doubleCosetInvolutionIndicesCheck row oneIndex indices = true)
    (tests : Fin L → G → Bool)
    (htests : ∀ a ∈ (P : Subgroup G), ∀ j, tests j a = true)
    (representatives : Fin M → G)
    (shards : List (List (DoubleCosetInvolutionGoodCertificate
      row indices tests representatives)))
    (hlabels : doubleCosetInvolutionGoodCertificateIndices shards = List.finRange M) :
    ∀ i, mixedSylowInter P P (representatives i) = ⊥ := by
  intro i
  have hmem : i ∈ shards.flatten.map (fun c ↦ c.index) := by
    change i ∈ doubleCosetInvolutionGoodCertificateIndices shards
    rw [hlabels]
    simp
  obtain ⟨c, _, hci⟩ := List.mem_map.mp hmem
  have hgood := doubleCosetInvolutionGoodCheck_sound P row oneIndex hone indices
    hcover hindices tests htests c.witness (representatives c.index) c.checked
  simpa only [hci] using hgood

end LisiSabatini
