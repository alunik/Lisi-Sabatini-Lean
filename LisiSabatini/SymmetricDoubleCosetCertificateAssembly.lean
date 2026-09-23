module

public import LisiSabatini.SymmetricDoubleCosetCheck

/-!
# Assembly of sharded double-coset certificates

Each record stores a previously checked negative-test certificate. Large
families are assembled by concatenating lists of these records. The only
global finite check compares their labels with the canonical lists of
indices and ordered pairs. It does not evaluate the permutation tests again.

In particular, a family of 41 representatives requires 820 pair labels,
with no proof by 41-by-41 case splitting.
-/

@[expose] public section

namespace LisiSabatini

variable {G : Type*} [Group G]

/-- All strictly ordered pairs of representative indices, in lexicographic
order. This list is suitable for a small literal coverage check. -/
def doubleCosetOrderedPairs (M : ℕ) : List (Fin M × Fin M) :=
  (List.finRange M).flatMap fun i ↦
    ((List.finRange M).filter fun j ↦ decide (i < j)).map fun j ↦ (i, j)

@[simp]
theorem mem_doubleCosetOrderedPairs_iff {M : ℕ} (i j : Fin M) :
    (i, j) ∈ doubleCosetOrderedPairs M ↔ i < j := by
  simp [doubleCosetOrderedPairs, List.mem_flatMap, List.mem_map]

/-- A single checked good representative. The proof field refers to its
individual certificate theorem; the assembly need not replay its test. -/
structure DoubleCosetGoodCertificate {N L M : ℕ}
    (row : Fin N → G) (oneIndex : Fin N) (tests : Fin L → G → Bool)
    (representatives : Fin M → G) where
  index : Fin M
  witness : Fin N → Fin L
  checked : doubleCosetGoodCheck row oneIndex tests witness (representatives index) = true

/-- A single checked pair of representatives. The pair may have either
orientation; coverage below uses the increasing orientation. -/
structure DoubleCosetPairCertificate {N L M : ℕ}
    (row : Fin N → G) (tests : Fin L → G → Bool)
    (representatives : Fin M → G) where
  pair : Fin M × Fin M
  witness : Fin N → Fin L
  checked : doubleCosetSeparationCheck row tests witness
    (representatives pair.1) (representatives pair.2) = true

/-- Flatten the inexpensive labels of the checked good-certificate shards. -/
def doubleCosetGoodCertificateIndices {N L M : ℕ}
    {row : Fin N → G} {oneIndex : Fin N} {tests : Fin L → G → Bool}
    {representatives : Fin M → G}
    (shards : List (List (DoubleCosetGoodCertificate row oneIndex tests representatives))) :
    List (Fin M) := shards.flatten.map (fun c ↦ c.index)

/-- Flatten the inexpensive labels of the checked pair-certificate shards. -/
def doubleCosetPairCertificateIndices {N L M : ℕ}
    {row : Fin N → G} {tests : Fin L → G → Bool} {representatives : Fin M → G}
    (shards : List (List (DoubleCosetPairCertificate row tests representatives))) :
    List (Fin M × Fin M) := shards.flatten.map (fun c ↦ c.pair)

/-- Complete label coverage turns independently checked good-certificate
shards into a theorem about every representative. -/
theorem doubleCosetGoodCertificates_sound {N L M p : ℕ}
    (P : Sylow p G) (row : Fin N → G) (oneIndex : Fin N)
    (hcover : ∀ a ∈ (P : Subgroup G), ∃ i, row i = a)
    (hone : row oneIndex = 1) (tests : Fin L → G → Bool)
    (htests : ∀ a ∈ (P : Subgroup G), ∀ j, tests j a = true)
    (representatives : Fin M → G)
    (shards : List (List (DoubleCosetGoodCertificate row oneIndex tests representatives)))
    (hindices : doubleCosetGoodCertificateIndices shards = List.finRange M) :
    ∀ i, mixedSylowInter P P (representatives i) = ⊥ := by
  intro i
  have hmem : i ∈ shards.flatten.map (fun c ↦ c.index) := by
    change i ∈ doubleCosetGoodCertificateIndices shards
    rw [hindices]
    simp
  obtain ⟨c, _, hci⟩ := List.mem_map.mp hmem
  have hgood := doubleCosetGoodCheck_sound P row oneIndex hcover hone tests htests
    c.witness (representatives c.index) c.checked
  simpa only [hci] using hgood

/-- Complete pair-label coverage turns independently checked pair shards
into separation for all distinct representative indices. -/
theorem doubleCosetPairCertificates_sound {N L M : ℕ}
    (P : Subgroup G) (row : Fin N → G)
    (hcover : ∀ a ∈ P, ∃ i, row i = a)
    (tests : Fin L → G → Bool) (htests : ∀ a ∈ P, ∀ j, tests j a = true)
    (representatives : Fin M → G)
    (shards : List (List (DoubleCosetPairCertificate row tests representatives)))
    (hindices : doubleCosetPairCertificateIndices shards = doubleCosetOrderedPairs M) :
    ∀ i j, i ≠ j → ∀ a ∈ P, (representatives i)⁻¹ * a * representatives j ∉ P := by
  have hordered (i j : Fin M) (hij : i < j) :
      ∀ a ∈ P, (representatives i)⁻¹ * a * representatives j ∉ P := by
    have hmem : (i, j) ∈ shards.flatten.map (fun c ↦ c.pair) := by
      change (i, j) ∈ doubleCosetPairCertificateIndices shards
      rw [hindices]
      exact (mem_doubleCosetOrderedPairs_iff i j).mpr hij
    obtain ⟨c, _, hcij⟩ := List.mem_map.mp hmem
    have hsep := doubleCosetSeparationCheck_sound P row hcover tests htests
      c.witness (representatives c.pair.1) (representatives c.pair.2) c.checked
    simpa only [hcij] using hsep
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hordered i j hijlt
  · exact doubleCoset_separation_symm P (representatives j) (representatives i)
      (hordered j i hjilt)

/-- Sharded certificate assembly feeds directly into the exact bad-count
bound. Only the two short label equalities need a global finite check. -/
theorem bad_conjugators_add_card_mul_le_of_doubleCoset_certificates
    [Finite G] {N L M p : ℕ}
    (P : Sylow p G) (row : Fin N → G) (oneIndex : Fin N)
    (hcover : ∀ a ∈ (P : Subgroup G), ∃ i, row i = a)
    (hone : row oneIndex = 1) (tests : Fin L → G → Bool)
    (htests : ∀ a ∈ (P : Subgroup G), ∀ j, tests j a = true)
    (representatives : Fin M → G)
    (goodShards : List (List (DoubleCosetGoodCertificate row oneIndex tests representatives)))
    (pairShards : List (List (DoubleCosetPairCertificate row tests representatives)))
    (hgoodIndices : doubleCosetGoodCertificateIndices goodShards = List.finRange M)
    (hpairIndices : doubleCosetPairCertificateIndices pairShards = doubleCosetOrderedPairs M) :
    (mixedSylowPairBadConjugators P P).ncard + M * Nat.card P * Nat.card P ≤ Nat.card G := by
  have hgood := doubleCosetGoodCertificates_sound P row oneIndex hcover hone tests htests
    representatives goodShards hgoodIndices
  have hsep := doubleCosetPairCertificates_sound (P : Subgroup G) row hcover tests htests
    representatives pairShards hpairIndices
  simpa only [Nat.card_fin] using
    bad_conjugators_add_family_card_mul_le P P representatives hgood hsep

end LisiSabatini
