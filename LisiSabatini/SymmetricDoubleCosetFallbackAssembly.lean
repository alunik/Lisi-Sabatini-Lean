module

public import LisiSabatini.SymmetricDoubleCosetCertificateAssembly

/-!
# Assemble short residual separation certificates after invariant separation

An independent invariant handles most pairs. Explicit negative-test records
are required only for the remaining ordered pairs; their labels are checked
against the corresponding filtered canonical pair list.
-/

@[expose] public section

namespace LisiSabatini

variable {G : Type*} [Group G]

/-- Combine a proved shortcut with residual checked pair records. -/
theorem doubleCosetPairCertificates_sound_of_shortcut {N L M : ℕ}
    (P : Subgroup G) (row : Fin N → G)
    (hcover : ∀ a ∈ P, ∃ i, row i = a)
    (tests : Fin L → G → Bool) (htests : ∀ a ∈ P, ∀ j, tests j a = true)
    (representatives : Fin M → G)
    (shortcut : Fin M → Fin M → Bool)
    (hshortcut : ∀ i j, shortcut i j = true →
      ∀ a ∈ P, (representatives i)⁻¹ * a * representatives j ∉ P)
    (shards : List (List (DoubleCosetPairCertificate row tests representatives)))
    (hindices : doubleCosetPairCertificateIndices shards =
      (doubleCosetOrderedPairs M).filter (fun ij ↦ !(shortcut ij.1 ij.2))) :
    ∀ i j, i ≠ j → ∀ a ∈ P, (representatives i)⁻¹ * a * representatives j ∉ P := by
  have hordered (i j : Fin M) (hij : i < j) :
      ∀ a ∈ P, (representatives i)⁻¹ * a * representatives j ∉ P := by
    by_cases hskip : shortcut i j = true
    · exact hshortcut i j hskip
    have hmem : (i, j) ∈ shards.flatten.map (fun c ↦ c.pair) := by
      change (i, j) ∈ doubleCosetPairCertificateIndices shards
      rw [hindices]
      apply List.mem_filter.mpr
      exact ⟨(mem_doubleCosetOrderedPairs_iff i j).mpr hij, by simp [hskip]⟩
    obtain ⟨c, _, hcij⟩ := List.mem_map.mp hmem
    have hsep := doubleCosetSeparationCheck_sound P row hcover tests htests
      c.witness (representatives c.pair.1) (representatives c.pair.2) c.checked
    simpa only [hcij] using hsep
  intro i j hij
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hordered i j hijlt
  · exact doubleCoset_separation_symm P (representatives j) (representatives i)
      (hordered j i hjilt)

end LisiSabatini
