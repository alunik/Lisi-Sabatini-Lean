module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Necessary
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.Involutions
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.AllGood
public import LisiSabatini.SymmetricDoubleCosetCertificates.S9.AllPairs
public import LisiSabatini.SymmetricDoubleCosetGroupRows

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S9

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

open LisiSabatini.SymmetricDoubleCosetCentralRows

theorem necessary_on_sylow :
    ∀ a ∈ (sylow9 : Subgroup (Equiv.Perm (Fin 9))), ∀ j, tests j a = true := by
  apply doubleCosetNecessaryCheck_sound (sylow9 : Subgroup _) row9 tests
  · intro a ha; exact (mem_sylow9_iff_row a).mp ha
  · exact necessary

theorem all_good : ∀ i, mixedSylowInter sylow9 sylow9 (reps i) = ⊥ := by
  apply doubleCosetInvolutionGoodCertificates_sound sylow9 row9 0
    (fun a ha ↦ (mem_sylow9_iff_row a).mp ha) row_zero involutionIndices
    involutions_complete tests necessary_on_sylow reps [goodCertificates]
  simpa [doubleCosetInvolutionGoodCertificateIndices] using goodCertificates_indices

theorem z9_central : z9 ∈
    Subgroup.centralizer (sylow9 : Set (Equiv.Perm (Fin 9))) :=
  mem_centralizer_of_row_commute (sylow9 : Subgroup _) row9
    mem_sylow9_iff_row z9 commute_z9_row

theorem features_central : ∀ f ∈ features,
    f.1 ∈ Subgroup.centralizer (sylow9 : Set (Equiv.Perm (Fin 9))) ∧
    f.2.1 ∈ Subgroup.centralizer (sylow9 : Set _) := by
  intro f hf
  simp only [features, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl
  · exact ⟨z9_central, z9_central⟩

theorem shortcut_sound : ∀ i j, shortcut i j = true →
    ∀ a ∈ (sylow9 : Subgroup (Equiv.Perm (Fin 9))),
      (reps i)⁻¹ * a * reps j ∉ (sylow9 : Subgroup _) := by
  intro i j hij
  apply doubleCoset_separated_of_centralFixedPowerSignature_ne
    (sylow9 : Subgroup _) (sylow9 : Subgroup _) features features_central
  rw [signature_eq, signature_eq]
  exact of_decide_eq_true hij

theorem all_separated : ∀ i j, i ≠ j →
    ∀ a ∈ (sylow9 : Subgroup (Equiv.Perm (Fin 9))),
      (reps i)⁻¹ * a * reps j ∉ (sylow9 : Subgroup _) := by
  apply doubleCosetPairCertificates_sound_of_shortcut (sylow9 : Subgroup _) row9
    (fun a ha ↦ (mem_sylow9_iff_row a).mp ha) tests necessary_on_sylow
    reps shortcut shortcut_sound [pairCertificates] pairCertificates_indices

end LisiSabatini.SymmetricDoubleCosetCertificates.S9
