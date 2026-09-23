module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Necessary
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.Involutions
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.AllGood
public import LisiSabatini.SymmetricDoubleCosetCertificates.S12.AllPairs
public import LisiSabatini.SymmetricDoubleCosetGroupRows

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S12

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

open LisiSabatini.SymmetricDoubleCosetCentralRows

theorem necessary_on_sylow :
    ∀ a ∈ (sylow12 : Subgroup (Equiv.Perm (Fin 12))), ∀ j, tests j a = true := by
  apply doubleCosetNecessaryCheck_sound (sylow12 : Subgroup _) row12 tests
  · intro a ha; exact (mem_sylow12_iff_row a).mp ha
  · exact necessary

theorem all_good : ∀ i, mixedSylowInter sylow12 sylow12 (reps i) = ⊥ := by
  apply doubleCosetInvolutionGoodCertificates_sound sylow12 row12 0
    (fun a ha ↦ (mem_sylow12_iff_row a).mp ha) row_zero involutionIndices
    involutions_complete tests necessary_on_sylow reps [goodCertificates]
  simpa [doubleCosetInvolutionGoodCertificateIndices] using goodCertificates_indices

theorem z12Left_central : z12Left ∈
    Subgroup.centralizer (sylow12 : Set (Equiv.Perm (Fin 12))) :=
  mem_centralizer_of_row_commute (sylow12 : Subgroup _) row12
    mem_sylow12_iff_row z12Left commute_z12Left_row

theorem z12Right_central : z12Right ∈
    Subgroup.centralizer (sylow12 : Set (Equiv.Perm (Fin 12))) :=
  mem_centralizer_of_row_commute (sylow12 : Subgroup _) row12
    mem_sylow12_iff_row z12Right commute_z12Right_row

theorem z12Both_central : z12Both ∈
    Subgroup.centralizer (sylow12 : Set (Equiv.Perm (Fin 12))) :=
  mem_centralizer_of_row_commute (sylow12 : Subgroup _) row12
    mem_sylow12_iff_row z12Both commute_z12Both_row

theorem features_central : ∀ f ∈ features,
    f.1 ∈ Subgroup.centralizer (sylow12 : Set (Equiv.Perm (Fin 12))) ∧
    f.2.1 ∈ Subgroup.centralizer (sylow12 : Set _) := by
  intro f hf
  simp only [features, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl
  · exact ⟨z12Left_central, z12Left_central⟩
  · exact ⟨z12Left_central, z12Both_central⟩
  · exact ⟨z12Both_central, z12Left_central⟩
  · exact ⟨z12Both_central, z12Both_central⟩
  · exact ⟨z12Left_central, z12Left_central⟩

theorem shortcut_sound : ∀ i j, shortcut i j = true →
    ∀ a ∈ (sylow12 : Subgroup (Equiv.Perm (Fin 12))),
      (reps i)⁻¹ * a * reps j ∉ (sylow12 : Subgroup _) := by
  intro i j hij
  apply doubleCoset_separated_of_centralFixedPowerSignature_ne
    (sylow12 : Subgroup _) (sylow12 : Subgroup _) features features_central
  rw [signature_eq, signature_eq]
  exact of_decide_eq_true hij

theorem all_separated : ∀ i j, i ≠ j →
    ∀ a ∈ (sylow12 : Subgroup (Equiv.Perm (Fin 12))),
      (reps i)⁻¹ * a * reps j ∉ (sylow12 : Subgroup _) := by
  apply doubleCosetPairCertificates_sound_of_shortcut (sylow12 : Subgroup _) row12
    (fun a ha ↦ (mem_sylow12_iff_row a).mp ha) tests necessary_on_sylow
    reps shortcut shortcut_sound [pairCertificates] pairCertificates_indices

end LisiSabatini.SymmetricDoubleCosetCertificates.S12
