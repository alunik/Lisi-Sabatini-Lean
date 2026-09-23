module

public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Necessary
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.Involutions
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.AllGood
public import LisiSabatini.SymmetricDoubleCosetCertificates.S10.AllPairs
public import LisiSabatini.SymmetricDoubleCosetGroupRows

/-! Generated literal witnesses; every acceptance is kernel checked. -/

@[expose] public section

namespace LisiSabatini.SymmetricDoubleCosetCertificates.S10

open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows

set_option maxRecDepth 100000

open LisiSabatini.SymmetricDoubleCosetCentralRows

theorem necessary_on_sylow :
    ∀ a ∈ (sylow10 : Subgroup (Equiv.Perm (Fin 10))), ∀ j, tests j a = true := by
  apply doubleCosetNecessaryCheck_sound (sylow10 : Subgroup _) row10 tests
  · intro a ha; exact (mem_sylow10_iff_row a).mp ha
  · exact necessary

theorem all_good : ∀ i, mixedSylowInter sylow10 sylow10 (reps i) = ⊥ := by
  apply doubleCosetInvolutionGoodCertificates_sound sylow10 row10 0
    (fun a ha ↦ (mem_sylow10_iff_row a).mp ha) row_zero involutionIndices
    involutions_complete tests necessary_on_sylow reps [goodCertificates]
  simpa [doubleCosetInvolutionGoodCertificateIndices] using goodCertificates_indices

theorem z10Left_central : z10Left ∈
    Subgroup.centralizer (sylow10 : Set (Equiv.Perm (Fin 10))) :=
  mem_centralizer_of_row_commute (sylow10 : Subgroup _) row10
    mem_sylow10_iff_row z10Left commute_z10Left_row

theorem z10Right_central : z10Right ∈
    Subgroup.centralizer (sylow10 : Set (Equiv.Perm (Fin 10))) :=
  mem_centralizer_of_row_commute (sylow10 : Subgroup _) row10
    mem_sylow10_iff_row z10Right commute_z10Right_row

theorem z10Both_central : z10Both ∈
    Subgroup.centralizer (sylow10 : Set (Equiv.Perm (Fin 10))) :=
  mem_centralizer_of_row_commute (sylow10 : Subgroup _) row10
    mem_sylow10_iff_row z10Both commute_z10Both_row

theorem features_central : ∀ f ∈ features,
    f.1 ∈ Subgroup.centralizer (sylow10 : Set (Equiv.Perm (Fin 10))) ∧
    f.2.1 ∈ Subgroup.centralizer (sylow10 : Set _) := by
  intro f hf
  simp only [features, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl
  · exact ⟨z10Left_central, z10Left_central⟩
  · exact ⟨z10Left_central, z10Both_central⟩

theorem shortcut_sound : ∀ i j, shortcut i j = true →
    ∀ a ∈ (sylow10 : Subgroup (Equiv.Perm (Fin 10))),
      (reps i)⁻¹ * a * reps j ∉ (sylow10 : Subgroup _) := by
  intro i j hij
  apply doubleCoset_separated_of_centralFixedPowerSignature_ne
    (sylow10 : Subgroup _) (sylow10 : Subgroup _) features features_central
  rw [signature_eq, signature_eq]
  exact of_decide_eq_true hij

theorem all_separated : ∀ i j, i ≠ j →
    ∀ a ∈ (sylow10 : Subgroup (Equiv.Perm (Fin 10))),
      (reps i)⁻¹ * a * reps j ∉ (sylow10 : Subgroup _) := by
  apply doubleCosetPairCertificates_sound_of_shortcut (sylow10 : Subgroup _) row10
    (fun a ha ↦ (mem_sylow10_iff_row a).mp ha) tests necessary_on_sylow
    reps shortcut shortcut_sound [pairCertificates] pairCertificates_indices

end LisiSabatini.SymmetricDoubleCosetCertificates.S10
