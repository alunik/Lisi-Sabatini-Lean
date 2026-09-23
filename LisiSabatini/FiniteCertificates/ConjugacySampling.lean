module

public import LisiSabatini.SylowCoreAttainment
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Conjugacy-invariant sampling certificates

For a finite conjugacy-invariant sample, the number of bad self-row
conjugators is independent of the chosen Sylow subgroup.  Thus upper
bounds certified for canonical Sylow subgroups apply to every prescribed
family.  A strict finite union bound produces a common good conjugator
inside the sample itself.

This interface concerns self-rows `P ∩ gPg⁻¹`.  It does not assert the
corresponding transport for two independently chosen Sylow rows.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini.FiniteCertificates

variable {G : Type*} [Group G]

/-- Closure of a finite sample under every inner automorphism. -/
def ConjugacyInvariantSample (C : Finset G) : Prop :=
  ∀ a g : G, g ∈ C → a * g * a⁻¹ ∈ C

/-- The exact bad self-row elements belonging to the specified sample. -/
def sampleBadConjugators (C : Finset G) {p : ℕ} (P : Sylow p G) : Finset G := by
  classical
  exact C.filter (fun g ↦ sylowInter P g ≠ ⊥)

@[simp]
theorem mem_sampleBadConjugators_iff (C : Finset G) {p : ℕ}
    (P : Sylow p G) (g : G) :
    g ∈ sampleBadConjugators C P ↔ g ∈ C ∧ sylowInter P g ≠ ⊥ := by
  classical
  exact Finset.mem_filter

/-- Simultaneous conjugation of a self-row and its conjugator preserves
whether the resulting intersection is trivial. -/
theorem sylowInter_smul_conjugate_ne_bot_iff {p : ℕ} (P : Sylow p G) (a g : G) :
    sylowInter (a • P) (a * g * a⁻¹) ≠ ⊥ ↔ sylowInter P g ≠ ⊥ := by
  rw [LisiSabatini.sylowInter_smul_conjugate]
  exact not_congr (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj a).injective)

/-- Conjugation is an exact bijection of the bad sample elements in two
conjugate self-rows. -/
theorem sampleBadConjugators_smul_eq_image [DecidableEq G] (C : Finset G)
    (hC : ConjugacyInvariantSample C) {p : ℕ} (P : Sylow p G) (a : G) :
    sampleBadConjugators C (a • P) =
      (sampleBadConjugators C P).image (MulAut.conj a) := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨hgC, hgbad⟩ := (mem_sampleBadConjugators_iff C (a • P) g).mp hg
    let x := (MulAut.conj a).symm g
    have hxg : a * x * a⁻¹ = g := (MulAut.conj a).apply_symm_apply g
    have hxC : x ∈ C := by
      simpa only [x, MulAut.conj_symm_apply, inv_inv] using hC a⁻¹ g hgC
    have hxBad : sylowInter P x ≠ ⊥ :=
      (sylowInter_smul_conjugate_ne_bot_iff P a x).mp (by rwa [hxg])
    exact Finset.mem_image.mpr
      ⟨x, (mem_sampleBadConjugators_iff C P x).mpr ⟨hxC, hxBad⟩, hxg⟩
  · intro hg
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hg
    obtain ⟨hxC, hxBad⟩ := (mem_sampleBadConjugators_iff C P x).mp hx
    apply (mem_sampleBadConjugators_iff C (a • P) _).mpr
    exact ⟨hC a x hxC, (sylowInter_smul_conjugate_ne_bot_iff P a x).mpr hxBad⟩

/-- Bad sample cardinality is the same for every Sylow subgroup at the
given prime. -/
theorem sampleBadConjugators_card_eq [Finite G]
    (C : Finset G) (hC : ConjugacyInvariantSample C)
    {p : ℕ} (hp : p.Prime) (P Q : Sylow p G) :
    (sampleBadConjugators C P).card = (sampleBadConjugators C Q).card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G P Q
  rw [← ha, sampleBadConjugators_smul_eq_image C hC P a]
  exact (Finset.card_image_of_injective _ (MulAut.conj a).injective).symm

/-- A finite union bound inside a specified sample. No conjugacy
invariance is needed at this stage. -/
theorem exists_common_sylowInter_bot_in_sample_of_bad_sum_lt
    {I : Type*} [Fintype I] (C : Finset G)
    (p : I → ℕ) (P : ∀ i, Sylow (p i) G)
    (hcard : ∑ i, (sampleBadConjugators C (P i)).card < C.card) :
    ∃ g ∈ C, ∀ i, sylowInter (P i) g = ⊥ := by
  classical
  let B := Finset.univ.biUnion (fun i ↦ sampleBadConjugators C (P i))
  have hBcard : B.card < C.card := Finset.card_biUnion_le.trans_lt hcard
  have hnot : ¬ C ⊆ B := by
    intro hsub
    exact (not_le_of_gt hBcard) (Finset.card_le_card hsub)
  obtain ⟨g, hgC, hgB⟩ := Finset.not_subset.mp hnot
  refine ⟨g, hgC, fun i ↦ ?_⟩
  by_contra hbad
  apply hgB
  exact Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, (mem_sampleBadConjugators_iff C (P i) g).mpr ⟨hgC, hbad⟩⟩

/-- Soundness of a certificate computed only on canonical Sylow
self-rows. Conjugacy invariance transports each bound to an arbitrarily
prescribed Sylow family, and the strict total bound gives one common
conjugator in the sample. Distinctness of the prime labels is unnecessary
for this counting implication. -/
theorem exists_common_sylowInter_bot_in_sample_of_canonical_bounds
    [Finite G] {I : Type*} [Fintype I]
    (C : Finset G) (hC : ConjugacyInvariantSample C)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (P : ∀ i, Sylow (p i) G) (b : I → ℕ)
    (hbad : ∀ i, (sampleBadConjugators C (P i)).card ≤ b i)
    (hsum : ∑ i, b i < C.card) (Q : ∀ i, Sylow (p i) G) :
    ∃ g ∈ C, ∀ i, sylowInter (Q i) g = ⊥ := by
  apply exists_common_sylowInter_bot_in_sample_of_bad_sum_lt C p Q
  apply lt_of_le_of_lt (Finset.sum_le_sum fun i _ ↦ ?_) hsum
  rw [sampleBadConjugators_card_eq C hC (hp i) (Q i) (P i)]
  exact hbad i

end LisiSabatini.FiniteCertificates
