module

public import LisiSabatini.CliffordImprimitivity
public import LisiSabatini.FiniteLinearSubgroup
public import LisiSabatini.LinearImprimitivityPresentationExtractionCore

/-!
# Structural dichotomy at the recursive NCAS interface

Clifford theory supplies an extraction witness whenever an irreducible
finite linear action is not quasiprimitive.  The existing presentation
extraction machinery turns that witness into the exact prime-field primitive
internal imprimitivity presentation consumed by recursive NCAS.  This file
packages those two completed bridges as one public dichotomy.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

/-- Every irreducible concrete prime-field action is either quasiprimitive or
comes with a fully coordinated primitive internal imprimitivity presentation.

The imprimitive alternative includes the block count, local dimension,
internal direct-sum system, common local coordinates, and primitive
permutation top.  No coprimality or cross-characteristic hypothesis is used. -/
theorem quasiprimitiveLinearAction_or_internalImprimitivityPresentation
    (r d : ℕ) [Fact r.Prime]
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (hirr : IsIrreducibleLinearAction r d K) :
    IsQuasiprimitiveLinearAction r d K ∨
      Nonempty (Σ b e : ℕ,
        PrimeFieldPrimitiveInternalImprimitivityPresentation
          r b e (Fin d → ZMod r) K) := by
  let : Finite K := finite_linearSubgroup_of_finite K
  rcases Clifford.quasiprimitiveLinearAction_or_extractionWitness
      r d K hirr with hqp | hW
  · exact Or.inl hqp
  · obtain ⟨W⟩ := hW
    exact Or.inr
      ⟨ExtractedPrimitiveCoarsening.internalPresentationSigmaOfFiniteDimensional W⟩

end LisiSabatini
