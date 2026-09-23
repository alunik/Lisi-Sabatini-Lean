module

public import LisiSabatini.GoodSolvableReduction
public import LisiSabatini.NilpotentTranslatedRegularityReduction
public import LisiSabatini.NilpotentIntersectionCorollaries

/-!
# The good solvable case

For a finite solvable group, property (*) in every normal quotient implies
simultaneous attainment of all prescribed Sylow cores. The translated
linear input is proved in `NilpotentTranslatedRegularityReduction` and is
supplied here; these public endpoints have no additional linear premise.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG uI

/-- The prime-field nilpotent translated theorem supplies the full
normal-component synchronization theorem in every characteristic. -/
theorem regularNormalComponentSynchronization :
    RegularNormalComponentSynchronization.{uI} :=
  regularNormalComponentSynchronization_of_nilpotentTranslatedRegularity
    nilpotentTranslatedRegularity

/-- The strong form of the paper's main theorem: every prescribed family
of Sylows at distinct primes simultaneously intersects in its prime cores. -/
theorem strongLisiSabatini_of_solvable_of_quotientSylowCoreAttainment
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : QuotientSylowCoreAttainment G) :
    StrongLisiSabatini.{uG, uI} G :=
  strongLisiSabatini_of_quotientStar_of_linearSynchronization
    regularNormalComponentSynchronization hstar

/-- The original inclusion-minimal formulation of the good solvable case. -/
theorem hasLisiSabatini_of_solvable_of_quotientSylowCoreAttainment
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : QuotientSylowCoreAttainment G) :
    HasLisiSabatini.{uG, uI} G :=
  StrongLisiSabatini.hasLisiSabatini
    (strongLisiSabatini_of_solvable_of_quotientSylowCoreAttainment hstar)

/-- A formulation with the manuscript's literal quantification over normal
quotients, using the proved equivalence with the surjective-image API. -/
theorem hasLisiSabatini_of_solvable_of_normal_quotients
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : ∀ (N : Subgroup G) [N.Normal], SylowCoreAttainment (G ⧸ N)) :
    HasLisiSabatini.{uG, uI} G :=
  hasLisiSabatini_of_solvable_of_quotientSylowCoreAttainment
    (quotientSylowCoreAttainment_iff_normal_quotients.mpr hstar)

/-- The nilpotent self-intersection consequence under the same hypotheses. -/
theorem nilpotentSelfIntersectionInFitting_of_solvable_of_quotientSylowCoreAttainment
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hstar : QuotientSylowCoreAttainment G) :
    NilpotentSelfIntersectionInFitting G :=
  nilpotentSelfIntersectionInFitting_of_strongLS
    (strongLisiSabatini_of_solvable_of_quotientSylowCoreAttainment hstar)

end LisiSabatini
