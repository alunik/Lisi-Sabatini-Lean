import LisiSabatini.AffineTwoOrbitImprimitivePropagation
import LisiSabatini.ThreeSylowSolvableReduction

/-!
# Direct dimension recursion for the strong affine two-orbit invariant

Once the invariant is known for every positive-dimensional
quasiprimitive prime-field action, the strict internal imprimitivity
presentation propagates it by strong induction on dimension.  The
resulting theorem applies to every irreducible chief action, without a
solvability assumption on the ambient finite group.
-/

noncomputable section

namespace LisiSabatini

universe uG uI

/-- The exact remaining affine leaf theorem, quantified over all
positive-dimensional quasiprimitive prime-field actions. -/
def AllQuasiprimitiveActionsCommonDiagonalAffineTwoOrbitAvoidingTranslates :
    Prop :=
  ∀ (r d : ℕ) [Fact r.Prime],
    ∀ K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)),
      0 < d →
      IsQuasiprimitiveLinearAction r d K →
      CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
        r (Fin d → ZMod r) K

/-- **Fused strong dimension recursion.**  A universal quasiprimitive
two-orbit leaf theorem implies the recursively stable invariant for every
positive-dimensional irreducible prime-field action. -/
theorem
    commonDiagonalAffineTwoOrbitAvoidingTranslates_of_irreducible
    (hleaf :
      AllQuasiprimitiveActionsCommonDiagonalAffineTwoOrbitAvoidingTranslates.{uI})
    {r d : ℕ} [Fact r.Prime]
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hirr : IsIrreducibleLinearAction r d K)
    (hd : 0 < d) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
      r (Fin d → ZMod r) K := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      rcases
          quasiprimitiveLinearAction_or_strictInternalImprimitivityPresentation
            r d K hirr with hqp | hS
      · exact hleaf r d K hd hqp
      · obtain ⟨S⟩ := hS
        exact
          S.presentation
            |>.commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_children
              (fun i ↦
                ih S.localDimension S.localDimension_lt
                  (S.presentation.blockStabilizerLocalAction_irreducible i)
                  S.presentation.localDimension_pos)

/-- The universal quasiprimitive two-orbit leaf theorem supplies ordinary
CATB for every elementary-abelian chief action in the solvable induction. -/
theorem
    allSolvableChiefActionsCommonAffineTwoBaseTranslates_of_quasiprimitiveTwoOrbit
    (hleaf :
      AllQuasiprimitiveActionsCommonDiagonalAffineTwoOrbitAvoidingTranslates.{uI}) :
    AllSolvableChiefActionsCommonAffineTwoBaseTranslates.{uG, uI} := by
  intro H _ _ _ C
  letI : Fact C.r.Prime := ⟨C.prime⟩
  change
    CommonAffineTwoBaseTranslatesOn.{uI}
      C.r (Fin C.d → ZMod C.r) C.chiefAction
  exact
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.commonAffineTwoBaseTranslatesOn
      (commonDiagonalAffineTwoOrbitAvoidingTranslates_of_irreducible
        hleaf C.chiefAction_isIrreducibleLinearAction C.dimension_pos)

/-- The universal quasiprimitive two-orbit leaf theorem already closes
the mixed three-row theorem for every finite solvable group: all minimal
normal subgroups in that induction are elementary abelian. -/
theorem
    mixedThreeSylowCoreSynchronization_of_solvable_of_quasiprimitiveTwoOrbit
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hleaf :
      AllQuasiprimitiveActionsCommonDiagonalAffineTwoOrbitAvoidingTranslates.{uI}) :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G :=
  mixedThreeSylowCoreSynchronization_of_solvable_of_allChiefActionsCATB
    (allSolvableChiefActionsCommonAffineTwoBaseTranslates_of_quasiprimitiveTwoOrbit
      hleaf)

end LisiSabatini
