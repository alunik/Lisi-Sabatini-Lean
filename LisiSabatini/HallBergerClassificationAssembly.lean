import LisiSabatini.HallBergerClassificationEasyCase
import LisiSabatini.HallBergerFirstFrattiniBranch
import LisiSabatini.HallBergerCyclicHeadUniformInversion
import LisiSabatini.HallBergerFrattiniCentralizerDecomposition
import LisiSabatini.HallBergerMixedHeadAssembly

/-!
# Final assembly of the Berger--Kovács--Newman classification

The small-Frattini case is already handled by centrality.  In the
large-Frattini case, the first branch of the Frattini dichotomy is
impossible, so the cyclic square-image seed exists whenever the Frattini
centralizer is proper.  Its centralizer is either cyclic, giving an
ambient maximal-class head, or has an internal extraspecial factor and
assembles into the mixed maximal-class branch.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- Regard a maximal-class head as the corresponding nonmixed
Hall--Berger shape. -/
def HallBergerTwoCoreShape.ofMaximalClassHead
    {G : Type u} [Group G] [Finite G]
    (head : BergerMaximalClassHead G) :
    HallBergerTwoCoreShape G :=
  match head with
  | .dihedral k hk equiv =>
      .dihedral k (by omega) equiv
  | .semidihedral k hk presentation =>
      .semidihedral k hk presentation
  | .generalizedQuaternion n hn equiv =>
      .generalizedQuaternion n (by omega) equiv

/-- The large-Frattini branch of the corrected Hall--Berger
classification. -/
theorem hallBergerTwoCoreShape_of_two_lt_natCard_frattini
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hPhiLarge : 2 < Nat.card (frattini G)) :
    Nonempty (HallBergerTwoCoreShape G) := by
  by_cases hCtop : frattiniCentralizer G = ⊤
  · exact
      hallBergerTwoCoreShape_of_frattiniCentralizer_eq_top
        hG2 hBKN hCtop
  · have hSquare :
        frattini G =
          frattiniCentralizerCenterSquareImage G :=
      frattini_eq_frattiniCentralizerCenterSquareImage_of_two_lt_natCard
        hG2 hBKN hPhiLarge
    let seed : HallBergerCyclicHeadSeed G :=
      Classical.choice
        (exists_hallBergerCyclicHeadSeed_of_squareImage_of_ne_top
          hG2 hBKN hSquare hPhiLarge hCtop)
    rcases
        frattiniCentralizer_cyclic_or_exists_internal_extraspecial_factor_with_cyclic_residual
          hG2 hBKN with
      hCcyclic | ⟨E, hE, hFactor, hResidualCyclic⟩
    · exact
        ⟨HallBergerTwoCoreShape.ofMaximalClassHead
          (seed.ambientMaximalClassHeadOfCyclicFrattiniCentralizer
            hG2 hCcyclic)⟩
    · exact
        seed.nonempty_mixedShape_of_internal_extraspecial_cyclic_residual
          hG2 hBKN E hE hFactor hResidualCyclic

/-- The Berger--Kovács--Newman two-group classification. -/
theorem bergerKovacsNewmanTwoGroupClassification :
    BergerKovacsNewmanTwoGroupClassificationStatement := by
  unfold BergerKovacsNewmanTwoGroupClassificationStatement
  intro G _ _ hG2 hBKN
  by_cases hPhiSmall :
      Nat.card (frattini G) ≤ 2
  · exact
      hallBergerTwoCoreShape_of_natCard_frattini_le_two
        hG2 hBKN hPhiSmall
  · exact
      hallBergerTwoCoreShape_of_two_lt_natCard_frattini
        hG2 hBKN (by omega)

/-- The Hall-form classification used by the affine counting
application. -/
theorem hallBergerTwoGroupClassification :
    HallBergerTwoGroupClassificationStatement :=
  hallBergerTwoGroupClassification_of_bergerKovacsNewman
    bergerKovacsNewmanTwoGroupClassification

end LisiSabatini
