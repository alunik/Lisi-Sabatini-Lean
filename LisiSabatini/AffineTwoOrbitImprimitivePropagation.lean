import LisiSabatini.ActiveTopTwoOrbitComposition
import LisiSabatini.BlockStabilizerLocalAction
import LisiSabatini.DiagonalAffineTwoOrbitLinearEquiv
import LisiSabatini.DiagonalPairImprimitiveAction

/-!
# Strong affine two-orbit propagation through imprimitivity

The diagonal action on two copies of an imprimitive module becomes an
ordinary imprimitive action on blockwise pairs.  The parity-free ternary
top theorem therefore propagates the recursively stable two-orbit
invariant from the faithful block-stabilizer local actions to the original
action.
-/

noncomputable section

namespace LisiSabatini

universe uJ uV

namespace PrimeFieldPrimitiveInternalImprimitivityPresentation

variable {r b e : ℕ} {V : Type uV}
variable [AddCommGroup V] [Module (ZMod r) V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}

/-- Two-orbit diagonal synchronization in every faithful
block-stabilizer local action propagates through one strict primitive-top
imprimitive layer. -/
theorem commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_children
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K)
    (hlocal : ∀ i : Fin b,
      CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uJ}
        r (Fin e → ZMod r) (P.blockStabilizerLocalAction i)) :
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uJ} r V K := by
  have hblock :
      CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uJ} r
        (Fin b → Fin e → ZMod r) P.blockAction := by
    let D := P.imprimitiveLinearActionData
    let D₂ := D.diagonalPair
    letI : Nonempty (Fin b) := Fin.pos_iff_nonempty.mp
      (P.blockCount_one_lt.trans' Nat.zero_lt_one)
    letI : Finite D₂.blockPerm.range := by
      rw [D.diagonalPair_blockPerm_range]
      exact P.toPrimitiveImprimitivityPresentation.top_finite
    letI : FaithfulSMul D₂.blockPerm.range (Fin b) := by
      rw [D.diagonalPair_blockPerm_range]
      exact P.toPrimitiveImprimitivityPresentation.top_faithful
    letI : MulAction.IsPreprimitive D₂.blockPerm.range (Fin b) := by
      rw [D.diagonalPair_blockPerm_range]
      exact P.toPrimitiveImprimitivityPresentation.top_preprimitive
    intro J _ p hp hinj hcross H hHnormal hHp
    cases isEmpty_or_nonempty J with
    | inl hJ =>
        letI : IsEmpty J := hJ
        intro j
        exact isEmptyElim j
    | inr hJ =>
        letI : Nonempty J := hJ
        let H₂ : J → Subgroup (pairedSubgroup P.blockAction) :=
          fun j ↦ pairedInternalSubgroup P.blockAction (H j)
        have hpaired :
            TwoOrbitAvoidingCommonRegularTranslates
              (fun j ↦
                ImprimitiveLinearActionData.restrictedAmbient (H₂ j)) := by
          apply
            D₂.twoOrbitAvoidingCommonRegularTranslates_of_primitiveTop_of_localTwoOrbit
              p hp hinj H₂
              (fun j ↦
                pairedInternalSubgroup_normal P.blockAction
                  (H j) (hHnormal j))
              (fun j ↦
                pairedInternalSubgroup_isPGroup P.blockAction
                  (H j) (hHp j))
          intro i
          have hi :=
            hlocal i p hp hinj hcross
              (fun j ↦
                P.componentBaseInBlockStabilizerLocalActionOfBlockAction
                  (H j) i)
              (fun j ↦
                P.componentBaseInBlockStabilizerLocalActionOfBlockAction_normal
                  (H j) (hHnormal j) i)
              (fun j ↦
                P.componentBaseInBlockStabilizerLocalActionOfBlockAction_isPGroup
                  (H j) (hHp j) i)
          simpa only [
            D₂, H₂,
            D.diagonalPair_componentBaseImageInCommonLocalGL,
            P.map_componentBaseInBlockStabilizerLocalActionOfBlockAction_subtype_eq_commonLocalGL]
            using hi
        let pairCoordinates :=
          piProdLinearEquiv
            (I := Fin b) (R := ZMod r) (W := Fin e → ZMod r)
        have hambient :
            (fun j ↦
              ImprimitiveLinearActionData.restrictedAmbient (H₂ j)) =
              (fun j ↦
                (((H j).map P.blockAction.subtype).map
                    (diagonalGeneralLinearHom
                      (ZMod r) (Fin b → Fin e → ZMod r))).map
                  (NCASLinearEquiv.conjugation
                    pairCoordinates).toMonoidHom) := by
          funext j
          change
            (pairedInternalSubgroup P.blockAction (H j)).map
                (pairedSubgroup P.blockAction).subtype =
              (((H j).map P.blockAction.subtype).map
                  (diagonalGeneralLinearHom
                    (ZMod r) (Fin b → Fin e → ZMod r))).map
                (NCASLinearEquiv.conjugation
                  pairCoordinates).toMonoidHom
          rw [pairedInternalSubgroup_map_subtype]
          simp only [pairedGeneralLinearHom, Subgroup.map_map]
          congr 1
        rw [hambient] at hpaired
        exact
          (NCASLinearEquiv.twoOrbitAvoidingCommonRegularTranslates_map_conjugation_iff
            pairCoordinates
            (fun j ↦
              ((H j).map P.blockAction.subtype).map
                (diagonalGeneralLinearHom
                  (ZMod r) (Fin b → Fin e → ZMod r)))).mp hpaired
  apply
    NCASLinearEquiv.commonDiagonalAffineTwoOrbitAvoidingTranslatesOn_of_conjugate
      P.coordinates K
  exact hblock

end PrimeFieldPrimitiveInternalImprimitivityPresentation

end LisiSabatini
