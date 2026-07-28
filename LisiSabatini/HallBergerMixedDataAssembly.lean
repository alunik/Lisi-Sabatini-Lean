module

public import LisiSabatini.HallBergerHeadTransport

/-!
# Assembling the internal mixed Hall--Berger datum

Once an extraspecial factor and a maximal-class head commute and generate
the ambient group, the only remaining overlap check is formal: their
intersection is the center of the extraspecial factor as soon as that
center lies in the head.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- Package commuting, generating extraspecial and maximal-class factors
as the exact mixed datum used by the affine counting theorem. -/
def bergerMixedCentralProductDataOfCommute
    {P : Type u} [Group P] [Finite P]
    (E H : Subgroup P)
    (hE : IsExtraspecial 2 E)
    (head : BergerMaximalClassHead H)
    (hcomm :
      ∀ (e : E) (h : H),
        (e : P) * h = h * e)
    (hgenerate : E ⊔ H = ⊤)
    (hcenterLe :
      characteristicCenterImage E ≤ H) :
    BergerMixedCentralProductData P where
  extraspecialPart := E
  headPart := H
  extraspecial := hE
  head := head
  commute := hcomm
  generate := hgenerate
  overlap := by
    change
      characteristicCenterImage E =
        E ⊓ H
    apply le_antisymm
    · exact le_inf
        (by
          rw [
            characteristicCenterImage_eq_inf_centralizer]
          exact inf_le_left)
        hcenterLe
    · intro x hx
      rw [
        characteristicCenterImage_eq_inf_centralizer]
      refine ⟨hx.1, ?_⟩
      intro e he
      exact
        hcomm
          ⟨e, he⟩
          ⟨x, hx.2⟩

end LisiSabatini
