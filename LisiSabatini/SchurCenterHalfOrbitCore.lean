import LisiSabatini.SchurWeylBasis

/-!
# Quasiprimitive full-center Schur rows

For a faithful homogeneous representation, the action of the entire center
on any simple constituent is faithful.  Transporting that action to the
finite Schur field embeds `Z(P)` in its unit group.  Thus the order of the
whole center, rather than only its canonical order-prime subgroup, divides
the order of the Schur field minus one.

The resulting full Stone--von Neumann degree row is the exact interface used
by the odd-order proof.  The historical half-orbit consequences are retained
in the compatibility module `SchurCenterHalfOrbit.lean`.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped MonoidAlgebra

/-! ## The enhanced Stone--von Neumann row -/

/-- Full quasiprimitive dimension row with divisibility by the order of the
entire center.  The Schur degree `a` is the same degree whose field has
cardinality `r^a`. -/
theorem HomogeneousDimensionData.exists_schurDegree_fullCenter_row
    {r d q : ℕ} [Fact r.Prime]
    {P : Type*} [Group P] [Finite P]
    (rho : Representation (ZMod r) P (Fin d → ZMod r))
    (H : HomogeneousDimensionData r d rho)
    (hfaith : Function.Injective rho)
    (hP : IsOddCyclicCenterClassTwo q P) :
    ∃ a b : ℕ,
      0 < a ∧ 0 < b ∧
      Nat.card (Subgroup.center P) ∣ r ^ a - 1 ∧
      q ∣ r ^ a - 1 ∧
      Nat.card (Module.End (ZMod r)[P] H.constituent) = r ^ a ∧
      d = a * q ^ hP.cyclicCenterStructuralRank * b := by
  classical
  obtain ⟨a, ha, hqDvd, hcardEnd, hconstituentDim⟩ :=
    H.exists_schurDegree_fullMultiplicity rho hfaith hP
  let S := H.constituent
  letI : IsSimpleModule (ZMod r)[P] S := H.constituent_simple
  letI : Module.Finite (ZMod r) S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars (ZMod r)) S.subtype_injective
  letI : Finite rho.asModule :=
    rho.asModuleEquiv.toEquiv.finite_iff.mpr inferInstance
  letI : Finite S := Finite.of_injective S.subtype S.subtype_injective
  letI : Module.Finite (ZMod r) (Module.End (ZMod r)[P] S) :=
    moduleFinite_schurEnd
      (k := ZMod r) (A := (ZMod r)[P]) (S := S)
  letI : Finite (Module.End (ZMod r)[P] S) :=
    Module.finite_of_finite (ZMod r)
  have hcenterDvd : Nat.card (Subgroup.center P) ∣ r ^ a - 1 := by
    have h := card_center_dvd_natCard_schurField_sub_one
      rho hfaith H.decomposition.some
    have hcardSchur : Nat.card (SchurField (ZMod r)[P] S) = r ^ a := by
      calc
        Nat.card (SchurField (ZMod r)[P] S) =
            Nat.card (Module.End (ZMod r)[P] S) :=
          Nat.card_congr (SchurField.equiv (A := (ZMod r)[P]) (S := S))
        _ = r ^ a := by simpa only [S] using hcardEnd
    rwa [hcardSchur] at h
  have hb : 0 < H.multiplicity :=
    Nat.pos_of_ne_zero H.multiplicity_neZero.out
  refine ⟨a, H.multiplicity, ha, hb, hcenterDvd, hqDvd, hcardEnd, ?_⟩
  calc
    d = H.multiplicity * Module.finrank (ZMod r) H.constituent :=
      H.dimension_eq
    _ = a * q ^ hP.cyclicCenterStructuralRank * H.multiplicity := by
      rw [hconstituentDim]
      ac_rfl

end LisiSabatini
