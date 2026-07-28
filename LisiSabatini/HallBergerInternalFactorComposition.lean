module

public import LisiSabatini.HallBergerExtraspecialExtension

/-!
# Composing internal central factors

The Hall--Berger maximality argument enlarges a central factor `E` by a
central factor found inside its residual centralizer.  This file records
that transitivity step intrinsically for subgroups.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- If `E` is an internal central factor of `C`, and `H` is an internal
central factor of the residual centralizer of `E`, then adjoining the
image of `H` to `E` gives another internal central factor of `C`.

The finiteness assumption matches the Hall--Berger application, although
the subgroup-lattice argument itself does not use it. -/
theorem IsInternalCentralFactor.sup_map_of_centralizer
    {C : Type u} [Group C] [Finite C]
    {E : Subgroup C} (hE : IsInternalCentralFactor E)
    (H : Subgroup (Subgroup.centralizer (E : Set C)))
    (hH : IsInternalCentralFactor H) :
    IsInternalCentralFactor
      (E ⊔ H.map (Subgroup.centralizer (E : Set C)).subtype) := by
  let D : Subgroup C := Subgroup.centralizer (E : Set C)
  let J : Subgroup C := H.map D.subtype
  let R : Subgroup D := Subgroup.centralizer (H : Set D)
  let R' : Subgroup C := R.map D.subtype
  have hD_decomp : J ⊔ R' = D := by
    calc
      J ⊔ R' = (H ⊔ R).map D.subtype := by
        exact (Subgroup.map_sup H R D.subtype).symm
      _ = (⊤ : Subgroup D).map D.subtype := by
        rw [hH.generate]
      _ = D.subtype.range :=
        (MonoidHom.range_eq_map D.subtype).symm
      _ = D := Subgroup.range_subtype D
  have hR'_centralizes : R' ≤
      Subgroup.centralizer ((E ⊔ J : Subgroup C) : Set C) := by
    intro r hr
    obtain ⟨rD, hrR, rfl⟩ := hr
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    let L : Subgroup C := Subgroup.centralizer ({(rD : C)} : Set C)
    have hE_le : E ≤ L := by
      intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact rD.property e he
    have hJ_le : J ≤ L := by
      rintro _ ⟨h, hh, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hrR h hh)
    have hkL : k ∈ L := (sup_le hE_le hJ_le) hk
    exact Subgroup.mem_centralizer_singleton_iff.mp hkL
  refine
    { generate := ?_
      overlap :=
        (characteristicCenterImage_eq_inf_centralizer
          (E ⊔ H.map
            (Subgroup.centralizer (E : Set C)).subtype)).symm }
  change E ⊔ J ⊔
      Subgroup.centralizer ((E ⊔ J : Subgroup C) : Set C) = ⊤
  apply top_unique
  calc
    (⊤ : Subgroup C) = E ⊔ D := by
      simpa only [D] using hE.generate.symm
    _ = E ⊔ (J ⊔ R') := by rw [hD_decomp]
    _ ≤ E ⊔ J ⊔
        Subgroup.centralizer ((E ⊔ J : Subgroup C) : Set C) :=
      sup_le
        (le_sup_left.trans le_sup_left)
        (sup_le
          (le_sup_right.trans le_sup_left)
          (hR'_centralizes.trans le_sup_right))

end LisiSabatini
