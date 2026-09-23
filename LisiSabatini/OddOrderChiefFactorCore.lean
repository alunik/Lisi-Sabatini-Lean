module

public import LisiSabatini.ChiefFactorCore
public import LisiSabatini.AffineReductionCore

/-!
# Minimal chief-factor input for the odd-order theorem

This proof-only module contains exactly the group-theoretic construction used
by the direct odd-order recursion: a nontrivial minimal normal subgroup of a
finite solvable odd-order group is a positive-dimensional elementary abelian
section in odd characteristic.

The historical abstract lifting interfaces remain in
`OddOrderReductionCore.lean`, outside the import closure of the unconditional
odd-order theorem.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped IsMulCommutative

universe uG

/-- A minimal normal subgroup of a finite solvable odd-order group admits a
chief elementary-abelian section in odd characteristic.  Positivity of its
dimension follows from minimal normality via
`ChiefElementaryAbelianSection.dimension_pos`; it need not be reproved during
the coordinate construction. -/
theorem MinimalNormal.exists_oddChiefElementaryAbelianSection
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    {N : Subgroup G} (hN : MinimalNormal N)
    (hodd : Odd (Nat.card G)) :
    ∃ C : ChiefElementaryAbelianSection G,
      C.N = N ∧ C.r ≠ 2 := by
  obtain ⟨C, hCN⟩ := hN.exists_chiefElementaryAbelianSection
  let : Fact C.r.Prime := ⟨C.prime⟩
  have hp_dvd_N : C.r ∣ Nat.card C.N :=
    C.elementarySection.isPGroup_N.card_eq_or_dvd.resolve_left
      (ne_of_gt (C.N.one_lt_card_iff_ne_bot.mpr C.minimal.ne_bot))
  have hp_dvd_G : C.r ∣ Nat.card G :=
    hp_dvd_N.trans C.N.card_subgroup_dvd_card
  exact ⟨C, hCN, hodd.ne_two_of_dvd_nat hp_dvd_G⟩

end LisiSabatini
