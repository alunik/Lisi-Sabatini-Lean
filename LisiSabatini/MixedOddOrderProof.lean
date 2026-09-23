module

public import LisiSabatini.MixedNormalComponentReductionCore
public import LisiSabatini.OddOrderChiefFactorCore
public import LisiSabatini.PrimewiseAffineRegularityCore

/-!
# Mixed two-row synchronization in finite solvable groups of odd order

This module proves the first new theorem of the three-conjugates programme.
The prescribed Sylow rows `P` and `Q` are independent.  The linear theorem
is unchanged: the second row contributes only an arbitrary affine
translation, which the existing primewise affine regularity theorem already
allows.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG uI

/-- **Mixed strong Lisi--Sabatini for finite solvable groups of odd order.**

For every finite family of distinct primes and every two independently
prescribed Sylow rows, one conjugator makes all mixed intersections equal to
their normal prime cores. -/
theorem mixedStrongLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    HasMixedTwoSylowCoreSynchronization.{uG, uI} G := by
  classical
  by_cases hsubsingleton : Subsingleton G
  · let : Subsingleton G := hsubsingleton
    exact mixedTwoSylowCoreSynchronization_of_subsingleton
  · let : Nontrivial G :=
      not_subsingleton_iff_nontrivial.mp hsubsingleton
    obtain ⟨N, hN⟩ := exists_minimalNormal (G := G)
    let : N.Normal := hN.normal
    obtain ⟨C, hCN, hrTwo⟩ :=
      hN.exists_oddChiefElementaryAbelianSection hodd
    subst N
    let : Fact C.r.Prime := ⟨C.prime⟩
    have hmarked : NormalComponentOrbitAvoidingSynchronization.{uI}
        C.r C.d C.chiefAction :=
      primewiseAffineOrbitAvoidance_of_irreducible.{uI}
        hrTwo C.chiefAction_isIrreducibleLinearAction C.dimension_pos
    have hlinearChief : NormalComponentAffineSynchronization.{uI}
        C.r C.d C.chiefAction :=
      NormalComponentOrbitAvoidingSynchronizationOn.normalComponentAffineSynchronization
        hmarked
    have hlinear : NormalComponentAffineSynchronization.{uI}
        C.r C.d C.elementarySection.commonAction := by
      change NormalComponentAffineSynchronization.{uI}
        C.r C.d C.conjugation.range
      exact hlinearChief
    exact
      C.elementarySection.mixedTwoSylowCoreSynchronization_lift_normalComponents
        hodd
        (mixedStrongLisiSabatini_of_solvable_of_odd
          (hodd.of_dvd_nat C.N.card_quotient_dvd_card))
        hlinear
termination_by Nat.card G
decreasing_by
  rw [← C.N.index_eq_card, ← C.N.index_mul_card]
  exact lt_mul_of_one_lt_right
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (C.N.one_lt_card_iff_ne_bot.mpr C.minimal.ne_bot)

/-- Diagonal specialization: the mixed theorem recovers the existing strong
same-row odd-order theorem. -/
theorem strongLisiSabatini_of_mixed_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    StrongLisiSabatini.{uG, uI} G :=
  HasMixedTwoSylowCoreSynchronization.strongLisiSabatini
    (mixedStrongLisiSabatini_of_solvable_of_odd.{uG, uI} hodd)

/-- The mixed two-row theorem immediately supplies mixed three-row
synchronization in finite solvable odd-order groups. -/
theorem mixedThreeSylowCoreSynchronization_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G :=
  mixedTwo_to_mixedThree
    (mixedStrongLisiSabatini_of_solvable_of_odd.{uG, uI} hodd)

end LisiSabatini
