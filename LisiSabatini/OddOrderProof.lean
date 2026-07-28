module

public import LisiSabatini.OddOrderChiefFactorCore
public import LisiSabatini.NormalComponentReductionCore
public import LisiSabatini.PrimewiseAffineRegularityCore

/-!
# Lisi--Sabatini for finite solvable groups of odd order

This is the minimal proof-only assembly module.  It contains one direct
induction on the group order.  At a nontrivial step, choose a minimal normal
subgroup, identify it with a positive-dimensional elementary abelian chief
section in odd characteristic, apply marked primewise affine regularity to
its faithful irreducible conjugation action, and lift the induction hypothesis
from the quotient.

The linear theorem itself is proved by a direct strong induction on dimension
in `PrimewiseAffineRegularityCore.lean`.  Historical abstract lifting
interfaces and materialized block-stabilizer towers are compatibility APIs and
are not imported here.

The theorem deliberately retains `[IsSolvable G]`.  Feit--Thompson is not
hidden in either its statement or proof.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG uI

/-- **Strong Lisi--Sabatini for finite solvable groups of odd order.**

For every finite family of prescribed Sylow subgroups at distinct primes,
one conjugator makes every intersection equal to the corresponding normal
prime core. -/
theorem strongLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    StrongLisiSabatini.{uG, uI} G := by
  classical
  by_cases hsubsingleton : Subsingleton G
  · letI : Subsingleton G := hsubsingleton
    exact strongLisiSabatini_of_subsingleton
  · letI : Nontrivial G :=
      not_subsingleton_iff_nontrivial.mp hsubsingleton
    obtain ⟨N, hN⟩ := exists_minimalNormal (G := G)
    letI : N.Normal := hN.normal
    obtain ⟨C, hCN, hrTwo⟩ :=
      hN.exists_oddChiefElementaryAbelianSection hodd
    subst N
    letI : Fact C.r.Prime := ⟨C.prime⟩
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
    exact C.elementarySection.strongLisiSabatini_lift_normalComponents hodd
      (strongLisiSabatini_of_solvable_of_odd
        (hodd.of_dvd_nat C.N.card_quotient_dvd_card))
      hlinear
termination_by Nat.card G
decreasing_by
  rw [← C.N.index_eq_card, ← C.N.index_mul_card]
  exact lt_mul_of_one_lt_right
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (C.N.one_lt_card_iff_ne_bot.mpr C.minimal.ne_bot)

/-- The original inclusion-minimal Lisi--Sabatini conclusion for finite
solvable groups of odd order. -/
theorem hasLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    HasLisiSabatini.{uG, uI} G :=
  StrongLisiSabatini.hasLisiSabatini
    (strongLisiSabatini_of_solvable_of_odd.{uG, uI} hodd)

end LisiSabatini
