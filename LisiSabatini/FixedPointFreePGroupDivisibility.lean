import LisiSabatini.FixedPointFreeOrbitAvoidanceCore
import LisiSabatini.FiniteLinearSubgroup

/-!
# Divisibility from a fixed-point-free p-group action
-/

noncomputable section

namespace LisiSabatini

universe uR uV

/-- A nontrivial fixed-point-free `p`-group contributes its prime to the
number of nonzero ambient vectors. -/
theorem prime_dvd_natCard_sub_one_of_nontrivial_pGroup_fixedPointFreeOffZero
    {R : Type uR} {V : Type uV}
    [Finite V] [Semiring R] [AddCommGroup V] [Module R V]
    {p : ℕ} (hp : Nat.Prime p)
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : H ≠ ⊥) (hP : IsPGroup p H)
    (hfp : FixedPointFreeOffZero H) :
    p ∣ Nat.card V - 1 := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : Finite H :=
    finite_linearSubgroup_of_finite (R := R) (W := V) H
  haveI : Nontrivial H := (H.nontrivial_iff_ne_bot).2 hH
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp hP
  have he0 : e ≠ 0 := by
    intro hezero
    have hcard : Nat.card H = 1 := by simpa [hezero] using he
    exact (ne_of_gt (Finite.one_lt_card (α := H))) hcard
  exact (he.symm ▸ dvd_pow_self p he0).trans
    (natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero H hfp)

end LisiSabatini
