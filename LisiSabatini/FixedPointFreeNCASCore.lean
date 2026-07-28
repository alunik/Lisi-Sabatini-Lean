module

public import LisiSabatini.FixedPointFreeOffZero
public import Mathlib.GroupTheory.PGroup

/-!
# Prime-size bounds for fixed-point-free linear groups

This proof-only core contains the three facts about one nontrivial
fixed-point-free prime subgroup used by the odd-order argument.  The
active-family bounds and the NCAS compatibility criterion remain in
`FixedPointFreeNCAS.lean`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uR uV

/-- A nontrivial subgroup of a general linear group moves some vector. -/
theorem exists_ne_smul_of_ne_bot
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V)) (hH : H ≠ ⊥) :
    ∃ g : H, ∃ v : V, g • v ≠ v := by
  haveI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hH
  obtain ⟨g : H, hg⟩ := exists_ne (1 : H)
  refine ⟨g, ?_⟩
  by_contra h
  push Not at h
  apply hg
  ext v
  exact h v

/-- The orbit map of a nonzero vector is injective when the action is
fixed-point-free away from zero. -/
theorem orbitMap_injective_of_fixedPointFreeOffZero_of_ne_zero
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : FixedPointFreeOffZero H) {v : V} (hv : v ≠ 0) :
    Function.Injective (fun g : H ↦ g • v) := by
  intro a b hab
  have hfix : (b⁻¹ * a) • v = v := by
    rw [mul_smul]
    change b⁻¹ • ((fun g : H ↦ g • v) a) = v
    rw [hab, inv_smul_smul]
  have hone : b⁻¹ * a = 1 := by
    by_contra hne
    exact hv (hH (b⁻¹ * a) hne v hfix)
  exact (inv_mul_eq_one.mp hone).symm

/-- A nontrivial finite `p`-subgroup acting fixed-point-freely away from zero
has prime label strictly below the cardinality of the vector set.

The proof injects one nonzero orbit into `V`; zero is not in the image, so the
group order is strictly below `Nat.card V`.  Nontriviality of the `p`-group
then gives `p ≤ |H|`. -/
theorem prime_lt_natCard_of_fixedPointFreeOffZero
    {R : Type uR} {V : Type uV}
    [Finite V] [Semiring R] [AddCommMonoid V] [Module R V]
    {p : ℕ} (hp : Nat.Prime p)
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hP : IsPGroup p H) (hH : H ≠ ⊥)
    (hfp : FixedPointFreeOffZero H) :
    p < Nat.card V := by
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨g, v, hgv⟩ := exists_ne_smul_of_ne_bot H hH
  have hv : v ≠ 0 := by
    intro hv0
    subst v
    exact hgv (smul_zero g)
  have horbit_inj : Function.Injective (fun h : H ↦ h • v) :=
    orbitMap_injective_of_fixedPointFreeOffZero_of_ne_zero H hfp hv
  letI : Finite H := Finite.of_injective (fun h : H ↦ h • v) horbit_inj
  letI : Fintype V := Fintype.ofFinite V
  letI : Fintype H := Fintype.ofFinite H
  have horbit : Fintype.card H < Fintype.card V :=
    Fintype.card_lt_of_injective_of_notMem
      (b := (0 : V))
      (fun h : H ↦ h • v)
      horbit_inj
      (by
        intro hzero
        obtain ⟨h, hh⟩ := hzero
        exact hv (by simpa using congrArg (fun x ↦ h⁻¹ • x) hh))
  have hp_dvd : p ∣ Nat.card H :=
    hP.card_eq_or_dvd.resolve_left fun hc ↦
      hH (H.eq_bot_of_card_eq hc)
  have hp_le : p ≤ Nat.card H :=
    Nat.le_of_dvd (Nat.card_pos) hp_dvd
  have hp_le' : p ≤ Fintype.card H := by
    simpa only [Nat.card_eq_fintype_card] using hp_le
  have hp_lt : p < Fintype.card V := hp_le'.trans_lt horbit
  simpa only [Nat.card_eq_fintype_card] using hp_lt

end LisiSabatini
