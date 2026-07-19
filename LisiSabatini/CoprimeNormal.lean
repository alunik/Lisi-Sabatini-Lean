import LisiSabatini.PCore
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normal subgroups at different primes

This file records the elementary coprime-normal subgroup facts used by the
affine reduction.  They are independent of any affine or representation-
theoretic hypothesis.
-/

noncomputable section

namespace LisiSabatini

universe u

variable {G : Type u} [Group G]

/-- A normal `p`-subgroup is contained in every Sylow `p`-subgroup. -/
theorem normalPSubgroup_le_sylow {p : ℕ} {N : Subgroup G}
    (hNp : IsPGroup p N) (hNn : N.Normal) (P : Sylow p G) :
    N ≤ (P : Subgroup G) :=
  (le_pCore hNp hNn).trans (pCore_le_sylow P)

/-- Subgroups at distinct prime characteristics are disjoint. -/
theorem pSubgroups_disjoint_of_ne {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hpr : p ≠ r) {P R : Subgroup G}
    (hPp : IsPGroup p P) (hRr : IsPGroup r R) : Disjoint P R :=
  IsPGroup.disjoint_of_ne p r hpr P R hPp hRr

/-- Elements of normal subgroups at distinct primes commute. -/
theorem normalPSubgroups_commute_of_ne {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (hpr : p ≠ r) {P R : Subgroup G}
    (hPp : IsPGroup p P) (hPn : P.Normal)
    (hRr : IsPGroup r R) (hRn : R.Normal)
    {x y : G} (hx : x ∈ P) (hy : y ∈ R) : Commute x y :=
  Subgroup.commute_of_normal_of_disjoint P R hPn hRn
    (pSubgroups_disjoint_of_ne hpr hPp hRr) x y hx hy

/-- The `p`-core centralizes every normal `r`-subgroup for `p ≠ r`. -/
theorem pCore_commute_normalPSubgroup_of_ne {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {R : Subgroup G} (hRr : IsPGroup r R) (hRn : R.Normal)
    {x y : G} (hx : x ∈ pCore p G) (hy : y ∈ R) : Commute x y :=
  normalPSubgroups_commute_of_ne hpr (pCore_isPGroup p G)
    (pCore_normal p G) hRr hRn hx hy

/-- Subgroup form of `pCore_commute_normalPSubgroup_of_ne`: the `p`-core is
contained in the centralizer of a normal `r`-subgroup when `p ≠ r`. -/
theorem pCore_le_centralizer_normalPSubgroup_of_ne {p r : ℕ}
    [Fact p.Prime] [Fact r.Prime] (hpr : p ≠ r)
    {R : Subgroup G} (hRr : IsPGroup r R) (hRn : R.Normal) :
    pCore p G ≤ Subgroup.centralizer (R : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (pCore_commute_normalPSubgroup_of_ne hpr hRr hRn hx hy).symm

end LisiSabatini
