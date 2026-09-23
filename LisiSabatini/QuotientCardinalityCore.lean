module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Tactic.Common
public import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Util.CompileInductive
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Cardinality of subgroup pullbacks through finite quotients
-/

@[expose] public section

namespace LisiSabatini

/-- The inverse image of a subgroup under a finite quotient has cardinality
equal to the product of the kernel cardinality and the subgroup cardinality. -/
theorem natCard_comap_quotient_eq_mul
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) (hCnormal : C.Normal)
    (D : Subgroup (G ⧸ C)) :
    Nat.card (D.comap (QuotientGroup.mk' C)) = Nat.card C * Nat.card D := by
  let : C.Normal := hCnormal
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  let M : Subgroup G := D.comap q
  have hCM : C ≤ M := by
    intro c hc
    change q c ∈ D
    rw [show q c = 1 from (QuotientGroup.eq_one_iff c).mpr hc]
    exact D.one_mem
  let qM : M →* D :=
    (q.comp M.subtype).codRestrict D (fun x ↦ x.2)
  have hqMSurj : Function.Surjective qM := by
    intro d
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective C d.1
    have hgM : g ∈ M := by
      change q g ∈ D
      simpa only [q] using hg.symm ▸ d.2
    refine ⟨⟨g, hgM⟩, ?_⟩
    apply Subtype.ext
    exact hg
  have hqMker : qM.ker = C.subgroupOf M := by
    ext x
    constructor
    · intro hx
      have hx' := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      change q (x : G) = 1 at hx'
      exact (QuotientGroup.eq_one_iff (x : G)).mp hx'
    · intro hx
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : G)).mpr hx
  have hCsubCard : Nat.card (C.subgroupOf M) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv
  calc
    Nat.card (D.comap (QuotientGroup.mk' C)) = Nat.card M := rfl
    _ = Nat.card qM.ker * Nat.card qM.range := by
      rw [← Subgroup.index_ker qM]
      exact qM.ker.card_mul_index.symm
    _ = Nat.card (C.subgroupOf M) * Nat.card D := by
      rw [hqMker, MonoidHom.range_eq_top.mpr hqMSurj, Subgroup.card_top]
    _ = Nat.card C * Nat.card D := by rw [hCsubCard]

end LisiSabatini
