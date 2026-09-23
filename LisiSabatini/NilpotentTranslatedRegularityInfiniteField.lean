module

public import LisiSabatini.LinearAction
public import Mathlib.Algebra.Module.Submodule.Union
public import Mathlib.LinearAlgebra.Prod

/-!
# Simultaneous regular translates over an infinite field

A finite family of proper translated linear subspaces cannot cover a vector
space over an infinite field, without any dimension assumption. Homogenizing
in `V × k` reduces this statement to Mathlib's finite-union theorem for linear
subspaces. Applied to the fixed spaces of the nonidentity elements, this gives
simultaneously regular translates for every faithful finite linear group.
Nilpotence, complete reducibility, and pre-existing regular vectors are not
needed in this case.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uK uV uI uG

variable {k : Type uK} [Field k] [Infinite k]
variable {V : Type uV} [AddCommGroup V] [Module k V]

/-- Finitely many proper translated subspaces do not cover a vector space
over an infinite field. There is no finite-dimensionality hypothesis. -/
theorem exists_translate_avoiding_submodules_of_infinite_field
    {I : Type uI} [Finite I]
    (S : I → Submodule k V) (hS : ∀ i, S i ≠ ⊤) (t : I → V) :
    ∃ v : V, ∀ i, v + t i ∉ S i := by
  let F (i : I) : (V × k) →ₗ[k] V :=
    LinearMap.fst k V k + (LinearMap.snd k V k).smulRight (t i)
  let T : Option I → Submodule k (V × k)
    | none => (LinearMap.snd k V k).ker
    | some i => (S i).comap (F i)
  have hT : ∀ j, T j ≠ ⊤ := by
    intro j hj
    cases j with
    | none =>
        have hm : ((0 : V), (1 : k)) ∈ T none := by rw [hj]; trivial
        simp [T] at hm
    | some i =>
        apply hS i
        apply Submodule.eq_top_iff'.mpr
        intro v
        have hm : (v - t i, (1 : k)) ∈ T (some i) := by rw [hj]; trivial
        simpa [T, F] using hm
  obtain ⟨⟨v, a⟩, h⟩ := Submodule.exists_forall_notMem_of_forall_ne_top T hT
  have ha : a ≠ 0 := by simpa [T] using h none
  refine ⟨a⁻¹ • v, fun i hi ↦ h (some i) ?_⟩
  have hm := (S i).smul_mem a hi
  simpa [T, F, smul_add, smul_smul, ha] using hm

/-- Every finite faithful representation over an infinite field has a
common regular translate at any finitely many prescribed shifts. -/
theorem exists_regular_translates_of_faithful_representation_over_infinite_field
    {G : Type uG} [Group G] [Finite G]
    {I : Type uI} [Finite I]
    (ρ : G →* LinearMap.GeneralLinearGroup k V)
    (hρ : Function.Injective ρ) (t : I → V) :
    ∃ v : V, ∀ i, actionPointStabilizer ρ (v + t i) = ⊥ := by
  classical
  let J := I × {g : G // g ≠ 1}
  let S (j : J) : Submodule k V :=
    LinearMap.ker ((ρ j.2.1 : Module.End k V) - LinearMap.id)
  have hS : ∀ j, S j ≠ ⊤ := by
    intro j hj
    apply j.2.2
    apply hρ
    rw [map_one]
    apply Units.ext
    apply LinearMap.ext
    intro w
    have hw : w ∈ S j := by rw [hj]; trivial
    simpa [S, sub_eq_zero] using hw
  obtain ⟨v, hv⟩ := exists_translate_avoiding_submodules_of_infinite_field
    S hS (fun j ↦ t j.1)
  refine ⟨v, fun i ↦ (Subgroup.eq_bot_iff_forall _).mpr ?_⟩
  intro g hg
  by_contra hgne
  apply hv (i, ⟨g, hgne⟩)
  change (ρ g : Module.End k V) (v + t i) - (v + t i) = 0
  exact sub_eq_zero.mpr ((mem_actionPointStabilizer ρ (v + t i) g).mp hg)

/-- A concrete finite linear group is automatically faithful, so its
regular vectors can be synchronized at arbitrary finitely many shifts. -/
theorem exists_regular_translates_of_finite_linearGroup_over_infinite_field
    (K : Subgroup (LinearMap.GeneralLinearGroup k V)) [Finite K]
    {I : Type uI} [Finite I] (t : I → V) :
    ∃ v : V, ∀ i, MulAction.stabilizer K (v + t i) = ⊥ := by
  obtain ⟨v, hv⟩ :=
    exists_regular_translates_of_faithful_representation_over_infinite_field
      K.subtype Subtype.val_injective t
  exact ⟨v, hv⟩

/-- Every finite family of subgroups of a finite linear group admits
simultaneously regular translates over an infinite field. In particular this
applies to arbitrary selected Sylow subgroups, with no structural hypotheses. -/
theorem exists_regular_translates_of_subgroups_over_infinite_field
    (K : Subgroup (LinearMap.GeneralLinearGroup k V)) [Finite K]
    {I : Type uI} [Finite I] (H : I → Subgroup K) (t : I → V) :
    ∃ v : V, ∀ i,
      MulAction.stabilizer ((H i).map K.subtype) (v + t i) = ⊥ := by
  obtain ⟨v, hv⟩ :=
    exists_regular_translates_of_finite_linearGroup_over_infinite_field K t
  refine ⟨v, fun i ↦ (Subgroup.eq_bot_iff_forall _).mpr ?_⟩
  intro g hg
  obtain ⟨a, _ha, hag⟩ := g.2
  change (a : LinearMap.GeneralLinearGroup k V) =
    (g : LinearMap.GeneralLinearGroup k V) at hag
  have hafix : a ∈ MulAction.stabilizer K (v + t i) := by
    change (a : LinearMap.GeneralLinearGroup k V) • (v + t i) = v + t i
    change (g : LinearMap.GeneralLinearGroup k V) • (v + t i) = v + t i at hg
    rw [hag]
    exact hg
  have haone : a = 1 := (Subgroup.eq_bot_iff_forall _).mp (hv i) a hafix
  apply Subtype.ext
  exact hag.symm.trans (congrArg K.subtype haone)

end LisiSabatini
