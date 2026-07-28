import LisiSabatini.SectionConstructionCore
import LisiSabatini.MinimalNormalCore
import Mathlib.Algebra.Module.Submodule.Lattice

/-!
# The irreducible action of a chief elementary-abelian section

This proof-only core pulls invariant coordinate submodules directly back to
ambient normal subgroups.  Representation-theoretic compatibility APIs,
solvability, action-order, and defining-characteristic core results remain
in `ChiefAction.lean`.
-/

noncomputable section

namespace LisiSabatini

universe u

variable {G : Type u} [Group G]

/-- A field-instance-free irreducibility predicate for a concrete subgroup
of a general linear group. -/
def IsIrreducibleLinearAction
    (r d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop :=
  ∀ U : Submodule (ZMod r) (Fin d → ZMod r),
    (∀ k : K, ∀ v ∈ U,
      (k : LinearMap.GeneralLinearGroup
        (ZMod r) (Fin d → ZMod r)) • v ∈ U) →
    U = ⊥ ∨ U = ⊤

/-- An elementary-abelian normal section together with minimal normality. -/
structure ChiefElementaryAbelianSection (G : Type u) [Group G]
    extends ElementaryAbelianSection G where
  minimal : MinimalNormal toElementaryAbelianSection.N

namespace ChiefElementaryAbelianSection

variable (S : ChiefElementaryAbelianSection G)

/-- Forget the chief-factor certificate. -/
abbrev elementarySection : ElementaryAbelianSection G :=
  S.toElementaryAbelianSection

/-- The faithful linear image induced by conjugation on the chief factor. -/
def chiefAction :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod S.r) (Fin S.d → ZMod S.r)) :=
  S.conjugation.range

/-- Minimal normality forces the coordinate dimension to be positive. -/
theorem dimension_pos : 0 < S.d := by
  apply Nat.pos_of_ne_zero
  intro hd
  apply S.minimal.ne_bot
  apply (Subgroup.eq_bot_iff_forall S.N).mpr
  intro x hx
  let n : S.N := ⟨x, hx⟩
  have hempty : IsEmpty (Fin S.d) := by
    rw [hd]
    infer_instance
  have hcoord : S.coordinates (Additive.ofMul n) = 0 := by
    funext i
    exact isEmptyElim i
  have hn : n = 1 := by
    apply Additive.ofMul.injective
    apply S.coordinates.injective
    simpa using hcoord
  exact congrArg Subtype.val hn

/-- The subgroup of the chief factor cut out by a coordinate submodule. -/
def coordinateSubgroup
    (U : Submodule (ZMod S.r) (Fin S.d → ZMod S.r)) : Subgroup S.N where
  carrier := {n | S.coordinates (Additive.ofMul n) ∈ U}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    change S.coordinates (Additive.ofMul (a * b)) ∈ U
    simpa using U.add_mem ha hb
  inv_mem' {a} ha := by
    change S.coordinates (Additive.ofMul a⁻¹) ∈ U
    simpa using U.neg_mem ha

@[simp]
theorem mem_coordinateSubgroup
    (U : Submodule (ZMod S.r) (Fin S.d → ZMod S.r)) (n : S.N) :
    n ∈ S.coordinateSubgroup U ↔ S.coordinates (Additive.ofMul n) ∈ U :=
  Iff.rfl

/-- Pull a coordinate submodule back to an ambient subgroup. -/
def ambientCoordinateSubgroup
    (U : Submodule (ZMod S.r) (Fin S.d → ZMod S.r)) : Subgroup G :=
  (S.coordinateSubgroup U).map S.N.subtype

theorem ambientCoordinateSubgroup_le_N
    (U : Submodule (ZMod S.r) (Fin S.d → ZMod S.r)) :
    S.ambientCoordinateSubgroup U ≤ S.N :=
  Subgroup.map_subtype_le _

/-- An invariant coordinate submodule pulls back to an ambient normal
subgroup. -/
theorem ambientCoordinateSubgroup_normal
    (U : Submodule (ZMod S.r) (Fin S.d → ZMod S.r))
    (hU : ∀ k : S.chiefAction, ∀ v ∈ U,
      (k : LinearMap.GeneralLinearGroup
        (ZMod S.r) (Fin S.d → ZMod S.r)) • v ∈ U) :
    (S.ambientCoordinateSubgroup U).Normal := by
  constructor
  intro x hx g
  rcases hx with ⟨n, hnU, rfl⟩
  let k : S.chiefAction := ⟨S.conjugation g, ⟨g, rfl⟩⟩
  let n' : S.N := normalConj S.N S.normal g n
  refine ⟨n', ?_, ?_⟩
  · change S.coordinates (Additive.ofMul n') ∈ U
    have hstable := hU k (S.coordinates (Additive.ofMul n)) hnU
    change S.conjugation g • S.coordinates (Additive.ofMul n) ∈ U at hstable
    rw [S.conjugation_apply] at hstable
    exact hstable
  · simp [n', coe_normalConj]

/-- The pulled-back subgroup is trivial exactly when the coordinate
submodule is trivial. -/
theorem ambientCoordinateSubgroup_eq_bot_iff
    (U : Submodule (ZMod S.r) (Fin S.d → ZMod S.r)) :
    S.ambientCoordinateSubgroup U = ⊥ ↔ U = ⊥ := by
  constructor
  · intro hM
    apply le_antisymm
    · intro v hv
      let n : S.N := Additive.toMul (S.coordinates.symm v)
      have hnU : n ∈ S.coordinateSubgroup U := by simpa [n]
      have hnM : (n : G) ∈ S.ambientCoordinateSubgroup U := ⟨n, hnU, rfl⟩
      rw [hM] at hnM
      have hnOne : n = 1 := by
        apply Subtype.ext
        simpa using hnM
      have hvzero : v = 0 := by
        calc
          v = S.coordinates (Additive.ofMul n) := by simp [n]
          _ = S.coordinates (Additive.ofMul 1) := by rw [hnOne]
          _ = 0 := by simp
      simp [hvzero]
    · exact bot_le
  · intro hU
    subst U
    apply le_antisymm
    · rintro x ⟨n, hn, rfl⟩
      change S.coordinates (Additive.ofMul n) ∈
        (⊥ : Submodule (ZMod S.r) (Fin S.d → ZMod S.r)) at hn
      have hnOne : n = 1 := by
        apply Additive.ofMul.injective
        apply S.coordinates.injective
        simpa using hn
      simp [hnOne]
    · exact bot_le

/-- The pulled-back subgroup is the whole chief factor exactly when the
coordinate submodule is the whole module. -/
theorem ambientCoordinateSubgroup_eq_N_iff
    (U : Submodule (ZMod S.r) (Fin S.d → ZMod S.r)) :
    S.ambientCoordinateSubgroup U = S.N ↔ U = ⊤ := by
  constructor
  · intro hM
    apply le_antisymm le_top
    intro v _
    let n : S.N := Additive.toMul (S.coordinates.symm v)
    have hnN : (n : G) ∈ S.N := n.2
    have hnM : (n : G) ∈ S.ambientCoordinateSubgroup U := hM.ge hnN
    rcases hnM with ⟨m, hmU, hm⟩
    have hmn : m = n := S.N.subtype_injective hm
    subst m
    simpa [n] using hmU
  · intro hU
    subst U
    apply le_antisymm (S.ambientCoordinateSubgroup_le_N ⊤)
    intro x hx
    let n : S.N := ⟨x, hx⟩
    refine ⟨n, ?_, rfl⟩
    change S.coordinates (Additive.ofMul n) ∈
      (⊤ : Submodule (ZMod S.r) (Fin S.d → ZMod S.r))
    exact Submodule.mem_top

/-- Minimal normality proves irreducibility directly, without first passing
through `Subrepresentation` or a typeclass-valued irreducibility theorem. -/
theorem chiefAction_isIrreducibleLinearAction :
    IsIrreducibleLinearAction S.r S.d S.chiefAction := by
  intro U hU
  letI : (S.ambientCoordinateSubgroup U).Normal :=
    S.ambientCoordinateSubgroup_normal U hU
  rcases S.minimal.eq_bot_or_eq (S.ambientCoordinateSubgroup U)
      inferInstance (S.ambientCoordinateSubgroup_le_N U) with hbot | htop
  · exact Or.inl ((S.ambientCoordinateSubgroup_eq_bot_iff U).mp hbot)
  · exact Or.inr ((S.ambientCoordinateSubgroup_eq_N_iff U).mp htop)

/-- Bundle a previously constructed elementary section with minimal
normality. -/
def ofSection (T : ElementaryAbelianSection G) (hT : MinimalNormal T.N) :
    ChiefElementaryAbelianSection G where
  toElementaryAbelianSection := T
  minimal := hT

end ChiefElementaryAbelianSection

end LisiSabatini
