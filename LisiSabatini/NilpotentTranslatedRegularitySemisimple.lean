module

public import LisiSabatini.QuasiprimitiveRepresentation
public import Mathlib.RepresentationTheory.Submodule
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent

/-!
# The characteristic is coprime to a faithful semisimple nilpotent action

The fixed space of a normal subgroup is invariant under the ambient group.
For a normal group of characteristic-power order, a semisimple complement
to this fixed space must vanish: a nonzero finite vector space in that
characteristic always has a nonzero fixed vector for a p-group action.
Faithfulness therefore kills every normal p-subgroup. In a nilpotent group
the characteristic Sylow is normal, giving the required coprimality.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

namespace Representation

variable {r : ℕ} [Fact r.Prime] {G V : Type*} [Group G]
  [AddCommGroup V] [Module (ZMod r) V]

/-- The fixed space of a normal subgroup, as an ambient invariant subspace. -/
def normalFixedInvtSubmodule (rho : _root_.Representation (ZMod r) G V)
    (P : Subgroup G) [P.Normal] : rho.invtSubmodule := by
  let W : Submodule (ZMod r) V :=
    { carrier := {v | ∀ p : P, rho p v = v}
      zero_mem' := by simp
      add_mem' := by intro x y hx hy p; rw [map_add, hx p, hy p]
      smul_mem' := by intro a x hx p; rw [map_smul, hx p] }
  refine ⟨W, (_root_.Representation.mem_invtSubmodule rho).mpr ?_⟩
  intro g v hv p
  let q : P := ⟨g⁻¹ * (p : G) * g, (inferInstance : P.Normal).conj_mem' p p.2 g⟩
  have hq := hv q
  change rho p (rho g v) = rho g v
  calc
    rho p (rho g v) = rho g (rho q v) := by
      simp only [← Module.End.mul_apply, ← map_mul]
      congr 2
      dsimp [q]
      group
    _ = rho g v := congrArg (rho g) hq

@[simp]
theorem mem_normalFixedInvtSubmodule
    (rho : _root_.Representation (ZMod r) G V)
    (P : Subgroup G) [P.Normal] (v : V) :
    v ∈ (normalFixedInvtSubmodule rho P : Submodule (ZMod r) V) ↔
      ∀ p : P, rho p v = v := Iff.rfl

/-- Semisimplicity supplies a complement in the original vector space,
with ambient invariance retained explicitly. -/
theorem exists_invariant_complement_of_semisimple
    (rho : _root_.Representation (ZMod r) G V)
    (hsemi : IsSemisimpleModule (ZMod r)[G] rho.asModule)
    (W : rho.invtSubmodule) :
    ∃ U : rho.invtSubmodule,
      IsCompl (W : Submodule (ZMod r) V) (U : Submodule (ZMod r) V) := by
  have := hsemi
  let E := _root_.Representation.mapSubmodule rho
  obtain ⟨N, hN⟩ := exists_isCompl (E W)
  refine ⟨E.symm N, ?_⟩
  have h := E.symm.isCompl hN
  rw [E.symm_apply_apply] at h
  exact IsCompl.of_eq
    (congrArg Subtype.val h.inf_eq_bot)
    (congrArg Subtype.val h.sup_eq_top)

/-- A normal p-subgroup acts trivially on any finite semisimple module
over the prime field of characteristic p. -/
theorem normal_pGroup_acts_trivially_of_semisimple
    [Finite V] (rho : _root_.Representation (ZMod r) G V)
    (hsemi : IsSemisimpleModule (ZMod r)[G] rho.asModule)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup r P) :
    ∀ p : P, ∀ v : V, rho p v = v := by
  classical
  let W := normalFixedInvtSubmodule rho P
  obtain ⟨U, hU⟩ := exists_invariant_complement_of_semisimple rho hsemi W
  have hUbot : (U : Submodule (ZMod r) V) = ⊥ := by
    by_contra hne
    have : Nontrivial (U : Submodule (ZMod r) V) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    let : MulAction P (U : Submodule (ZMod r) V) :=
      { smul := fun p u ↦ ⟨rho p u,
          ((_root_.Representation.mem_invtSubmodule rho).mp U.2 p) u.2⟩
        one_smul := by
          intro u
          apply Subtype.ext
          change rho (1 : G) u = u
          rw [map_one]
          rfl
        mul_smul := by
          intro p q u
          apply Subtype.ext
          change rho ((p : G) * q) u = rho p (rho q u)
          rw [map_mul]
          rfl }
    have hcard : r ∣ Nat.card (U : Submodule (ZMod r) V) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod]
      exact dvd_pow_self r (ne_of_gt (Module.finrank_pos
        (R := ZMod r) (M := (U : Submodule (ZMod r) V))))
    have hzero : (0 : (U : Submodule (ZMod r) V)) ∈
        MulAction.fixedPoints P (U : Submodule (ZMod r) V) := by
      intro p
      apply Subtype.ext
      exact map_zero (rho p)
    obtain ⟨v, hv, hnezero⟩ :=
      hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (U : Submodule (ZMod r) V) hcard hzero
    have hvW : (v : V) ∈ (W : Submodule (ZMod r) V) := by
      intro p
      exact congrArg Subtype.val (hv p)
    have hvzero : (v : V) = 0 := by
      have hmem : (v : V) ∈ (W : Submodule (ZMod r) V) ⊓ U := ⟨hvW, v.2⟩
      simpa [hU.inf_eq_bot] using hmem
    exact hnezero (Subtype.ext hvzero.symm)
  have hWtop : (W : Submodule (ZMod r) V) = ⊤ := by
    simpa [hUbot] using hU.sup_eq_top
  intro p v
  have hv : v ∈ (W : Submodule (ZMod r) V) := by simp [hWtop]
  exact hv p

/-- A faithful finite semisimple representation has no nontrivial normal
subgroup of characteristic-power order. -/
theorem normal_pGroup_eq_bot_of_faithful_semisimple
    [Finite V] (rho : _root_.Representation (ZMod r) G V)
    (hfaith : Function.Injective rho)
    (hsemi : IsSemisimpleModule (ZMod r)[G] rho.asModule)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup r P) : P = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall P).mpr
  intro p hp
  apply hfaith
  apply LinearMap.ext
  intro v
  simpa using normal_pGroup_acts_trivially_of_semisimple rho hsemi P hP ⟨p, hp⟩ v

end Representation

/-- A finite faithful completely reducible nilpotent linear group has
order coprime to the characteristic, including a zero-dimensional module. -/
theorem characteristic_coprime_of_nilpotent_semisimple
    {r : ℕ} [Fact r.Prime] {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Finite K] [Group.IsNilpotent K]
    (hsemi : IsSemisimpleModule (MonoidAlgebra (ZMod r) K)
      (linearSubgroupRepresentation K).asModule) :
    Nat.Coprime r (Nat.card K) := by
  apply (Fact.out : r.Prime).coprime_iff_not_dvd.mpr
  intro hdvd
  let P : Sylow r K := Classical.choice inferInstance
  have hbot : (P : Subgroup K) = ⊥ :=
    Representation.normal_pGroup_eq_bot_of_faithful_semisimple
      (linearSubgroupRepresentation K) (linearSubgroupRepresentation_faithful K)
      hsemi P P.isPGroup'
  exact P.ne_bot_of_dvd_card hdvd hbot

end LisiSabatini
