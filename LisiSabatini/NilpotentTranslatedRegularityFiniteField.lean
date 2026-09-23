module

public import LisiSabatini.NilpotentTranslatedRegularityReduction
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.Algebra.CharP.Lemmas

/-!
# Translated regular orbits over arbitrary finite fields

This module removes the prime-field coordinate presentation from the
translated regular-orbit theorem. The hypotheses are a finite nilpotent
group and a faithful semisimple representation on a finite vector space
over a finite field. No coprimality premise is required: the normal
characteristic Sylow acts trivially by semisimplicity and is killed by
faithfulness. Scalar restriction and a basis then identify the action with
the prime-field coordinate theorem.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

namespace FiniteFieldRepresentation

variable {r : ℕ} [Fact r.Prime] {k G V : Type*} [Field k] [CharP k r] [Group G]
  [AddCommGroup V] [Module k V]

/-- The fixed space of a normal subgroup, as an ambient invariant subspace. -/
def normalFixedInvtSubmodule (rho : _root_.Representation k G V)
    (P : Subgroup G) [P.Normal] : rho.invtSubmodule := by
  let W : Submodule k V :=
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
    (rho : _root_.Representation k G V)
    (P : Subgroup G) [P.Normal] (v : V) :
    v ∈ (normalFixedInvtSubmodule rho P : Submodule k V) ↔
      ∀ p : P, rho p v = v := Iff.rfl

/-- Semisimplicity supplies a complement in the original vector space,
with ambient invariance retained explicitly. -/
theorem exists_invariant_complement_of_semisimple
    (rho : _root_.Representation k G V)
    (hsemi : IsSemisimpleModule k[G] rho.asModule)
    (W : rho.invtSubmodule) :
    ∃ U : rho.invtSubmodule,
      IsCompl (W : Submodule k V) (U : Submodule k V) := by
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
over a field of characteristic p. -/
theorem normal_pGroup_acts_trivially_of_semisimple
    [Finite V] (rho : _root_.Representation k G V)
    (hsemi : IsSemisimpleModule k[G] rho.asModule)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup r P) :
    ∀ p : P, ∀ v : V, rho p v = v := by
  classical
  let W := normalFixedInvtSubmodule rho P
  obtain ⟨U, hU⟩ := exists_invariant_complement_of_semisimple rho hsemi W
  have hUbot : (U : Submodule k V) = ⊥ := by
    by_contra hne
    have : Nontrivial (U : Submodule k V) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    let : MulAction P (U : Submodule k V) :=
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
    have hcard : r ∣ Nat.card (U : Submodule k V) := by
      let : Algebra (ZMod r) k := ZMod.algebra k r
      let : Module (ZMod r) (U : Submodule k V) :=
        Module.compHom (U : Submodule k V) (algebraMap (ZMod r) k)
      rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod]
      exact dvd_pow_self r (ne_of_gt (Module.finrank_pos
        (R := ZMod r) (M := (U : Submodule k V))))
    have hzero : (0 : (U : Submodule k V)) ∈
        MulAction.fixedPoints P (U : Submodule k V) := by
      intro p
      apply Subtype.ext
      exact map_zero (rho p)
    obtain ⟨v, hv, hnezero⟩ :=
      hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
        (U : Submodule k V) hcard hzero
    have hvW : (v : V) ∈ (W : Submodule k V) := by
      intro p
      exact congrArg Subtype.val (hv p)
    have hvzero : (v : V) = 0 := by
      have hmem : (v : V) ∈ (W : Submodule k V) ⊓ U := ⟨hvW, v.2⟩
      simpa [hU.inf_eq_bot] using hmem
    exact hnezero (Subtype.ext hvzero.symm)
  have hWtop : (W : Submodule k V) = ⊤ := by
    simpa [hUbot] using hU.sup_eq_top
  intro p v
  have hv : v ∈ (W : Submodule k V) := by simp [hWtop]
  exact hv p

/-- A faithful finite semisimple representation has no nontrivial normal
subgroup of characteristic-power order. -/
theorem normal_pGroup_eq_bot_of_faithful_semisimple
    [Finite V] (rho : _root_.Representation k G V)
    (hfaith : Function.Injective rho)
    (hsemi : IsSemisimpleModule k[G] rho.asModule)
    (P : Subgroup G) [P.Normal] (hP : IsPGroup r P) : P = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall P).mpr
  intro p hp
  apply hfaith
  apply LinearMap.ext
  intro v
  simpa using normal_pGroup_acts_trivially_of_semisimple rho hsemi P hP ⟨p, hp⟩ v

/-- Faithful semisimplicity forces a finite nilpotent group to have order
coprime to the positive characteristic of the field. -/
theorem characteristic_coprime_of_faithful_semisimple
    [Finite G] [Finite V] [Group.IsNilpotent G]
    (rho : _root_.Representation k G V)
    (hfaith : Function.Injective rho)
    (hsemi : IsSemisimpleModule k[G] rho.asModule) :
    Nat.Coprime r (Nat.card G) := by
  apply (Fact.out : r.Prime).coprime_iff_not_dvd.mpr
  intro hdvd
  let P : Sylow r G := Classical.choice inferInstance
  have hbot : (P : Subgroup G) = ⊥ :=
    normal_pGroup_eq_bot_of_faithful_semisimple rho hfaith hsemi P P.isPGroup'
  exact P.ne_bot_of_dvd_card hdvd hbot

end FiniteFieldRepresentation

private theorem faithful_image_regular_iff
    {G R W : Type*} [Group G] [Semiring R]
    [AddCommMonoid W] [Module R W]
    (sigma : G →* LinearMap.GeneralLinearGroup R W)
    (hfaith : Function.Injective sigma) (P : Subgroup G) (x : W) :
    MulAction.stabilizer (P.map sigma) x = ⊥ ↔
      ∀ g : G, g ∈ P → sigma g • x = x → g = 1 := by
  constructor
  · intro h g hg hfix
    have hmem : (⟨sigma g, ⟨g, hg, rfl⟩⟩ : P.map sigma) ∈
        MulAction.stabilizer (P.map sigma) x := hfix
    rw [h] at hmem
    have heq : (⟨sigma g, ⟨g, hg, rfl⟩⟩ : P.map sigma) = 1 := hmem
    apply hfaith
    simpa using congrArg Subtype.val heq
  · intro h
    apply (Subgroup.eq_bot_iff_forall _).mpr
    rintro g hg
    obtain ⟨a, ha, heq⟩ := g.2
    apply Subtype.ext
    change g.1 = 1
    have haone : a = 1 := h a ha (by
      change g.1 • x = x at hg
      rwa [heq])
    rw [← heq, haone, map_one]

/-- **Translated regular orbits over a finite field.** Given a faithful,
completely reducible representation of a finite nilpotent group on a finite
vector space, Sylow subgroups at distinct primes with individual regular
vectors have simultaneous regular translates for arbitrary offsets.

Regularity is written directly in terms of the supplied representation,
so no concrete subgroup presentation or chosen coordinates appear in the
statement. Only the selected primes need individual regular vectors. -/
theorem exists_translated_regular_sylows_finiteField
    {k G V I : Type*} [Field k] [Finite k] [Group G] [Finite G]
    [Group.IsNilpotent G] [AddCommGroup V] [Module k V] [Finite V]
    [Finite I] (rho : Representation k G V)
    (hfaith : Function.Injective rho)
    (hsemi : IsSemisimpleModule k[G] rho.asModule)
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P : ∀ i, Sylow (p i) G)
    (hregular : ∀ i, ∃ w : V, ∀ g : G,
      g ∈ (P i : Subgroup G) → rho g w = w → g = 1)
    (t : I → V) :
    ∃ v : V, ∀ i, ∀ g : G,
      g ∈ (P i : Subgroup G) → rho g (v + t i) = v + t i → g = 1 := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let r := ringChar k
  have : Fact r.Prime := ⟨CharP.prime_ringChar k⟩
  let : Algebra (ZMod r) k := ZMod.algebra k r
  let : Module (ZMod r) V := Module.compHom V (algebraMap (ZMod r) k)
  have hcop : Nat.Coprime r (Nat.card G) :=
    FiniteFieldRepresentation.characteristic_coprime_of_faithful_semisimple
      rho hfaith hsemi
  let rhoPrime : Representation (ZMod r) G V :=
    { toFun := fun g ↦ (rho g).restrictScalars (ZMod r)
      map_one' := by ext; simp
      map_mul' := by intros; ext; simp [Module.End.mul_apply] }
  let d := Module.finrank (ZMod r) V
  let e : V ≃ₗ[ZMod r] (Fin d → ZMod r) := (Module.finBasis (ZMod r) V).equivFun
  let sigma : G →* LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r) :=
    (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom.comp rhoPrime.asGroupHom
  have hsigma (g : G) (v : V) : sigma g • e v = e (rho g v) := by
    exact LinearImprimitivitySystem.congrLinearEquiv_smul e (rhoPrime.asGroupHom g) v
  have hsigmaFaith : Function.Injective sigma := by
    intro g h heq
    apply hfaith
    apply LinearMap.ext
    intro v
    apply e.injective
    rw [← hsigma, ← hsigma, heq]
  let K := sigma.range
  let : Finite K := Finite.of_surjective sigma.rangeRestrict sigma.rangeRestrict_surjective
  let : Group.IsNilpotent K :=
    Group.nilpotent_of_surjective sigma.rangeRestrict sigma.rangeRestrict_surjective
  have hcopK : Nat.Coprime r (Nat.card K) :=
    hcop.of_dvd_right (Subgroup.card_range_dvd sigma)
  have : NeZero (Nat.card K : ZMod r) := ⟨by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact (Fact.out : r.Prime).coprime_iff_not_dvd.mp hcopK⟩
  have hsemiK : IsSemisimpleModule (ZMod r)[K]
      (linearSubgroupRepresentation K).asModule := inferInstance
  let Q : ∀ i, Sylow (p i) K := fun i ↦ by
    have : Fact (p i).Prime := ⟨hp i⟩
    exact (P i).mapSurjective sigma.rangeRestrict_surjective
  have hQimage (i : I) : (Q i : Subgroup K).map K.subtype =
      (P i : Subgroup G).map sigma := by
    change ((P i : Subgroup G).map sigma.rangeRestrict).map K.subtype = _
    rw [Subgroup.map_map]
    rfl
  have hregularQ (i : I) : ∃ w : Fin d → ZMod r,
      MulAction.stabilizer ((Q i : Subgroup K).map K.subtype) w = ⊥ := by
    obtain ⟨w, hw⟩ := hregular i
    refine ⟨e w, ?_⟩
    rw [hQimage, faithful_image_regular_iff sigma hsigmaFaith]
    intro g hg hfix
    apply hw g hg
    apply e.injective
    rwa [hsigma] at hfix
  obtain ⟨v, hv⟩ := nilpotentTranslatedRegularity r d K inferInstance hsemiK
    p hp hinj Q hregularQ (fun i ↦ e (t i))
  refine ⟨e.symm v, fun i g hg hfix ↦ ?_⟩
  have hvi := hv i
  rw [hQimage, faithful_image_regular_iff sigma hsigmaFaith] at hvi
  apply hvi g hg
  have htransport : e (rho g (e.symm v + t i)) = e (e.symm v + t i) :=
    congrArg e hfix
  rw [← hsigma, map_add, e.apply_symm_apply] at htransport
  exact htransport

end LisiSabatini
