module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.Sylow

/-!
# Minimal normal subgroups used by the odd-order induction
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe u

/-- `N` is a nontrivial normal subgroup of `G` with no proper nontrivial
normal subgroup of the ambient group below it. -/
structure MinimalNormal {G : Type u} [Group G] (N : Subgroup G) : Prop where
  normal : N.Normal
  ne_bot : N ≠ ⊥
  eq_bot_or_eq (K : Subgroup G) :
    K.Normal → K ≤ N → K = ⊥ ∨ K = N

/-- A nontrivial finite group has a minimal normal subgroup. -/
theorem exists_minimalNormal
    {G : Type u} [Group G] [Finite G] [Nontrivial G] :
    ∃ N : Subgroup G, MinimalNormal N := by
  let P : Subgroup G → Prop := fun N ↦ N.Normal ∧ N ≠ ⊥
  obtain ⟨N, hN⟩ := exists_minimal_of_wellFoundedLT P
    (show ∃ N, P N from ⟨⊤, Subgroup.normal_top, top_ne_bot⟩)
  refine ⟨N, hN.1.1, hN.1.2, ?_⟩
  intro K hKnormal hKN
  by_cases hK : K = ⊥
  · exact Or.inl hK
  · exact Or.inr (le_antisymm hKN (hN.2 ⟨hKnormal, hK⟩ hKN))

namespace MinimalNormal

/-- A minimal normal subgroup of a solvable group is abelian. -/
theorem isMulCommutative
    {G : Type u} [Group G] [IsSolvable G]
    {N : Subgroup G} (hN : MinimalNormal N) :
    IsMulCommutative N := by
  letI : N.Normal := hN.normal
  have hcommutator_lt : ⁅N, N⁆ < N :=
    IsSolvable.commutator_lt_of_ne_bot hN.ne_bot
  have hcommutator : ⁅N, N⁆ = ⊥ :=
    (hN.eq_bot_or_eq ⁅N, N⁆ inferInstance
      (Subgroup.commutator_le_self N)).resolve_right
      (ne_of_lt hcommutator_lt)
  exact Subgroup.le_centralizer_iff_isMulCommutative.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommutator)

/-- A finite abelian minimal normal subgroup is a `p`-group for one prime
`p`. -/
theorem exists_prime_isPGroup
    {G : Type u} [Group G] [Finite G]
    {N : Subgroup G} (hN : MinimalNormal N)
    (hcomm : IsMulCommutative N) :
    ∃ p : ℕ, p.Prime ∧ IsPGroup p N := by
  letI : N.Normal := hN.normal
  letI : IsMulCommutative N := hcomm
  let p := (Nat.card N).minFac
  have hcard : 1 < Nat.card N :=
    N.one_lt_card_iff_ne_bot.mpr hN.ne_bot
  have hp : p.Prime := Nat.minFac_prime hcard.ne'
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p N := Classical.choice Sylow.nonempty
  have hPne : (P : Subgroup N) ≠ ⊥ :=
    P.ne_bot_of_dvd_card (Nat.card N).minFac_dvd
  letI : (P : Subgroup N).Characteristic :=
    Sylow.characteristic_of_normal P
      (Subgroup.normal_of_comm (P : Subgroup N))
  letI : ((P : Subgroup N).map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hmap_ne : (P : Subgroup N).map N.subtype ≠ ⊥ := by
    intro h
    apply hPne
    rw [← Subgroup.map_subtype_inj]
    simpa using h
  have hmap_eq : (P : Subgroup N).map N.subtype = N :=
    (hN.eq_bot_or_eq _ inferInstance
      (Subgroup.map_subtype_le _)).resolve_left hmap_ne
  have hPtop : (P : Subgroup N) = ⊤ := by
    rw [← Subgroup.map_subtype_inj, hmap_eq, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  refine ⟨p, hp, P.isPGroup'.of_surjective
    (P : Subgroup N).subtype ?_⟩
  rw [← MonoidHom.range_eq_top, Subgroup.range_subtype, hPtop]

/-- Every element of an abelian minimal normal `p`-subgroup is killed by the
`p`th-power map. -/
theorem pow_prime_eq_one
    {G : Type u} [Group G] [Finite G]
    {N : Subgroup G} (hN : MinimalNormal N)
    (hcomm : IsMulCommutative N) {p : ℕ}
    (hp : p.Prime) (hpg : IsPGroup p N) :
    ∀ x : N, x ^ p = 1 := by
  letI : N.Normal := hN.normal
  letI : IsMulCommutative N := hcomm
  letI : Fact p.Prime := ⟨hp⟩
  let K : Subgroup N := (powMonoidHom p).ker
  have hKchar : K.Characteristic := by
    rw [Subgroup.characteristic_iff_map_eq]
    intro e
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change (e x) ^ p = 1
      change x ^ p = 1 at hx
      simpa using congrArg e hx
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change (e.symm y) ^ p = 1
      change y ^ p = 1 at hy
      simpa using congrArg e.symm hy
  letI : K.Characteristic := hKchar
  letI : (K.map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hp_dvd : p ∣ Nat.card N :=
    hpg.card_eq_or_dvd.resolve_left
      (ne_of_gt (N.one_lt_card_iff_ne_bot.mpr hN.ne_bot))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hp_dvd
  have hxK : x ∈ K := by
    change x ^ p = 1
    rw [← hx, pow_orderOf_eq_one]
  have hKne : K ≠ ⊥ := by
    intro h
    have hxone : x = 1 := by simpa [h] using hxK
    have hone_eq_p : 1 = p := by simpa [hxone] using hx
    exact hp.ne_one hone_eq_p.symm
  have hmap_ne : K.map N.subtype ≠ ⊥ := by
    intro h
    apply hKne
    rw [← Subgroup.map_subtype_inj]
    simpa using h
  have hmap_eq : K.map N.subtype = N :=
    (hN.eq_bot_or_eq _ inferInstance
      (Subgroup.map_subtype_le _)).resolve_left hmap_ne
  have hKtop : K = ⊤ := by
    rw [← Subgroup.map_subtype_inj, hmap_eq, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  intro y
  change y ∈ K
  rw [hKtop]
  trivial

end MinimalNormal

end LisiSabatini
