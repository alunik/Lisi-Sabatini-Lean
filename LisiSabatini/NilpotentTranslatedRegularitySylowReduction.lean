module

public import LisiSabatini.NilpotentTranslatedRegularityRankTwo
public import LisiSabatini.FittingSubgroup

/-!
# Ambient rank-two extraction in a finite nilpotent group

The odd Sylow rank-two extraction lifts to the whole nilpotent group.  The
other Sylow subgroups centralize the chosen Sylow subgroup, so neither
normality nor the centralizer index changes under this lift.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped IsMulCommutative

private theorem eq_top_of_contains_sylows
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    (K : Subgroup G)
    (hK : ∀ p, p.Prime → ∀ P : Sylow p G, (P : Subgroup G) ≤ K) :
    K = ⊤ := by
  apply top_unique
  apply nilpotentSubgroup_le_of_sylow_map_le ⊤ K inferInstance
  intro p P
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map (⊤ : Subgroup G).subtype).exists_le_sylow
  exact hQ.trans (hK p (Nat.prime_of_mem_primeFactors p.2) Q)

/-- A normal Sylow subgroup in a finite nilpotent group generates the
whole group together with its centralizer. -/
theorem sylow_sup_centralizer_eq_top_of_nilpotent
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (P : Subgroup G) ⊔ Subgroup.centralizer (P : Set G) = ⊤ := by
  apply eq_top_of_contains_sylows
  intro q hq Q
  let : Fact q.Prime := ⟨hq⟩
  by_cases hpq : q = p
  · subst q
    let : Unique (Sylow p G) := Sylow.unique_of_normal P inferInstance
    have hQP : Q = P := Subsingleton.elim _ _
    subst Q
    exact le_sup_left
  · apply le_trans ?_ le_sup_right
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.commute_of_normal_of_disjoint
      (Q : Subgroup G) (P : Subgroup G) inferInstance inferInstance
      (IsPGroup.disjoint_of_ne q p hpq _ _ Q.isPGroup' P.isPGroup')
      x y hx hy).symm

/-- A subgroup normal in a Sylow subgroup of a finite nilpotent group
is normal in the whole group. -/
theorem normal_map_sylow_subtype_of_nilpotent
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (E : Subgroup P) (hE : E.Normal) :
    (E.map (P : Subgroup G).subtype).Normal := by
  let B := E.map (P : Subgroup G).subtype
  have hBP : B ≤ (P : Subgroup G) := Subgroup.map_subtype_le E
  have hBN : (B.subgroupOf (P : Subgroup G)).Normal := by
    change (Subgroup.comap (P : Subgroup G).subtype
      (E.map (P : Subgroup G).subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective (P : Subgroup G).subtype_injective]
    exact hE
  have hPN : (P : Subgroup G) ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp hBN
  have hCN : Subgroup.centralizer (P : Set G) ≤ Subgroup.normalizer (B : Set G) :=
    (Subgroup.centralizer_le hBP).trans (Subgroup.centralizer_le_normalizer _)
  apply Subgroup.normalizer_eq_top_iff.mp
  apply top_unique
  rw [← sylow_sup_centralizer_eq_top_of_nilpotent P]
  exact sup_le hPN hCN

/-- The center of a Sylow subgroup of a finite nilpotent group lies in
the ambient center. -/
theorem map_sylow_center_le_center_of_nilpotent
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) :
    (Subgroup.center P).map (P : Subgroup G).subtype ≤ Subgroup.center G := by
  rintro z ⟨a, ha, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ (P : Subgroup G) ⊔ Subgroup.centralizer (P : Set G) := by
    rw [sylow_sup_centralizer_eq_top_of_nilpotent P]
    trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  rw [← hxy]
  have hxa : x * (a : G) = (a : G) * x :=
    congrArg Subtype.val (Subgroup.mem_center_iff.mp ha (⟨x, hx⟩ : P))
  have hya : y * (a : G) = (a : G) * y :=
    (Subgroup.mem_centralizer_iff.mp hy a a.2).symm
  exact (Commute.mul_left hxa hya).eq

/-- Cyclicity of the ambient center passes to every Sylow center in a
finite nilpotent group. -/
theorem isCyclic_sylow_center_of_nilpotent
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hCenter : IsCyclic (Subgroup.center G)) :
    IsCyclic (Subgroup.center P) := by
  let : IsCyclic (Subgroup.center G) := hCenter
  have himage : IsCyclic ((Subgroup.center P).map (P : Subgroup G).subtype) :=
    Subgroup.isCyclic_of_le (map_sylow_center_le_center_of_nilpotent P)
  let e := (Subgroup.center P).equivMapOfInjective
    (P : Subgroup G).subtype (P : Subgroup G).subtype_injective
  exact e.isCyclic.mpr himage

/-- Centralizer index is unchanged when a normal subgroup of a Sylow
subgroup is viewed inside the whole nilpotent group. -/
theorem centralizer_index_map_sylow_subtype_of_nilpotent
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (E : Subgroup P) (hE : E.Normal) :
    (Subgroup.centralizer (E.map (P : Subgroup G).subtype : Set G)).index =
      (Subgroup.centralizer (E : Set P)).index := by
  let B := E.map (P : Subgroup G).subtype
  let C := Subgroup.centralizer (B : Set G)
  have hBP : B ≤ (P : Subgroup G) := Subgroup.map_subtype_le E
  let : B.Normal := normal_map_sylow_subtype_of_nilpotent P E hE
  have hsup : (P : Subgroup G) ⊔ C = ⊤ := by
    apply top_unique
    rw [← sylow_sup_centralizer_eq_top_of_nilpotent P]
    exact sup_le_sup_left (Subgroup.centralizer_le hBP) _
  have hC : C.subgroupOf (P : Subgroup G) = Subgroup.centralizer (E : Set P) := by
    ext x
    change (x : G) ∈ Subgroup.centralizer (B : Set G) ↔
      x ∈ Subgroup.centralizer (E : Set P)
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h y hy
      apply Subtype.ext
      exact h y (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
    · intro h y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
      exact congrArg Subtype.val (h a ha)
  change C.index = _
  calc
    C.index = C.relIndex (⊤ : Subgroup G) := (Subgroup.relIndex_top_right C).symm
    _ = C.relIndex ((P : Subgroup G) ⊔ C) := by rw [hsup]
    _ = C.relIndex (P : Subgroup G) := Subgroup.relIndex_sup_right _ _
    _ = (Subgroup.centralizer (E : Set P)).index := congrArg Subgroup.index hC

/-- A noncyclic odd Sylow subgroup of a finite nilpotent group with
cyclic center supplies the normal elementary abelian subgroup and the
ambient prime-index centralizer required by Clifford induction. -/
theorem exists_normal_primeSquare_of_noncyclic_odd_sylow
    {G : Type*} [Group G] [Finite G] [Group.IsNilpotent G]
    {p : ℕ} (hp : p.Prime) (hpOdd : Odd p) (P : Sylow p G)
    (hP : ¬ IsCyclic P) (hCenter : IsCyclic (Subgroup.center G)) :
    ∃ B : Subgroup G,
      B.Normal ∧ B ≤ (P : Subgroup G) ∧ Nat.card B = p ^ 2 ∧
        IsMulCommutative B ∧ (∀ x : B, x ^ p = 1) ∧ ¬ IsCyclic B ∧
          (Subgroup.centralizer (B : Set G)).index = p := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hE, hEcard, hEcomm, hEpow, hEnoncyclic⟩ :=
    exists_normal_primeSquare_of_odd_of_not_isCyclic hp hpOdd P.isPGroup' hP
  let B := E.map (P : Subgroup G).subtype
  let e : E ≃* B := E.equivMapOfInjective
    (P : Subgroup G).subtype (P : Subgroup G).subtype_injective
  have hBcard : Nat.card B = p ^ 2 := (Nat.card_congr e.toEquiv).symm.trans hEcard
  have hBcomm : IsMulCommutative B :=
    Function.Surjective.isMulCommutative e.surjective hEcomm
  refine ⟨B, normal_map_sylow_subtype_of_nilpotent P E hE,
    Subgroup.map_subtype_le E, hBcard, hBcomm, ?_, ?_, ?_⟩
  · intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_pow, hEpow, map_one]
  · intro hBcyclic
    exact hEnoncyclic (e.isCyclic.mpr hBcyclic)
  · rw [centralizer_index_map_sylow_subtype_of_nilpotent P E hE]
    exact centralizer_index_eq_prime_of_normal_primeSquare_noncyclic
      hp P.isPGroup' (isCyclic_sylow_center_of_nilpotent P hCenter)
      E hE hEcard hEnoncyclic

end LisiSabatini
