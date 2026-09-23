module

public import LisiSabatini.Basic

/-!
# The `p`-core of a group

The `p`-core is the largest normal `p`-subgroup.  Mathlib 4.29.1 does not
currently package this subgroup, so we construct it as the supremum of all
normal `p`-subgroups.

The key point in the construction is that normal `p`-subgroups form a
directed family: the supremum of two of them is again a normal `p`-subgroup.
This lets us use `Subgroup.mem_sSup_of_directedOn` rather than reason about
arbitrary words in a subgroup closure.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe u

variable {G : Type u} [Group G]

/-- The set of normal `p`-subgroups of `G`. -/
def normalPSubgroups (p : ℕ) (G : Type u) [Group G] : Set (Subgroup G) :=
  {K | IsPGroup p K ∧ K.Normal}

/-- The `p`-core `O_p(G)`: the supremum of all normal `p`-subgroups of `G`. -/
def pCore (p : ℕ) (G : Type u) [Group G] : Subgroup G :=
  sSup (normalPSubgroups p G)

private theorem normalPSubgroups_nonempty (p : ℕ) (G : Type u) [Group G] :
    (normalPSubgroups p G).Nonempty :=
  ⟨⊥, IsPGroup.of_bot, inferInstance⟩

private theorem normalPSubgroups_directedOn (p : ℕ) (G : Type u) [Group G] :
    DirectedOn (· ≤ ·) (normalPSubgroups p G) := by
  rintro K ⟨hKp, hKn⟩ L ⟨hLp, hLn⟩
  let : K.Normal := hKn
  let : L.Normal := hLn
  refine ⟨K ⊔ L, ⟨?_, inferInstance⟩, le_sup_left, le_sup_right⟩
  exact hKp.to_sup_of_normal_right hLp

/-- Membership in the `p`-core is witnessed by a normal `p`-subgroup. -/
theorem mem_pCore_iff {p : ℕ} {x : G} :
    x ∈ pCore p G ↔ ∃ K : Subgroup G, IsPGroup p K ∧ K.Normal ∧ x ∈ K := by
  rw [pCore, Subgroup.mem_sSup_of_directedOn
    (normalPSubgroups_nonempty p G) (normalPSubgroups_directedOn p G)]
  simp only [normalPSubgroups, Set.mem_ofPred_eq, and_assoc]

/-- Every normal `p`-subgroup is contained in the `p`-core. -/
theorem le_pCore {p : ℕ} {K : Subgroup G} (hKp : IsPGroup p K) (hKn : K.Normal) :
    K ≤ pCore p G := by
  exact le_sSup ⟨hKp, hKn⟩

/-- Mapping a normal `p`-subgroup of a subgroup `K` into its ambient group
lands inside the mapped `p`-core of `K`. -/
theorem map_normalPSubgroup_le_map_pCore
    {L : Type*} [Group L] {K : Subgroup L}
    {p : ℕ} {H : Subgroup K}
    (hHp : IsPGroup p H) (hHn : H.Normal) :
    H.map K.subtype ≤ (pCore p K).map K.subtype :=
  Subgroup.map_mono (le_pCore hHp hHn)

/-- The `p`-core is a `p`-group. -/
theorem pCore_isPGroup (p : ℕ) (G : Type u) [Group G] : IsPGroup p (pCore p G) := by
  intro x
  obtain ⟨K, hKp, _hKn, hxK⟩ := mem_pCore_iff.mp x.2
  obtain ⟨k, hk⟩ := hKp ⟨x.1, hxK⟩
  refine ⟨k, ?_⟩
  rw [Subtype.ext_iff, (pCore p G).coe_pow]
  rw [Subtype.ext_iff, K.coe_pow] at hk
  exact hk

/-- The `p`-core is normal in `G`. -/
instance pCore_normal (p : ℕ) (G : Type u) [Group G] : (pCore p G).Normal where
  conj_mem x hx g := by
    obtain ⟨K, hKp, hKn, hxK⟩ := mem_pCore_iff.mp hx
    exact mem_pCore_iff.mpr ⟨K, hKp, hKn, hKn.conj_mem x hxK g⟩

/-- The `p`-core is characteristic in `G`. -/
instance pCore_characteristic (p : ℕ) (G : Type u) [Group G] :
    (pCore p G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  exact le_pCore ((pCore_isPGroup p G).map (φ : G →* G))
    (Subgroup.Normal.map inferInstance (φ : G →* G) φ.surjective)

/-- The `p`-core is the greatest normal `p`-subgroup. -/
theorem normalPSubgroup_le_pCore {p : ℕ} {K : Subgroup G}
    [K.Normal] (hKp : IsPGroup p K) : K ≤ pCore p G :=
  le_pCore hKp inferInstance

/-- The `p`-core is contained in every Sylow `p`-subgroup.

No finiteness or primality assumption is needed: this follows directly from
the maximality field of `Sylow` and normality of the core.
-/
theorem pCore_le_sylow {p : ℕ} (P : Sylow p G) : pCore p G ≤ (P : Subgroup G) := by
  have hsup : IsPGroup p (((pCore p G) ⊔ (P : Subgroup G)) : Subgroup G) :=
    (pCore_isPGroup p G).to_sup_of_normal_left P.isPGroup'
  have heq : (pCore p G) ⊔ (P : Subgroup G) = (P : Subgroup G) :=
    P.is_maximal' hsup le_sup_right
  exact le_sup_left.trans_eq heq

/-- The `p`-core is a lower bound for every intersection of a Sylow
`p`-subgroup with one of its conjugates. -/
theorem pCore_le_sylowInter {p : ℕ} (P : Sylow p G) (x : G) :
    pCore p G ≤ sylowInter P x :=
  le_inf (pCore_le_sylow P) (pCore_le_sylow (x • P))

end LisiSabatini
