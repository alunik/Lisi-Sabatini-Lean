module

public import LisiSabatini.PCore
public import Mathlib.GroupTheory.Nilpotent

/-!
# The Fitting subgroup and nilpotent Sylow generation

Mathlib 4.29.1 does not package the Fitting subgroup of a finite group.  We
define it as the supremum of all normal nilpotent subgroups.  The
three-conjugates programme uses its universal property, the inclusion of
every prime core, and a finite-nilpotent containment principle.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG

/-- The set of normal nilpotent subgroups of `G`. -/
def normalNilpotentSubgroups (G : Type uG) [Group G] : Set (Subgroup G) :=
  {K | K.Normal ∧ Group.IsNilpotent K}

/-- The Fitting subgroup, defined as the supremum of all normal nilpotent
subgroups. -/
def fittingSubgroup (G : Type uG) [Group G] : Subgroup G :=
  sSup (normalNilpotentSubgroups G)

/-- Every normal nilpotent subgroup lies in the Fitting subgroup. -/
theorem normalNilpotent_le_fittingSubgroup
    {G : Type uG} [Group G] {K : Subgroup G}
    (hKn : K.Normal) (hKnil : Group.IsNilpotent K) :
    K ≤ fittingSubgroup G :=
  le_sSup ⟨hKn, hKnil⟩

/-- Every prime core lies in the Fitting subgroup. -/
theorem pCore_le_fittingSubgroup
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] :
    pCore p G ≤ fittingSubgroup G := by
  apply normalNilpotent_le_fittingSubgroup inferInstance
  exact (pCore_isPGroup p G).isNilpotent

/-- A finite nilpotent subgroup lies in `K` if the ambient image of each of
its Sylow subgroups lies in `K`.

The proof constructs the canonical product of the normal Sylow subgroups
and proves that it is bijective by the exact prime-factor cardinality
formula. -/
theorem nilpotentSubgroup_le_of_sylow_map_le
    {G : Type uG} [Group G] [Finite G]
    (L K : Subgroup G) (hLnil : Group.IsNilpotent L)
    (h : ∀ (q : (Nat.card L).primeFactors) (Q : Sylow (q : ℕ) L),
      (Q : Subgroup L).map L.subtype ≤ K) : L ≤ K := by
  classical
  let : Group.IsNilpotent L := hLnil
  let : Fintype L := Fintype.ofFinite L
  let ps := (Nat.card L).primeFactors
  let P : ∀ p : ps, Sylow (p : ℕ) L := fun _ ↦ default
  let : ∀ p : ps, Fintype (P p) := fun _ ↦ Fintype.ofFinite _
  have hn : ∀ {p : ℕ} [Fact p.Prime] (Q : Sylow p L),
      (Q : Subgroup L).Normal := by
    intro p hp Q
    infer_instance
  have hcomm : Pairwise fun p₁ p₂ : ps ↦
      ∀ x y : L, x ∈ P p₁ → y ∈ P p₂ → Commute x y := by
    rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
    have hp₁' : Fact (Nat.Prime p₁) :=
      ⟨Nat.prime_of_mem_primeFactors hp₁⟩
    have hp₂' : Fact (Nat.Prime p₂) :=
      ⟨Nat.prime_of_mem_primeFactors hp₂⟩
    have hne' : p₁ ≠ p₂ := by simpa using hne
    apply Subgroup.commute_of_normal_of_disjoint _ _ (hn (P ⟨p₁, hp₁⟩))
      (hn (P ⟨p₂, hp₂⟩))
    exact IsPGroup.disjoint_of_ne p₁ p₂ hne' _ _
      (P ⟨p₁, hp₁⟩).isPGroup' (P ⟨p₂, hp₂⟩).isPGroup'
  let f : (∀ p : ps, P p) →* L := Subgroup.noncommPiCoprod hcomm
  have hf_bij : Function.Bijective f := by
    apply (Fintype.bijective_iff_injective_and_card f).mpr
    constructor
    · apply Subgroup.injective_noncommPiCoprod_of_iSupIndep
      apply Subgroup.independent_of_coprime_order hcomm
      rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ hne
      have hp₁' : Fact (Nat.Prime p₁) :=
        ⟨Nat.prime_of_mem_primeFactors hp₁⟩
      have hp₂' : Fact (Nat.Prime p₂) :=
        ⟨Nat.prime_of_mem_primeFactors hp₂⟩
      have hne' : p₁ ≠ p₂ := by simpa using hne
      simp only [← Nat.card_eq_fintype_card]
      exact IsPGroup.coprime_card_of_ne p₁ p₂ hne' _ _
        (P ⟨p₁, hp₁⟩).isPGroup' (P ⟨p₂, hp₂⟩).isPGroup'
    · simp only [← Nat.card_eq_fintype_card]
      calc
        Nat.card (∀ p : ps, P p) = ∏ p : ps, Nat.card (P p) := Nat.card_pi
        _ = ∏ p : ps, p.1 ^ (Nat.card L).factorization p.1 := by
          congr 1 with ⟨p, hp⟩
          exact @Sylow.card_eq_multiplicity L _ _ p
            ⟨Nat.prime_of_mem_primeFactors hp⟩ (P ⟨p, hp⟩)
        _ = ∏ p ∈ ps, p ^ (Nat.card L).factorization p :=
          Finset.prod_finset_coe
            (fun p ↦ p ^ (Nat.card L).factorization p) _
        _ = (Nat.card L).factorization.prod (· ^ ·) := rfl
        _ = Nat.card L :=
          Nat.prod_factorization_pow_eq_self Nat.card_pos.ne'
  have htop : (⨆ p : ps, (P p : Subgroup L)) = ⊤ := by
    rw [← Subgroup.noncommPiCoprod_range (hcomm := hcomm)]
    exact f.range_eq_top_of_surjective hf_bij.2
  calc
    L = (⊤ : Subgroup L).map L.subtype := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    _ = (⨆ p : ps, (P p : Subgroup L)).map L.subtype := by rw [htop]
    _ = ⨆ p : ps, (P p : Subgroup L).map L.subtype :=
      Subgroup.map_iSup _ _
    _ ≤ K := iSup_le fun p ↦ h p (P p)

end LisiSabatini
