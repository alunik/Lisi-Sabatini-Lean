module

public import LisiSabatini.SymmetricSmallDegreeMatchingSylow
public import LisiSabatini.AlternatingSylowWreathSupport
public import LisiSabatini.AlternatingSylowCoefficientBridge
public import Mathlib.Data.Finset.Powerset

/-! Exact cycle-type rows for a perfect matching flip subgroup. -/

@[expose] public section

noncomputable section

namespace LisiSabatini

open Equiv

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Flip precisely the edges indexed by a finite set. -/
def pairFlip (s : Finset α) : Perm (α × Bool) where
  toFun x := (x.1, if x.1 ∈ s then !x.2 else x.2)
  invFun x := (x.1, if x.1 ∈ s then !x.2 else x.2)
  left_inv x := by by_cases h : x.1 ∈ s <;> simp [h]
  right_inv x := by by_cases h : x.1 ∈ s <;> simp [h]

omit [Fintype α] in
@[simp]
theorem pairFlip_apply (s : Finset α) (a : α) (b : Bool) :
    pairFlip s (a, b) = (a, if a ∈ s then !b else b) := rfl

/-- The full perfect matching on pairs. -/
def pairMatching : Perm (α × Bool) := pairFlip Finset.univ

@[simp]
theorem pairMatching_apply (a : α) (b : Bool) :
    pairMatching (a, b) = (a, !b) := by simp [pairMatching]

theorem pairMatching_involutive : Function.Involutive (pairMatching (α := α)) := by
  rintro ⟨a, b⟩
  simp

theorem pairMatching_fixedPointFree (x : α × Bool) : pairMatching x ≠ x := by
  rcases x with ⟨a, b⟩
  cases b <;> simp

/-- The actual elementary abelian subgroup of independent pair flips. -/
def pairFlipSubgroup : Subgroup (Perm (α × Bool)) :=
  matchingFlipSubgroup pairMatching pairMatching_involutive

theorem pairFlip_mem (s : Finset α) : pairFlip s ∈ pairFlipSubgroup := by
  rintro ⟨a, b⟩
  by_cases h : a ∈ s
  · right; simp [h]
  · left; simp [h]

omit [Fintype α] in
theorem pairFlip_injective : Function.Injective (pairFlip (α := α)) := by
  intro s t h
  ext a
  have ha := congrArg (fun g : Perm (α × Bool) ↦ (g (a, false)).2) h
  simp only [pairFlip_apply] at ha
  by_cases hs : a ∈ s <;> by_cases ht : a ∈ t <;> simp_all


/-- Every element is uniquely determined by the set of flipped pairs. -/
theorem exists_pairFlip_of_mem {g : Perm (α × Bool)} (hg : g ∈ pairFlipSubgroup) :
    ∃ s : Finset α, pairFlip s = g := by
  classical
  let s := Finset.univ.filter fun a ↦ g (a, false) = (a, true)
  refine ⟨s, ?_⟩
  apply Equiv.ext
  rintro ⟨a, b⟩
  have hgf := hg (a, false)
  have hgt := hg (a, true)
  simp only [pairMatching_apply, Bool.not_false, Bool.not_true] at hgf hgt
  rcases hgf with hgf | hgf
  · have hs : a ∉ s := by simp [s, hgf]
    have hgt' : g (a, true) = (a, true) := by
      rcases hgt with h | h
      · exact h
      · have heq := g.injective (h.trans hgf.symm)
        simp at heq
    cases b <;> simp [hs, hgf, hgt']
  · have hs : a ∈ s := by simp [s, hgf]
    have hgt' : g (a, true) = (a, false) := by
      have hinv := involutive_of_mem_matchingFlipSubgroup
        pairMatching pairMatching_involutive hg (a, false)
      simpa only [hgf] using hinv
    cases b <;> simp [hs, hgf, hgt']

@[simp]
theorem support_pairFlip (s : Finset α) :
    (pairFlip s).support = s ×ˢ Finset.univ := by
  ext x
  rcases x with ⟨a, b⟩
  cases b <;> by_cases h : a ∈ s <;> simp [Perm.mem_support, h]

@[simp]
theorem card_support_pairFlip (s : Finset α) :
    (pairFlip s).support.card = s.card * 2 := by
  simp

@[simp]
theorem cycleType_pairFlip (s : Finset α) :
    (pairFlip s).cycleType = Multiset.replicate s.card 2 := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : pairFlip s ^ 2 = 1 :=
    sq_eq_one_of_mem_matchingFlipSubgroup pairMatching pairMatching_involutive
      (pairFlip_mem s)
  rw [Perm.cycleType_of_pow_prime_eq_one hp,
    cycleType_card_eq_card_support_div_prime _ hp, card_support_pairFlip,
    Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- The exact conjugacy-class row of the matching subgroup. -/
theorem ncard_pairFlipSubgroup_cycleType (j : ℕ) :
    {g : Perm (α × Bool) | g ∈ pairFlipSubgroup ∧
      g.cycleType = Multiset.replicate j 2}.ncard =
        Nat.choose (Fintype.card α) j := by
  classical
  have heq : {g : Perm (α × Bool) | g ∈ pairFlipSubgroup ∧
      g.cycleType = Multiset.replicate j 2} =
      pairFlip '' (↑((Finset.univ : Finset α).powersetCard j) : Set (Finset α)) := by
    ext g
    constructor
    · rintro ⟨hg, hcycle⟩
      obtain ⟨s, rfl⟩ := exists_pairFlip_of_mem hg
      have hs : s.card = j := by
        simpa only [cycleType_pairFlip, Multiset.card_replicate] using
          congrArg Multiset.card hcycle
      exact ⟨s, by simp [Finset.mem_powersetCard, hs], rfl⟩
    · rintro ⟨s, hs, rfl⟩
      have hcard : s.card = j := (Finset.mem_powersetCard.mp hs).2
      exact ⟨pairFlip_mem s, by simp [hcard]⟩
  rw [heq, Set.ncard_image_of_injective _ pairFlip_injective]
  simp

section Transport

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Transport a perfect matching to any equinumerous point set. -/
def pairMatchingOn (e : (α × Bool) ≃ β) : Perm β := e.permCongr pairMatching

omit [Fintype β] [DecidableEq β] in
theorem pairMatchingOn_involutive (e : (α × Bool) ≃ β) :
    Function.Involutive (pairMatchingOn e) := by
  intro b
  simp only [pairMatchingOn, Equiv.permCongr_apply, e.symm_apply_apply]
  rw [pairMatching_involutive, e.apply_symm_apply]

omit [Fintype β] [DecidableEq β] in
theorem pairMatchingOn_fixedPointFree (e : (α × Bool) ≃ β) (b : β) :
    pairMatchingOn e b ≠ b := by
  intro h
  apply pairMatching_fixedPointFree (e.symm b)
  simpa only [pairMatchingOn, Equiv.permCongr_apply, e.symm_apply_apply] using
    congrArg e.symm h

/-- The actual matching flip subgroup on the transported point set. -/
def pairFlipSubgroupOn (e : (α × Bool) ≃ β) : Subgroup (Perm β) :=
  matchingFlipSubgroup (pairMatchingOn e) (pairMatchingOn_involutive e)

omit [Fintype β] [DecidableEq β] in
theorem pairFlipSubgroupOn_mem_iff (e : (α × Bool) ≃ β) (g : Perm (α × Bool)) :
    e.permCongr g ∈ pairFlipSubgroupOn e ↔ g ∈ pairFlipSubgroup := by
  constructor
  · intro h x
    have hx := h (e x)
    simp only [pairMatchingOn, Equiv.permCongr_apply, e.symm_apply_apply] at hx
    exact hx.imp (fun h ↦ e.injective h) (fun h ↦ e.injective h)
  · intro h b
    have hb := h (e.symm b)
    change e (g (e.symm b)) = b ∨ e (g (e.symm b)) = e (pairMatching (e.symm b))
    exact hb.imp (fun h ↦ (congrArg e h).trans (e.apply_symm_apply b)) (congrArg e)

omit [Fintype α] in
@[simp]
theorem cycleType_permCongr_pairFlip [Finite α]
    (e : (α × Bool) ≃ β) (s : Finset α) :
    (e.permCongr (pairFlip s)).cycleType = Multiset.replicate s.card 2 := by
  let : Fintype α := Fintype.ofFinite α
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : pairFlip s ^ 2 = 1 :=
    sq_eq_one_of_mem_matchingFlipSubgroup pairMatching pairMatching_involutive
      (pairFlip_mem s)
  have hp' : e.permCongr (pairFlip s) ^ 2 = 1 := by
    change e.permCongrHom (pairFlip s) ^ 2 = 1
    rw [← map_pow, hp, map_one]
  rw [Perm.cycleType_of_pow_prime_eq_one hp',
    cycleType_card_eq_card_support_div_prime _ hp', card_support_permCongr,
    card_support_pairFlip, Nat.mul_div_cancel _ (by decide : 0 < 2)]

/-- Transport preserves the exact binomial cycle-type row. -/
theorem ncard_pairFlipSubgroupOn_cycleType (e : (α × Bool) ≃ β) (j : ℕ) :
    {g : Perm β | g ∈ pairFlipSubgroupOn e ∧
      g.cycleType = Multiset.replicate j 2}.ncard =
        Nat.choose (Fintype.card α) j := by
  classical
  have heq : {g : Perm β | g ∈ pairFlipSubgroupOn e ∧
      g.cycleType = Multiset.replicate j 2} =
      (fun s ↦ e.permCongr (pairFlip s)) ''
        (↑((Finset.univ : Finset α).powersetCard j) : Set (Finset α)) := by
    ext g
    constructor
    · rintro ⟨hg, hcycle⟩
      obtain ⟨f, rfl⟩ := e.permCongr.surjective g
      obtain ⟨s, rfl⟩ := exists_pairFlip_of_mem
        ((pairFlipSubgroupOn_mem_iff e f).mp hg)
      have hs : s.card = j := by
        simpa only [cycleType_permCongr_pairFlip, Multiset.card_replicate] using
          congrArg Multiset.card hcycle
      exact ⟨s, by simp [Finset.mem_powersetCard, hs], rfl⟩
    · rintro ⟨s, hs, rfl⟩
      have hcard : s.card = j := (Finset.mem_powersetCard.mp hs).2
      exact ⟨(pairFlipSubgroupOn_mem_iff e _).mpr (pairFlip_mem s), by simp [hcard]⟩
  have hinj : Function.Injective (fun s : Finset α ↦ e.permCongr (pairFlip s)) :=
    e.permCongr.injective.comp pairFlip_injective
  rw [heq, Set.ncard_image_of_injective _ hinj]
  simp

/-- The exact row of the conjugacy class of any permutation of type `2^j`. -/
theorem ncard_conjClass_inter_pairFlipSubgroupOn
    (e : (α × Bool) ≃ β) (σ : Perm β) (j : ℕ)
    (hσ : σ.cycleType = Multiset.replicate j 2) :
    ((ConjClasses.mk σ).carrier ∩ (pairFlipSubgroupOn e : Set (Perm β))).ncard =
      Nat.choose (Fintype.card α) j := by
  have heq : (ConjClasses.mk σ).carrier ∩ (pairFlipSubgroupOn e : Set (Perm β)) =
      {g : Perm β | g ∈ pairFlipSubgroupOn e ∧
        g.cycleType = Multiset.replicate j 2} := by
    ext g
    simp only [Set.mem_inter_iff, ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj, Perm.isConj_iff_cycleType_eq, hσ,
      Set.mem_ofPred_eq, and_comm]
    rfl
  rw [heq, ncard_pairFlipSubgroupOn_cycleType]

end Transport

/-- A concrete identification of paired points with an even symmetric degree. -/
def pairPointsEquivFin (m : ℕ) : (Fin m × Bool) ≃ Fin (2 * m) :=
  Fintype.equivOfCardEq (by simp [Nat.mul_comm])

/-- Perfect matching on `2m` letters. -/
def finPairMatching (m : ℕ) : Perm (Fin (2 * m)) :=
  pairMatchingOn (pairPointsEquivFin m)

def finPairFlipSubgroup (m : ℕ) : Subgroup (Perm (Fin (2 * m))) :=
  pairFlipSubgroupOn (pairPointsEquivFin m)

theorem finPairMatching_involutive (m : ℕ) : Function.Involutive (finPairMatching m) :=
  pairMatchingOn_involutive _

theorem finPairMatching_fixedPointFree (m : ℕ) (x : Fin (2 * m)) :
    finPairMatching m x ≠ x := pairMatchingOn_fixedPointFree _ x

theorem ncard_finPairFlipSubgroup_cycleType (m j : ℕ) :
    {g : Perm (Fin (2 * m)) | g ∈ finPairFlipSubgroup m ∧
      g.cycleType = Multiset.replicate j 2}.ncard = Nat.choose m j := by
  simpa only [finPairFlipSubgroup, Fintype.card_fin] using
    ncard_pairFlipSubgroupOn_cycleType (pairPointsEquivFin m) j

theorem ncard_conjClass_inter_finPairFlipSubgroup (m j : ℕ)
    (σ : Perm (Fin (2 * m))) (hσ : σ.cycleType = Multiset.replicate j 2) :
    ((ConjClasses.mk σ).carrier ∩ (finPairFlipSubgroup m : Set _)).ncard =
      Nat.choose m j := by
  simpa only [finPairFlipSubgroup, Fintype.card_fin] using
    ncard_conjClass_inter_pairFlipSubgroupOn (pairPointsEquivFin m) σ j hσ

theorem exists_sylow_two_ge_finPairFlipSubgroup (m : ℕ) :
    ∃ P : Sylow 2 (Perm (Fin (2 * m))), finPairFlipSubgroup m ≤ P :=
  exists_sylow_two_ge_matchingFlipSubgroup
    (pairMatchingOn (pairPointsEquivFin m)) (pairMatchingOn_involutive _)

/-- The transported subgroup is definitionally the matching flip subgroup. -/
theorem finPairFlipSubgroup_eq_matchingFlipSubgroup (m : ℕ) :
    finPairFlipSubgroup m =
      matchingFlipSubgroup (finPairMatching m) (finPairMatching_involutive m) := rfl

/-- The matching subgroup contains exactly `m` transpositions. -/
theorem ncard_finPairFlipSubgroup_isSwap (m : ℕ) :
    {g : Perm (Fin (2 * m)) | g ∈ finPairFlipSubgroup m ∧ g.IsSwap}.ncard = m := by
  have heq : {g : Perm (Fin (2 * m)) | g ∈ finPairFlipSubgroup m ∧ g.IsSwap} =
      {g : Perm (Fin (2 * m)) | g ∈ finPairFlipSubgroup m ∧
        g.cycleType = Multiset.replicate 1 2} := by
    ext g
    simp only [Set.mem_ofPred_eq, Perm.isSwap_iff_cycleType, Multiset.replicate_one]
  rw [heq, ncard_finPairFlipSubgroup_cycleType, Nat.choose_one_right]

/-- Exact row cardinal in the canonical cycle-class indexing. -/
theorem ncard_primeCycleTypeClass_inter_finPairFlipSubgroup (m j : ℕ) (hj : j ≤ m) :
    ((primeCycleTypeClass (2 * m) 2 j).carrier ∩
      (finPairFlipSubgroup m : Set _)).ncard = Nat.choose m j := by
  rw [carrier_primeCycleTypeClass
    (isValidPrimeCycleType_of_prime Nat.prime_two (Nat.mul_le_mul_left 2 hj))]
  have heq : {g : Perm (Fin (2 * m)) | g.cycleType = Multiset.replicate j 2} ∩
      (finPairFlipSubgroup m : Set _) =
      {g : Perm (Fin (2 * m)) | g ∈ finPairFlipSubgroup m ∧
        g.cycleType = Multiset.replicate j 2} := by
    ext g
    exact and_comm
  rw [heq, ncard_finPairFlipSubgroup_cycleType]

/-- Every Sylow extending the matching has exactly its transpositions. -/
theorem isSwap_mem_sylow_two_iff_mem_finPairFlipSubgroup (m : ℕ)
    (P : Sylow 2 (Perm (Fin (2 * m)))) (hP : finPairFlipSubgroup m ≤ P)
    {g : Perm (Fin (2 * m))} (hg : g.IsSwap) :
    g ∈ P ↔ g ∈ finPairFlipSubgroup m := by
  exact isSwap_mem_sylow_two_iff_mem_matchingFlipSubgroup
    (finPairMatching m) (finPairMatching_involutive m)
    (finPairMatching_fixedPointFree m) P hP hg

end LisiSabatini
