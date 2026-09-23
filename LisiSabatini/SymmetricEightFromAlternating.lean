module

public import LisiSabatini.A8DoubleCosetCompletion
public import LisiSabatini.SymmetricEightDoubleCoset
public import LisiSabatini.SymmetricIndexTwoMinimality

/-!
# S8 from the alternating-group result

If a trivial binary Sylow pair exists, its good double coset and the
degree-eight odd-prime budgets give simultaneous trivial intersections.
Otherwise the alternating-group result makes every intersection have
order at most two, which gives inclusion-minimality in every prime row.
-/

@[expose] public section

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini

private theorem sylowInter_cast_prime
    {G : Type*} [Group G] {p q : ℕ} (h : p = q) (P : Sylow p G) (x : G) :
    sylowInter (h ▸ P) x = sylowInter P x := by
  subst q
  rfl

private theorem sylowInter_inf_subgroup_eq_bot_of_comap_le
    {G : Type*} [Group G] (H : Subgroup G) {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : (P : Subgroup G).comap H.subtype ≤ Q) (x : H)
    (hx : sylowInter Q x = ⊥) : sylowInter P (x : G) ⊓ H = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro y hy
  let yH : H := ⟨y, hy.2⟩
  have hyQ : yH ∈ sylowInter Q x := by
    refine ⟨hPQ hy.1.1, ?_⟩
    have hyconj : y ∈ (P : Subgroup G).map (MulAut.conj (x : G)).toMonoidHom := hy.1.2
    obtain ⟨z, hzP, hzy⟩ := hyconj
    have hzx : z = (x : G)⁻¹ * y * (x : G) := by
      rw [← hzy]
      change z = (x : G)⁻¹ * ((x : G) * z * (x : G)⁻¹) * (x : G)
      group
    have hzH : z ∈ H := by
      rw [hzx]
      exact H.mul_mem (H.mul_mem (H.inv_mem x.property) hy.2) x.property
    change yH ∈ (Q : Subgroup H).map (MulAut.conj x).toMonoidHom
    exact ⟨⟨z, hzH⟩, hPQ hzP, Subtype.ext hzy⟩
  have hyone : yH = 1 := by simpa only [hx, Subgroup.mem_bot] using hyQ
  exact congrArg Subtype.val hyone

/-- Extending each restricted row to an alternating Sylow suffices: exact
normal-subgroup Sylow restriction is unnecessary. -/
theorem exists_common_symmetricEight_inter_card_le_two_of_A8_pair
    (R : Sylow 2 (alternatingGroup (Fin 8)))
    (hcardR : Nat.card R = 64) (hR : ∃ g, sylowInter R g = ⊥)
    {I : Type*} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P : ∀ i, Sylow (p i) (Equiv.Perm (Fin 8))) :
    ∃ x : Equiv.Perm (Fin 8), ∀ i, Nat.card (sylowInter (P i) x) ≤ 2 := by
  classical
  let H := alternatingGroup (Fin 8)
  have hQ : ∀ i, ∃ Q : Sylow (p i) H, (P i : Subgroup _).comap H.subtype ≤ Q := by
    intro i
    exact ((P i).isPGroup'.comap_subtype).exists_le_sylow
  choose Q hPQ using hQ
  obtain ⟨x, hx⟩ := exists_common_mixedSylowInter_bot_A8_of_one_pair
    R hcardR hR p hp hinj Q Q
  refine ⟨x, fun i ↦ ?_⟩
  have hindex : H.index ≤ 2 := by
    change (alternatingGroup (Fin 8)).index ≤ 2
    rw [alternatingGroup.index_eq_two]
  apply sylowInter_card_le_two_of_inf_eq_bot H hindex (P i) (x : Equiv.Perm (Fin 8))
  apply sylowInter_inf_subgroup_eq_bot_of_comap_le H (P i) (Q i) (hPQ i) x
  simpa only [sylowInter, mixedSylowInter] using hx i

private theorem sylowInter_eq_bot_of_card_le_two_of_ne_two
    {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (P : Sylow p G) (x : G) (hcard : Nat.card (sylowInter P x) ≤ 2) :
    sylowInter P x = ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  have hpg : IsPGroup p (sylowInter P x) := P.isPGroup'.to_inf_left
  rcases hpg.card_eq_or_dvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · have hle : p ≤ Nat.card (sylowInter P x) := Nat.le_of_dvd (Nat.card_pos) h
    have htwo := hp.two_le
    exact (hne (by omega)).elim

private theorem symmetricEight_bad_probability_le_row_budget
    (R : Sylow 2 (Equiv.Perm (Fin 8))) (hR : ∃ g, sylowInter R g = ⊥)
    (p : ℕ) (hp : p.Prime) (P Q : Sylow p (Equiv.Perm (Fin 8))) :
    ((mixedSylowPairBadConjugators P Q).ncard : ℝ) /
        Nat.card (Equiv.Perm (Fin 8)) ≤
      if p = 2 then (251 : ℝ) / 315 else alternatingSylowProfileQuadraticCost 8 p := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases htwo : p = 2
  · subst p
    rw [ite_eq_left rfl]
    have h := bad_probability_le_of_one_trivial_pair R hR P Q
    have hG : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
      rw [natCard_perm_fin]
      norm_num [Nat.factorial]
    have hRcard : Nat.card R = 128 := by
      rw [R.card_eq_multiplicity, hG]
      decide +kernel
    rw [hRcard, hG] at h
    rw [hG]
    norm_num at h ⊢
    linarith
  · rw [ite_eq_right htwo]
    have hprofile : symmetricSylowProfileQuadraticCost 8 p =
        alternatingSylowProfileQuadraticCost 8 p := by
      simp only [alternatingSylowProfileQuadraticCost, ite_eq_right htwo]
    rw [← hprofile, ← normalizedSameRowSylowQuadraticCost_perm_eq_profile hp P]
    unfold normalizedSameRowSylowQuadraticCost
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h := ncard_mixedSylowPairBadConjugators_le_quadraticClass_sum P Q
    simp_rw [mixedSylowPairQuadraticClassTerm_eq_sameRow P Q P] at h
    exact_mod_cast h

/-- The branch with a trivial binary pair even gives the mixed trivial
intersection conclusion. Its binary bound is stronger than the A8 budget. -/
theorem exists_common_mixedSylowInter_bot_symmetricEight_of_one_pair
    (R : Sylow 2 (Equiv.Perm (Fin 8))) (hR : ∃ g, sylowInter R g = ⊥)
    {I : Type*} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P Q : ∀ i, Sylow (p i) (Equiv.Perm (Fin 8))) :
    ∃ x : Equiv.Perm (Fin 8), ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  let := Fintype.ofFinite I
  apply exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt p P Q
  have hsum :
      (∑ i, ((mixedSylowPairBadConjugators (P i) (Q i)).ncard : ℝ) /
        Nat.card (Equiv.Perm (Fin 8))) < 1 :=
    (Finset.sum_le_sum (fun i _ ↦
      symmetricEight_bad_probability_le_row_budget R hR (p i) (hp i) (P i) (Q i))).trans_lt
      (sum_a8_double_coset_row_budget_lt_one p hp hinj)
  have htotal :
      ((∑ i, (mixedSylowPairBadConjugators (P i) (Q i)).ncard : ℕ) : ℝ) /
        Nat.card (Equiv.Perm (Fin 8)) < 1 := by
    simpa only [Nat.cast_sum, div_eq_mul_inv, Finset.sum_mul] using hsum
  have hpos : (0 : ℝ) < Nat.card (Equiv.Perm (Fin 8)) := by
    exact_mod_cast (Nat.card_pos (α := Equiv.Perm (Fin 8)))
  exact_mod_cast (div_lt_one hpos).mp htotal

/-- The original S8 conclusion follows from the A8 mixed result in both
binary cases, without a census proving that binary intersections are nontrivial. -/
theorem hasLisiSabatini_symmetricEight_of_A8_one_pair
    (R : Sylow 2 (alternatingGroup (Fin 8)))
    (hcardR : Nat.card R = 64) (hR : ∃ g, sylowInter R g = ⊥) :
    HasLisiSabatini (Equiv.Perm (Fin 8)) := by
  classical
  intro I _ p hp hinj P
  by_cases hbinary : ∃ S : Sylow 2 (Equiv.Perm (Fin 8)), ∃ g, sylowInter S g = ⊥
  · obtain ⟨S, hS⟩ := hbinary
    obtain ⟨x, hx⟩ := exists_common_mixedSylowInter_bot_symmetricEight_of_one_pair
      S hS p hp hinj P P
    refine ⟨x, fun i y _hy ↦ ?_⟩
    have hbot : sylowInter (P i) x = ⊥ := by
      simpa only [sylowInter, mixedSylowInter] using hx i
    rw [hbot]
    exact bot_le
  · obtain ⟨x, hx⟩ := exists_common_symmetricEight_inter_card_le_two_of_A8_pair
      R hcardR hR p hp hinj P
    refine ⟨x, fun i ↦ ?_⟩
    by_cases htwo : p i = 2
    · have hnon : ∀ y, sylowInter (P i) y ≠ ⊥ := by
        intro y hy
        exact hbinary ⟨htwo ▸ P i, y, by rw [sylowInter_cast_prime]; exact hy⟩
      apply isMinimalSylowInter_of_card_two (P i) hnon
      have hnot : ¬ Nat.card (sylowInter (P i) x) ≤ 1 := by
        intro hsmall
        exact hnon x (Subgroup.eq_bot_of_card_le _ hsmall)
      have hbound := hx i
      omega
    · have hbot := sylowInter_eq_bot_of_card_le_two_of_ne_two (hp i) htwo (P i) x (hx i)
      intro y _hy
      rw [hbot]
      exact bot_le

end LisiSabatini
