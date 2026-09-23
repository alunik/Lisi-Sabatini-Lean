module

public import LisiSabatini.PaperTinyAlternating
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.CosetCover
public import Mathlib.GroupTheory.IndexNormal

/-!
# Symmetric groups of degree at most four

The degree-four argument retains the normal Klein four subgroup in every
Sylow 2-intersection. Distinct Sylow 2-subgroups meet exactly in that subgroup;
distinct Sylow 3-subgroups meet trivially. The resulting statements therefore
assert actual prime-core attainment, including the nontrivial small cores.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace LisiSabatini

universe uG uI

/-- Extend an injectively prime-indexed Sylow family to a choice at every
natural number, retaining the original prescribed rows. -/
private theorem exists_sylowFamily_extension
    {G : Type uG} [Group G] {I : Type uI}
    (p : I → ℕ) (hinj : Function.Injective p) (P : ∀ i, Sylow (p i) G) :
    ∃ A : ∀ q : ℕ, Sylow q G, ∀ i, A (p i) = P i := by
  classical
  let A (q : ℕ) : Sylow q G :=
    if h : ∃ i, p i = q then h.choose_spec ▸ P h.choose
    else Classical.choice inferInstance
  refine ⟨A, fun i ↦ ?_⟩
  dsimp only [A]
  split_ifs with h
  · have aux : ∀ (j : I) (hji : p j = p i), hji ▸ P j = P i := by
      intro j hji
      have hji' : j = i := hinj hji
      subst j
      rfl
    exact aux h.choose h.choose_spec
  · exact False.elim (h ⟨i, rfl⟩)

/-- A theorem for two explicit prime rows assembles into the full finite
family statement if all other Sylow subgroups are normal. -/
theorem mixedTwoSylowCoreSynchronization_of_two_exceptional_primes
    {G : Type uG} [Group G] [Finite G] (q r : ℕ)
    (hnormal : ∀ p : ℕ, Nat.Prime p → p ≠ q → p ≠ r →
      ∀ P : Sylow p G, P.Normal)
    (hpair : ∀ (P Q : Sylow q G) (R S : Sylow r G),
      ∃ x : G, mixedSylowInter P Q x = pCore q G ∧
        mixedSylowInter R S x = pCore r G) :
    HasMixedTwoSylowCoreSynchronization.{uG, uI} G := by
  intro I _ p hp hinj P Q
  obtain ⟨A, hA⟩ := exists_sylowFamily_extension p hinj P
  obtain ⟨B, hB⟩ := exists_sylowFamily_extension p hinj Q
  obtain ⟨x, hxq, hxr⟩ := hpair (A q) (B q) (A r) (B r)
  refine ⟨x, fun i ↦ ?_⟩
  by_cases hiq : p i = q
  · subst q
    simpa only [hA i, hB i] using hxq
  · by_cases hir : p i = r
    · subst r
      simpa only [hA i, hB i] using hxr
    · let : Fact (p i).Prime := ⟨hp i⟩
      exact mixedSylowInter_eq_of_normal (P i) (Q i) x
        (hnormal (p i) (hp i) hiq hir (P i))

private theorem card_symmetricGroup_three : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial_succ]

private theorem card_symmetricGroup_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial_succ]

private theorem card_sylow_three_symmetricGroup_three
    (P : Sylow 3 (Equiv.Perm (Fin 3))) : Nat.card P = 3 := by
  rw [Sylow.card_eq_multiplicity, card_symmetricGroup_three]
  rw [show 6 = 3 * 2 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 3 2),
    Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 2)]
  norm_num

private theorem card_sylow_two_symmetricGroup_three
    (P : Sylow 2 (Equiv.Perm (Fin 3))) : Nat.card P = 2 := by
  rw [Sylow.card_eq_multiplicity, card_symmetricGroup_three]
  rw [show 6 = 2 * 3 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 2 3),
    Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
  norm_num

private theorem card_sylow_two_symmetricGroup_four
    (P : Sylow 2 (Equiv.Perm (Fin 4))) : Nat.card P = 8 := by
  rw [Sylow.card_eq_multiplicity, card_symmetricGroup_four]
  rw [show 24 = 2 ^ 3 * 3 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime (2 ^ 3) 3),
    Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply,
    Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 3)]
  norm_num

private theorem card_sylow_three_symmetricGroup_four
    (P : Sylow 3 (Equiv.Perm (Fin 4))) : Nat.card P = 3 := by
  rw [Sylow.card_eq_multiplicity, card_symmetricGroup_four]
  rw [show 24 = 3 * 8 from rfl,
    Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 3 8),
    Nat.prime_three.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 8)]
  norm_num

/-- Distinct Sylow 2-subgroups of S₄ meet in its normal Klein four subgroup,
which is consequently the 2-core. -/
theorem sylow_two_inf_eq_pCore_symmetricGroup_four
    (P Q : Sylow 2 (Equiv.Perm (Fin 4))) (hPQ : P ≠ Q) :
    (P : Subgroup (Equiv.Perm (Fin 4))) ⊓ (Q : Subgroup (Equiv.Perm (Fin 4))) =
      pCore 2 (Equiv.Perm (Fin 4)) := by
  let A := alternatingGroup (Fin 4)
  let K : Subgroup (Equiv.Perm (Fin 4)) := (alternatingGroup.kleinFour (Fin 4)).map A.subtype
  let : (alternatingGroup.kleinFour (Fin 4)).Characteristic :=
    alternatingGroup.characteristic_kleinFour (by simp)
  have hKnormal : K.Normal := inferInstance
  let : K.Normal := hKnormal
  have hKcard : Nat.card K = 4 := by
    rw [Subgroup.card_subtype]
    exact alternatingGroup.kleinFour_card_of_card_eq_four (by simp)
  have hKp : IsPGroup 2 K := IsPGroup.of_card (n := 2) (by simpa using hKcard)
  have hKle : K ≤ (P : Subgroup (Equiv.Perm (Fin 4))) ⊓
      (Q : Subgroup (Equiv.Perm (Fin 4))) :=
    le_inf (hKp.le_sylow_of_normal P) (hKp.le_sylow_of_normal Q)
  have hlt : (P : Subgroup (Equiv.Perm (Fin 4))) ⊓
      (Q : Subgroup (Equiv.Perm (Fin 4))) < (P : Subgroup (Equiv.Perm (Fin 4))) := by
    apply lt_of_le_of_ne inf_le_left
    intro heq
    have hle : (P : Subgroup (Equiv.Perm (Fin 4))) ≤ Q := by
      rw [← heq]
      exact inf_le_right
    exact hPQ (Sylow.ext (P.is_maximal' Q.isPGroup' hle).symm)
  have hcardlt : Nat.card ↥((P : Subgroup (Equiv.Perm (Fin 4))) ⊓
      (Q : Subgroup (Equiv.Perm (Fin 4)))) < 8 := by
    simpa only [card_sylow_two_symmetricGroup_four P] using Subgroup.card_lt_of_lt hlt
  have hcarddvd : 4 ∣ Nat.card ↥((P : Subgroup (Equiv.Perm (Fin 4))) ⊓
      (Q : Subgroup (Equiv.Perm (Fin 4)))) := by
    simpa only [hKcard] using Subgroup.card_dvd_of_le hKle
  have hcardeq : Nat.card ↥((P : Subgroup (Equiv.Perm (Fin 4))) ⊓
      (Q : Subgroup (Equiv.Perm (Fin 4)))) = 4 := by
    have hpos := Nat.card_pos (α := ↥((P : Subgroup (Equiv.Perm (Fin 4))) ⊓
      (Q : Subgroup (Equiv.Perm (Fin 4)))))
    omega
  have heq : K = (P : Subgroup (Equiv.Perm (Fin 4))) ⊓
      (Q : Subgroup (Equiv.Perm (Fin 4))) :=
    Subgroup.eq_of_le_of_card_ge hKle (by rw [hcardeq, hKcard])
  apply le_antisymm
  · rw [← heq]
    exact le_pCore hKp hKnormal
  · exact le_inf (pCore_le_sylow P) (pCore_le_sylow Q)

section TwoSylowRows

variable {G : Type uG} [Group G] [Finite G]

/-- A nonnormal Sylow subgroup has a normalizer of index greater than two:
an index-two normalizer would itself be normal and force Sylow normality. -/
theorem two_lt_sylow_normalizer_index {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hP : ¬ P.Normal) :
    2 < (Subgroup.normalizer (P : Set G)).index := by
  have h0 := (Subgroup.normalizer (P : Set G)).index_ne_zero_of_finite
  have h1 : (Subgroup.normalizer (P : Set G)).index ≠ 1 := by
    intro h
    exact hP (P.normal_of_normalizer_normal (Subgroup.normal_of_index_eq_one h))
  have h2 : (Subgroup.normalizer (P : Set G)).index ≠ 2 := by
    intro h
    exact hP (P.normal_of_normalizer_normal (Subgroup.normal_of_index_eq_two h))
  omega

/-- Every prescribed Sylow row can be moved away from a nonnormal Sylow. -/
theorem exists_sylow_smul_ne_of_not_normal {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) (hP : ¬ P.Normal) :
    ∃ x : G, x • Q ≠ P := by
  classical
  by_contra h
  push Not at h
  have hsame : ∀ R : Sylow p G, R = P := by
    intro R
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G Q R
    exact hx.symm.trans (h x)
  let : Subsingleton (Sylow p G) := ⟨fun R S ↦ (hsame R).trans (hsame S).symm⟩
  exact hP (Sylow.normal_of_subsingleton P)

/-- Two prescribed nonnormal Sylow targets can be avoided simultaneously.
Their bad conjugators lie in two normalizer cosets, each of index above two. -/
theorem exists_two_sylow_smul_ne_of_not_normal {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (P Q : Sylow p G) (R S : Sylow q G)
    (hP : ¬ P.Normal) (hR : ¬ R.Normal) :
    ∃ x : G, x • Q ≠ P ∧ x • S ≠ R := by
  classical
  have hQ : ¬ Q.Normal := by
    intro hn
    let : Unique (Sylow p G) := Sylow.unique_of_normal Q hn
    exact hP (by simpa only [Subsingleton.elim P Q] using hn)
  have hS : ¬ S.Normal := by
    intro hn
    let : Unique (Sylow q G) := Sylow.unique_of_normal S hn
    exact hR (by simpa only [Subsingleton.elim R S] using hn)
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G Q P
  obtain ⟨b, hb⟩ := MulAction.exists_smul_eq G S R
  let H : Bool → Subgroup G := fun i ↦
    if i then Subgroup.normalizer (S : Set G) else Subgroup.normalizer (Q : Set G)
  let g : Bool → G := fun i ↦ if i then b else a
  have hindex : ∀ i : Bool, 2 < (H i).index := by
    intro i
    cases i
    · exact two_lt_sylow_normalizer_index Q hQ
    · exact two_lt_sylow_normalizer_index S hS
  have hmemQ (x : G) (hx : x • Q = P) :
      x ∈ a • (Subgroup.normalizer (Q : Set G) : Set G) := by
    rw [mem_leftCoset_iff]
    apply (Sylow.smul_eq_iff_mem_normalizer (P := Q)).mp
    rw [mul_smul, hx, ← ha]
    simp
  have hmemS (x : G) (hx : x • S = R) :
      x ∈ b • (Subgroup.normalizer (S : Set G) : Set G) := by
    rw [mem_leftCoset_iff]
    apply (Sylow.smul_eq_iff_mem_normalizer (P := S)).mp
    rw [mul_smul, hx, ← hb]
    simp
  by_contra h
  push Not at h
  have hcover : ⋃ i ∈ (Finset.univ : Finset Bool), g i • (H i : Set G) = Set.univ := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hx : x • Q = P
    · exact Set.mem_iUnion.mpr ⟨false, Set.mem_iUnion.mpr
        ⟨Finset.mem_univ false, hmemQ x hx⟩⟩
    · exact Set.mem_iUnion.mpr ⟨true, Set.mem_iUnion.mpr
        ⟨Finset.mem_univ true, hmemS x (h x hx)⟩⟩
  obtain ⟨i, _hi, _hfinite, hcard⟩ :=
    Subgroup.exists_index_le_card_of_leftCoset_cover hcover
  have hlt := hindex i
  have htwo : (Finset.univ : Finset Bool).card = 2 := by decide
  omega

/-- If distinct Sylows meet in the prime core at each of two primes, then
one conjugator attains both independently prescribed mixed intersections. -/
theorem exists_mixedSylowInter_pair_eq_pCore_of_distinct {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (P Q : Sylow p G) (R S : Sylow q G)
    (hp : ∀ A B : Sylow p G, A ≠ B →
      (A : Subgroup G) ⊓ (B : Subgroup G) = pCore p G)
    (hq : ∀ A B : Sylow q G, A ≠ B →
      (A : Subgroup G) ⊓ (B : Subgroup G) = pCore q G) :
    ∃ x : G, mixedSylowInter P Q x = pCore p G ∧
      mixedSylowInter R S x = pCore q G := by
  classical
  by_cases hP : P.Normal
  · by_cases hR : R.Normal
    · exact ⟨1, mixedSylowInter_eq_of_normal P Q 1 hP,
        mixedSylowInter_eq_of_normal R S 1 hR⟩
    · obtain ⟨x, hx⟩ := exists_sylow_smul_ne_of_not_normal R S hR
      exact ⟨x, mixedSylowInter_eq_of_normal P Q x hP, hq R (x • S) hx.symm⟩
  · by_cases hR : R.Normal
    · obtain ⟨x, hx⟩ := exists_sylow_smul_ne_of_not_normal P Q hP
      exact ⟨x, hp P (x • Q) hx.symm, mixedSylowInter_eq_of_normal R S x hR⟩
    · obtain ⟨x, hx, hy⟩ := exists_two_sylow_smul_ne_of_not_normal P Q R S hP hR
      exact ⟨x, hp P (x • Q) hx.symm, hq R (x • S) hy.symm⟩

end TwoSylowRows


/-- Prime-order Sylows meet in the core whenever they are distinct. -/
theorem sylow_inf_eq_pCore_of_prime_card
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) (hcard : Nat.card P = p) (hPQ : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = pCore p G := by
  apply le_antisymm
  · rw [sylow_inf_eq_bot_of_prime_card P Q hcard hPQ]
    exact bot_le
  · exact le_inf (pCore_le_sylow P) (pCore_le_sylow Q)

/-- S₄ satisfies the mixed strong property. Its Sylow-2 intersections
attain the nontrivial Klein four core. -/
theorem mixedTwoSylowCoreSynchronization_symmetricGroup_four :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (Equiv.Perm (Fin 4)) := by
  apply mixedTwoSylowCoreSynchronization_of_two_exceptional_primes 2 3
  · intro p hp hp2 hp3 P
    let : Fact p.Prime := ⟨hp⟩
    apply normal_sylow_of_not_dvd_card P
    rw [card_symmetricGroup_four]
    intro hdvd
    have h24 : p ∣ 2 ^ 3 * 3 := by simpa using hdvd
    rcases hp.dvd_mul.mp h24 with h8 | h3
    · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp (hp.dvd_of_dvd_pow h8)
        |>.resolve_left hp.ne_one)
    · exact hp3 ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left hp.ne_one)
  · intro P Q R S
    apply exists_mixedSylowInter_pair_eq_pCore_of_distinct P Q R S
    · exact sylow_two_inf_eq_pCore_symmetricGroup_four
    · intro A B hAB
      exact sylow_inf_eq_pCore_of_prime_card A B
        (card_sylow_three_symmetricGroup_four A) hAB

/-- S₃ satisfies mixed core synchronization; its normal Sylow 3-subgroup
is retained as the 3-core. -/
theorem mixedTwoSylowCoreSynchronization_symmetricGroup_three :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (Equiv.Perm (Fin 3)) := by
  apply mixedTwoSylowCoreSynchronization_of_one_exceptional_prime 2
  · intro p hp hp2 P
    let : Fact p.Prime := ⟨hp⟩
    by_cases hp3 : p = 3
    · subst p
      have hmul := (P : Subgroup (Equiv.Perm (Fin 3))).index_mul_card
      rw [card_sylow_three_symmetricGroup_three P, card_symmetricGroup_three] at hmul
      exact Subgroup.normal_of_index_eq_two (by omega)
    · apply normal_sylow_of_not_dvd_card P
      rw [card_symmetricGroup_three]
      intro hdvd
      have h6 : p ∣ 2 * 3 := by simpa using hdvd
      rcases hp.dvd_mul.mp h6 with h2 | h3
      · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one)
      · exact hp3 ((Nat.dvd_prime Nat.prime_three).mp h3 |>.resolve_left hp.ne_one)
  · intro P Q
    exact exists_mixedSylowInter_eq_pCore_of_prime_card P Q
      (card_sylow_two_symmetricGroup_three P)

/-- The mixed strong property for every symmetric group of degree at most
four, including the nontrivial small prime cores. -/
theorem mixedTwoSylowCoreSynchronization_symmetricGroup_le_four
    (n : ℕ) (hn : n ≤ 4) :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (Equiv.Perm (Fin n)) := by
  by_cases hn4 : n = 4
  · subst n
    exact mixedTwoSylowCoreSynchronization_symmetricGroup_four
  by_cases hn3 : n = 3
  · subst n
    exact mixedTwoSylowCoreSynchronization_symmetricGroup_three
  have hn2 : n ≤ 2 := by omega
  have hcard : Nat.card (Equiv.Perm (Fin n)) ∣ 2 := by
    rw [Nat.card_perm, Nat.card_fin]
    interval_cases n <;> norm_num [Nat.factorial_succ]
  let : IsCyclic (Equiv.Perm (Fin n)) := isCyclic_of_card_dvd_prime (p := 2) hcard
  exact mixedTwoSylowCoreSynchronization_of_isMulCommutative

/-- The original minimal-intersection statement for Sₙ in degrees at most
four, obtained from exact simultaneous prime-core attainment. -/
theorem hasLisiSabatini_symmetricGroup_le_four (n : ℕ) (hn : n ≤ 4) :
    HasLisiSabatini.{0, uI} (Equiv.Perm (Fin n)) :=
  StrongLisiSabatini.hasLisiSabatini
    (HasMixedTwoSylowCoreSynchronization.strongLisiSabatini
      (mixedTwoSylowCoreSynchronization_symmetricGroup_le_four n hn))

end LisiSabatini
