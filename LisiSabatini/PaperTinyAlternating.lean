module

public import LisiSabatini.ThreeConjugatesSynchronization
public import Mathlib.GroupTheory.SpecificGroups.Alternating.KleinFour

/-!
# Alternating groups of degree at most four

For degree at most three the alternating group is abelian. For degree four,
the Sylow 2-subgroup is normal, and every Sylow 3-subgroup has prime order.
Consequently one may first handle the sole possibly nonnormal prime, and then
all remaining mixed intersections already equal their prime cores.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG uI

variable {G : Type uG} [Group G] [Finite G]

/-- Two distinct Sylow subgroups of prime order intersect trivially. -/
theorem sylow_inf_eq_bot_of_prime_card {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) (hcard : Nat.card P = p) (hPQ : P ≠ Q) :
    (P : Subgroup G) ⊓ (Q : Subgroup G) = ⊥ := by
  have hdvd : Nat.card ↥((P : Subgroup G) ⊓ (Q : Subgroup G)) ∣ p := by
    simpa only [hcard] using
      (Subgroup.card_dvd_of_le (H := (P : Subgroup G) ⊓ (Q : Subgroup G))
        (K := (P : Subgroup G)) inf_le_left)
  rcases (Nat.dvd_prime (Fact.out : Nat.Prime p)).mp hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · have heq : (P : Subgroup G) ⊓ (Q : Subgroup G) = (P : Subgroup G) :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h, hcard])
    have hle : (P : Subgroup G) ≤ (Q : Subgroup G) := by
      rw [← heq]
      exact inf_le_right
    exact False.elim (hPQ (Sylow.ext (P.is_maximal' Q.isPGroup' hle).symm))

/-- A Sylow subgroup of prime order admits a core-attaining mixed
intersection with every independently prescribed Sylow subgroup. -/
theorem exists_mixedSylowInter_eq_pCore_of_prime_card {p : ℕ} [Fact p.Prime]
    (P Q : Sylow p G) (hcard : Nat.card P = p) :
    ∃ x : G, mixedSylowInter P Q x = pCore p G := by
  classical
  by_cases hP : P.Normal
  · exact ⟨1, mixedSylowInter_eq_of_normal P Q 1 hP⟩
  have hother : ∃ R : Sylow p G, P ≠ R := by
    by_contra h
    push Not at h
    let : Subsingleton (Sylow p G) := ⟨fun R S ↦ (h R).symm.trans (h S)⟩
    exact hP (Sylow.normal_of_subsingleton P)
  obtain ⟨R, hR⟩ := hother
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G Q R
  have hbot : mixedSylowInter P Q x = ⊥ := by
    rw [mixedSylowInter, hx]
    exact sylow_inf_eq_bot_of_prime_card P R hcard hR
  have hcore : pCore p G = ⊥ := by
    apply bot_unique
    rw [← hbot]
    exact pCore_le_mixedSylowInter P Q x
  exact ⟨x, hbot.trans hcore.symm⟩

/-- Synchronization is immediate when only one prime may have a nonnormal
Sylow subgroup and that prime admits individual mixed core attainment. -/
theorem mixedTwoSylowCoreSynchronization_of_one_exceptional_prime
    (q : ℕ)
    (hnormal : ∀ p : ℕ, Nat.Prime p → p ≠ q →
      ∀ P : Sylow p G, P.Normal)
    (hq : ∀ P Q : Sylow q G, ∃ x : G,
      mixedSylowInter P Q x = pCore q G) :
    HasMixedTwoSylowCoreSynchronization.{uG, uI} G := by
  classical
  intro I _ p hp hinj P Q
  by_cases hex : ∃ i, p i = q
  · obtain ⟨j, hj⟩ := hex
    obtain ⟨x, hx⟩ : ∃ x : G,
        mixedSylowInter (P j) (Q j) x = pCore (p j) G := by
      have hq' : ∀ A B : Sylow (p j) G, ∃ x : G,
          mixedSylowInter A B x = pCore (p j) G := by
        rw [hj]
        exact hq
      exact hq' (P j) (Q j)
    refine ⟨x, fun i ↦ ?_⟩
    by_cases hij : i = j
    · subst i
      exact hx
    · let : Fact (p i).Prime := ⟨hp i⟩
      exact mixedSylowInter_eq_of_normal (P i) (Q i) x
        (hnormal (p i) (hp i) (fun hi ↦ hij (hinj (hi.trans hj.symm))) (P i))
  · refine ⟨1, fun i ↦ ?_⟩
    let : Fact (p i).Prime := ⟨hp i⟩
    exact mixedSylowInter_eq_of_normal (P i) (Q i) 1
      (hnormal (p i) (hp i) (fun hi ↦ hex ⟨i, hi⟩) (P i))

/-- Finite abelian groups satisfy mixed core synchronization. -/
theorem mixedTwoSylowCoreSynchronization_of_isMulCommutative
    [IsMulCommutative G] :
    HasMixedTwoSylowCoreSynchronization.{uG, uI} G := by
  intro I _ p hp _hinj P Q
  refine ⟨1, fun i ↦ ?_⟩
  let : Fact (p i).Prime := ⟨hp i⟩
  exact mixedSylowInter_eq_of_normal (P i) (Q i) 1
    (Subgroup.normal_of_isMulCommutative (P i : Subgroup G))

/-- A prime not dividing the group order has a trivial, hence normal,
Sylow subgroup. -/
theorem normal_sylow_of_not_dvd_card {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (hp : ¬ p ∣ Nat.card G) : P.Normal := by
  have hbot : (P : Subgroup G) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [Sylow.card_eq_multiplicity, Nat.factorization_eq_zero_of_not_dvd hp, pow_zero]
  change (P : Subgroup G).Normal
  rw [hbot]
  infer_instance

/-- Degree four has one normal Sylow 2-subgroup and prime-order
Sylow 3-subgroups, so arbitrary mixed rows synchronize. -/
theorem mixedTwoSylowCoreSynchronization_alternatingGroup_four :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (alternatingGroup (Fin 4)) := by
  apply mixedTwoSylowCoreSynchronization_of_one_exceptional_prime 3
  · intro p hp hp3 P
    let : Fact p.Prime := ⟨hp⟩
    by_cases hp2 : p = 2
    · subst p
      let : Subsingleton (Sylow 2 (alternatingGroup (Fin 4))) :=
        alternatingGroup.subsingleton_two_sylow (by simp)
      exact Sylow.normal_of_subsingleton P
    · apply normal_sylow_of_not_dvd_card P
      rw [alternatingGroup.card_of_card_eq_four (by simp)]
      intro hdvd
      have h12 : p ∣ 2 * 2 * 3 := by simpa using hdvd
      rcases hp.dvd_mul.mp h12 with h4 | h3
      · rcases hp.dvd_mul.mp h4 with h2 | h2
        · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one)
        · exact hp2 ((Nat.dvd_prime Nat.prime_two).mp h2 |>.resolve_left hp.ne_one)
      · exact hp3 ((Nat.dvd_prime (by decide : Nat.Prime 3)).mp h3 |>.resolve_left hp.ne_one)
  · intro P Q
    apply exists_mixedSylowInter_eq_pCore_of_prime_card P Q
    rw [Sylow.card_eq_multiplicity, alternatingGroup.card_of_card_eq_four (by simp)]
    rw [show 12 = 3 * 4 from rfl,
      Nat.factorization_mul_apply_of_coprime (by decide : Nat.Coprime 3 4),
      (by decide : Nat.Prime 3).factorization_self,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 4)]
    norm_num

/-- Every alternating group of degree at most four satisfies the mixed
strong Lisi--Sabatini property. -/
theorem mixedTwoSylowCoreSynchronization_alternatingGroup_le_four
    (n : ℕ) (hn : n ≤ 4) :
    HasMixedTwoSylowCoreSynchronization.{0, uI} (alternatingGroup (Fin n)) := by
  by_cases hn4 : n = 4
  · subst n
    exact mixedTwoSylowCoreSynchronization_alternatingGroup_four
  · let : IsMulCommutative (alternatingGroup (Fin n)) :=
      alternatingGroup.isMulCommutative_of_card_le_three (by simpa using (by omega : n ≤ 3))
    exact mixedTwoSylowCoreSynchronization_of_isMulCommutative

/-- The original minimal-intersection statement for degrees at most four. -/
theorem hasLisiSabatini_alternatingGroup_le_four (n : ℕ) (hn : n ≤ 4) :
    HasLisiSabatini.{0, uI} (alternatingGroup (Fin n)) :=
  StrongLisiSabatini.hasLisiSabatini
    (HasMixedTwoSylowCoreSynchronization.strongLisiSabatini
      (mixedTwoSylowCoreSynchronization_alternatingGroup_le_four n hn))

end LisiSabatini
