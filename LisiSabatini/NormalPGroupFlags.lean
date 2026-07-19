import LisiSabatini.NormalPrimeSquareCentralizer
import LisiSabatini.QuotientCardinalityCore
import Mathlib.GroupTheory.Sylow

/-!
# Short ambient-normal flags in finite p-groups

This file formalizes the first two steps of the standard normal series in a
finite `p`-group.

* Every nontrivial normal subgroup meets the ambient center nontrivially.
* It consequently contains an ambient-normal central subgroup of order `p`.
* A normal subgroup of order `p` is central.
* More generally, a normal subgroup of cardinality at least `p ^ 2` contains
  an ambient-normal flag of orders `p` and `p ^ 2`.

The last statement is stronger than the elementary-abelian version: neither
commutativity nor exponent `p` is needed.  After choosing the central
order-`p` term, apply the order-`p` existence theorem to the image of the
given subgroup in the quotient and pull the result back.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open Subgroup

/-! ## A nontrivial central element in every nontrivial normal subgroup -/

/-- A nontrivial normal subgroup of a finite `p`-group meets the ambient
center nontrivially. -/
theorem center_inf_normal_ne_bot_of_isPGroup
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    Subgroup.center G ⊓ N ≠ ⊥ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : N.Normal := hNnormal
  have hNp : IsPGroup p N := hGp.to_subgroup N
  have hNcardNeOne : Nat.card N ≠ 1 := by
    exact ne_of_gt (N.one_lt_card_iff_ne_bot.mpr hNne)
  have hpDvdN : p ∣ Nat.card N :=
    hNp.card_eq_or_dvd.resolve_left hNcardNeOne
  have hConjP : IsPGroup p (ConjAct G) :=
    hGp.of_equiv ConjAct.toConjAct
  have honeFixed : (1 : N) ∈ MulAction.fixedPoints (ConjAct G) N := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact smul_one g
  obtain ⟨b, hbFixed, hbNe⟩ :=
    hConjP.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      N hpDvdN honeFixed
  have hbCenter : (b : G) ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hfix := MulAction.mem_fixedPoints.mp hbFixed
      (ConjAct.toConjAct g)
    have hconj : g * (b : G) * g⁻¹ = b := by
      exact congrArg Subtype.val hfix
    exact mul_inv_eq_iff_eq_mul.mp hconj
  have hbInf : (b : G) ∈ Subgroup.center G ⊓ N := ⟨hbCenter, b.2⟩
  intro hbot
  have hbOne : (b : G) = 1 := by
    have : (b : G) ∈ (⊥ : Subgroup G) := hbot ▸ hbInf
    simpa using this
  exact hbNe (Subtype.ext hbOne.symm)

/-! ## The ambient-normal subgroup of order p -/

/-- Every nontrivial normal subgroup of a finite `p`-group contains a
central ambient-normal subgroup of order `p`. -/
theorem exists_normal_central_subgroup_card_prime_le
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    ∃ C : Subgroup G,
      C.Normal ∧ C ≤ N ∧ Nat.card C = p ∧
        C ≤ Subgroup.center G := by
  letI : Fact p.Prime := ⟨hp⟩
  let H : Subgroup G := Subgroup.center G ⊓ N
  have hHne : H ≠ ⊥ :=
    center_inf_normal_ne_bot_of_isPGroup hp hGp N hNnormal hNne
  have hHp : IsPGroup p H := hGp.to_subgroup H
  have hHcardNeOne : Nat.card H ≠ 1 := by
    exact ne_of_gt (H.one_lt_card_iff_ne_bot.mpr hHne)
  have hpDvdH : p ∣ Nat.card H :=
    hHp.card_eq_or_dvd.resolve_left hHcardNeOne
  have hpLeH : p ^ 1 ≤ Nat.card H := by
    simpa only [pow_one] using Nat.le_of_dvd Nat.card_pos hpDvdH
  obtain ⟨C, hCleH, hCcard⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card
      (G := G) (n := 1) hp hGp hpLeH
  have hCcenter : C ≤ Subgroup.center G := hCleH.trans inf_le_left
  have hCN : C ≤ N := hCleH.trans inf_le_right
  have hCnormal : C.Normal := by
    refine ⟨?_⟩
    intro c hc g
    have hcomm : g * c = c * g :=
      Subgroup.mem_center_iff.mp (hCcenter hc) g
    have hconj : g * c * g⁻¹ = c :=
      mul_inv_eq_iff_eq_mul.mpr hcomm
    simpa only [hconj] using hc
  exact ⟨C, hCnormal, hCN, by simpa using hCcard, hCcenter⟩

/-- A normal subgroup of prime order in a finite `p`-group lies in the
ambient center. -/
theorem normal_subgroup_le_center_of_natCard_eq_prime
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (N : Subgroup G) (hNnormal : N.Normal)
    (hNcard : Nat.card N = p) :
    N ≤ Subgroup.center G := by
  have hNne : N ≠ ⊥ := by
    intro hbot
    have : p = 1 := by
      rw [← hNcard, hbot, Subgroup.card_bot]
    exact hp.ne_one this
  obtain ⟨C, _hCnormal, hCN, hCcard, hCcenter⟩ :=
    exists_normal_central_subgroup_card_prime_le
      hp hGp N hNnormal hNne
  have hCN_eq : C = N :=
    Subgroup.eq_of_le_of_card_ge hCN (by rw [hNcard, hCcard])
  rwa [← hCN_eq]

/-! ## A two-step ambient-normal flag -/

/-- A normal subgroup of a finite `p`-group whose cardinality is at least
`p ^ 2` contains nested ambient-normal subgroups of orders `p` and `p ^ 2`.

This is stronger than the elementary-abelian flag statement: the proof does
not require the subgroup to be commutative or to have exponent `p`. -/
theorem exists_normal_flag_card_prime_prime_sq_le
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (E : Subgroup G) (hEnormal : E.Normal)
    (hEcard : p ^ 2 ≤ Nat.card E) :
    ∃ C M : Subgroup G,
      C.Normal ∧ M.Normal ∧ C ≤ M ∧ M ≤ E ∧
        Nat.card C = p ∧ Nat.card M = p ^ 2 ∧
          C ≤ Subgroup.center G := by
  have hEne : E ≠ ⊥ := by
    intro hEbot
    rw [hEbot, Subgroup.card_bot] at hEcard
    have hpSqGtOne : 1 < p ^ 2 :=
      one_lt_pow₀ hp.one_lt (show 2 ≠ 0 by omega)
    omega
  obtain ⟨C, hCnormal, hCE, hCcard, hCcenter⟩ :=
    exists_normal_central_subgroup_card_prime_le
      hp hGp E hEnormal hEne
  letI : C.Normal := hCnormal
  let q : G →* G ⧸ C := QuotientGroup.mk' C
  let Ebar : Subgroup (G ⧸ C) := E.map q
  have hQp : IsPGroup p (G ⧸ C) := hGp.to_quotient C
  have hEbarNormal : Ebar.Normal :=
    hEnormal.map q (QuotientGroup.mk'_surjective C)
  have hEbarNe : Ebar ≠ ⊥ := by
    intro hbot
    have hEleC : E ≤ C := by
      have := (Subgroup.map_eq_bot_iff (H := E) (f := q)).mp hbot
      simpa only [q, QuotientGroup.ker_mk'] using this
    have hEcardLe : Nat.card E ≤ p := by
      calc
        Nat.card E ≤ Nat.card C := E.card_le_of_le hEleC
        _ = p := hCcard
    have hpLtSq : p < p ^ 2 := by
      simpa only [pow_one] using
        Nat.pow_lt_pow_right hp.one_lt (show 1 < 2 by omega)
    omega
  obtain ⟨D, hDnormal, hDEbar, hDcard, _hDcenter⟩ :=
    exists_normal_central_subgroup_card_prime_le
      hp hQp Ebar hEbarNormal hEbarNe
  let M : Subgroup G := D.comap q
  have hMnormal : M.Normal := hDnormal.comap q
  have hCM : C ≤ M := by
    intro c hc
    change q c ∈ D
    rw [show q c = 1 from (QuotientGroup.eq_one_iff c).mpr hc]
    exact D.one_mem
  have hqker : q.ker = C := by
    simpa only [q] using
      (QuotientGroup.ker_mk' (G := G) (N := C))
  have hME : M ≤ E := by
    calc
      M ≤ (E.map q).comap q := Subgroup.comap_mono hDEbar
      _ = E := by
        rw [Subgroup.comap_map_eq, hqker, sup_eq_left.mpr hCE]
  have hMcard : Nat.card M = p ^ 2 := by
    calc
      Nat.card M = Nat.card C * Nat.card D := by
        simpa only [M, q] using
          natCard_comap_quotient_eq_mul C hCnormal D
      _ = p * p := by rw [hCcard, hDcard]
      _ = p ^ 2 := (pow_two p).symm
  exact ⟨C, M, hCnormal, hMnormal, hCM, hME,
    hCcard, hMcard, hCcenter⟩

end LisiSabatini
