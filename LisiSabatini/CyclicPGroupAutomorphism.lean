module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Odd prime-order automorphisms of cyclic prime groups

These elementary automorphism lemmas are used by the cyclic-Frattini
argument.  They are independent of the later Hall index-descent machinery,
so isolating them keeps Hobby's theorem out of that legacy dependency cone.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- If `k ^ p = 1` modulo `p ^ n`, then `p ^ n` divides `p * (k - 1)`.
This is the elementary LTE calculation used in the automorphism lemma. -/
theorem primePow_dvd_prime_mul_sub_one_of_pow_modEq_one
    {p n k : ℕ} (hp : p.Prime) (hpOdd : Odd p) (hk : 0 < k)
    (hmod : k ^ p ≡ 1 [MOD p ^ n]) :
    p ^ n ∣ p * (k - 1) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have honePow : 1 ≤ k ^ p := one_le_pow₀ hk
  have hpowDvd : p ^ n ∣ k ^ p - 1 :=
    (Nat.modEq_iff_dvd' honePow).mp hmod.symm
  have hpDvdPow : p ∣ k ^ p - 1 :=
    (dvd_pow_self p hn).trans hpowDvd
  have hcastPow : (k : ZMod p) ^ p = 1 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff]
    exact (Nat.modEq_iff_dvd' honePow).mpr hpDvdPow |>.symm
  have hcast : (k : ZMod p) = 1 := by
    calc
      (k : ZMod p) = (k : ZMod p) ^ p := (ZMod.pow_card _).symm
      _ = 1 := hcastPow
  have hcastNat : (k : ZMod p) = ((1 : ℕ) : ZMod p) := by
    simpa using hcast
  have hkMod : k ≡ 1 [MOD p] :=
    (ZMod.natCast_eq_natCast_iff k 1 p).mp hcastNat
  have hpDvdSub : p ∣ k - 1 :=
    (Nat.modEq_iff_dvd' hk).mp hkMod.symm
  have hpNotDvdK : ¬ p ∣ k := by
    intro hpk
    have hkZero : k ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr hpk
    have hOneZero : 1 ≡ 0 [MOD p] := hkMod.symm.trans hkZero
    exact hp.ne_one (Nat.dvd_one.mp (Nat.modEq_zero_iff_dvd.mp hOneZero))
  rcases eq_or_ne k 1 with rfl | hkOne
  · simp
  have hkgt : 1 < k := lt_of_le_of_ne hk hkOne.symm
  have hval := padicValNat.pow_sub_pow (p := p) hpOdd
    hkgt hpDvdSub hpNotDvdK hp.ne_zero
  have hpowNe : k ^ p - 1 ≠ 0 := by
    exact Nat.sub_ne_zero_of_lt (one_lt_pow₀ hkgt hp.ne_zero)
  have hnVal : n ≤ padicValNat p (k ^ p - 1) :=
    (padicValNat_dvd_iff_le hpowNe).mp hpowDvd
  simp only [one_pow] at hval
  rw [hval, padicValNat_self] at hnVal
  have hpredVal : n - 1 ≤ padicValNat p (k - 1) := by omega
  have hsubNe : k - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hkgt
  have hpredDvd : p ^ (n - 1) ∣ k - 1 :=
    (padicValNat_dvd_iff_le hsubNe).mpr hpredVal
  have hnSucc : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hn)
  rw [← hnSucc, pow_succ]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    Nat.mul_dvd_mul_left p hpredDvd

/-- An automorphism of order dividing an odd prime `p` on a finite cyclic
`p`-group fixes every `p`-th power. -/
theorem cyclicPGroup_aut_pow_fixed_of_pow_prime_eq_one
    {p : ℕ} {A : Type*} [Group A] [Finite A]
    (hp : p.Prime) (hpOdd : Odd p) (hAp : IsPGroup p A)
    (hACyclic : IsCyclic A) (σ : MulAut A) (hσ : σ ^ p = 1) :
    ∀ a : A, σ (a ^ p) = a ^ p := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hA : Nontrivial A
  · letI : Nontrivial A := hA
    letI : IsCyclic A := hACyclic
    obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hAp
    have hn : n ≠ 0 := by
      intro hn0
      have hgt := Finite.one_lt_card (α := A)
      rw [hcard, hn0, pow_zero] at hgt
      exact (Nat.lt_irrefl 1 hgt)
    obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := A)
    have hgOrder : orderOf g = Nat.card A :=
      orderOf_eq_card_of_forall_mem_powers hg
    have hgNe : g ≠ 1 := by
      intro hgone
      have : orderOf g = 1 := by simp [hgone]
      have := Finite.one_lt_card (α := A)
      omega
    obtain ⟨k, hk⟩ := hg (σ g)
    change g ^ k = σ g at hk
    have hkpos : 0 < k := by
      rcases k with _ | k
      · simp only [pow_zero] at hk
        exfalso
        apply hgNe
        apply σ.injective
        simpa using hk.symm
      · exact Nat.succ_pos k
    have hiterate : ∀ j : ℕ, (σ ^ j) g = g ^ (k ^ j) := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
          calc
            (σ ^ (j + 1)) g = (σ ^ j) (σ g) := by
              rw [pow_succ]
              rfl
            _ = (σ ^ j) (g ^ k) := by rw [← hk]
            _ = ((σ ^ j) g) ^ k := map_pow (σ ^ j) g k
            _ = (g ^ (k ^ j)) ^ k := by rw [ih]
            _ = g ^ (k ^ (j + 1)) := by
              rw [← pow_mul, pow_succ]
    have hgPow : g ^ (k ^ p) = g := by
      rw [← hiterate p, hσ]
      rfl
    have hmodOrder : k ^ p ≡ 1 [MOD orderOf g] :=
      pow_eq_pow_iff_modEq.mp (by simpa using hgPow)
    have hmod : k ^ p ≡ 1 [MOD p ^ n] := by
      simpa [hgOrder, hcard] using hmodOrder
    have hdvd : p ^ n ∣ p * (k - 1) :=
      primePow_dvd_prime_mul_sub_one_of_pow_modEq_one hp hpOdd hkpos hmod
    have hkp : p ≤ k * p := by
      exact Nat.le_mul_of_pos_left p hkpos
    have hmodKP : k * p ≡ p [MOD p ^ n] := by
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd' hkp]
      simpa [Nat.mul_sub_left_distrib, mul_comm] using hdvd
    have hgpfixed : σ (g ^ p) = g ^ p := by
      calc
        σ (g ^ p) = (σ g) ^ p := map_pow σ g p
        _ = (g ^ k) ^ p := by rw [← hk]
        _ = g ^ (k * p) := by rw [pow_mul]
        _ = g ^ p := pow_eq_pow_iff_modEq.mpr <| by
          simpa [hgOrder, hcard] using hmodKP
    intro a
    obtain ⟨m, rfl⟩ := hg a
    calc
      σ ((g ^ m) ^ p) = σ ((g ^ p) ^ m) := by
        congr 1
        rw [← pow_mul, ← pow_mul, mul_comm]
      _ = (σ (g ^ p)) ^ m := map_pow σ (g ^ p) m
      _ = (g ^ p) ^ m := by rw [hgpfixed]
      _ = (g ^ m) ^ p := by
        rw [← pow_mul, ← pow_mul, mul_comm]
  · haveI : Subsingleton A := not_nontrivial_iff_subsingleton.mp hA
    intro a
    exact Subsingleton.elim _ _

end LisiSabatini
