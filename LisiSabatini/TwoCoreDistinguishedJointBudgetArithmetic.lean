import Mathlib

/-!
# The distinguished-two joint budget

Let `q` be the cardinality of the affine chief factor, `S` the total
diagonal bad locus of the odd rows, `B` the diagonal bad locus of the
normal `2`-core, `A` the number of active involutions in that core, and
`C` its order.

The existing odd-row argument gives

`2 * S ≤ q * (q - 1)`,

while the active-involution rectangle cover gives

`B ≤ 1 + A * (q - 1)`.

This file records the exact residual inequality needed after combining
those two estimates.  In particular, half-density alone is not silently
treated as sufficient: after replacing `2*A` by `q-1`, one still has to
pay the explicit term `4*C`.
-/

namespace LisiSabatini

/-- The exact residual left by the standard odd-row and active-involution
envelopes in the distinguished-`2` row. -/
def DistinguishedTwoCoreJointEnvelopeBudget
    (q active coreOrder : ℕ) : Prop :=
  2 * (1 + active * (q - 1)) + 4 * coreOrder <
    q * (q + 1)

/-- The exact envelope budget closes the full distinguished-`2` count. -/
theorem distinguishedTwo_joint_lt_of_envelopeBudget
    {q oddBad twoBad active coreOrder : ℕ}
    (hodd : 2 * oddBad ≤ q * (q - 1))
    (htwo : twoBad ≤ 1 + active * (q - 1))
    (hbudget :
      DistinguishedTwoCoreJointEnvelopeBudget q active coreOrder) :
    twoBad + oddBad + 2 * coreOrder < q * q := by
  unfold DistinguishedTwoCoreJointEnvelopeBudget at hbudget
  have hidentity :
      q * (q + 1) + q * (q - 1) = 2 * (q * q) := by
    by_cases hq : q = 0
    · simp [hq]
    · obtain ⟨q₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring
  have hdouble :
      2 * (twoBad + oddBad + 2 * coreOrder) ≤
        (2 * (1 + active * (q - 1)) + 4 * coreOrder) +
          q * (q - 1) := by
    calc
      2 * (twoBad + oddBad + 2 * coreOrder) =
          (2 * twoBad + 2 * oddBad) + 4 * coreOrder := by ring
      _ ≤
          (2 * (1 + active * (q - 1)) + q * (q - 1)) +
            4 * coreOrder :=
        Nat.add_le_add_right
          (Nat.add_le_add
            (Nat.mul_le_mul_left 2 htwo) hodd)
          (4 * coreOrder)
      _ =
          (2 * (1 + active * (q - 1)) + 4 * coreOrder) +
            q * (q - 1) := by ring
  have hstrict :
      (2 * (1 + active * (q - 1)) + 4 * coreOrder) +
          q * (q - 1) <
        2 * (q * q) := by
    calc
      (2 * (1 + active * (q - 1)) + 4 * coreOrder) +
            q * (q - 1) <
          q * (q + 1) + q * (q - 1) :=
        Nat.add_lt_add_right hbudget (q * (q - 1))
      _ = 2 * (q * q) := hidentity
  exact
    (Nat.mul_lt_mul_left (by norm_num : 0 < 2)).mp
      (hdouble.trans_lt hstrict)

/-- Equivalent residual form of the exact joint envelope.  The factor
`q + 2 - 2*active` measures the slack left by the active-involution
count before the core order is charged. -/
theorem distinguishedTwo_jointEnvelopeBudget_of_residual
    {q active coreOrder : ℕ}
    (hactive : 2 * active ≤ q + 2)
    (horder :
      4 * coreOrder <
        (q - 1) * (q + 2 - 2 * active)) :
    DistinguishedTwoCoreJointEnvelopeBudget q active coreOrder := by
  unfold DistinguishedTwoCoreJointEnvelopeBudget
  have hsplit :
      2 * active + (q + 2 - 2 * active) = q + 2 :=
    Nat.add_sub_of_le hactive
  calc
    2 * (1 + active * (q - 1)) + 4 * coreOrder =
        2 + 2 * active * (q - 1) + 4 * coreOrder := by ring
    _ < 2 + 2 * active * (q - 1) +
          (q - 1) * (q + 2 - 2 * active) :=
      Nat.add_lt_add_left horder
        (2 + 2 * active * (q - 1))
    _ = q * (q + 1) := by
      have hproductPos :
          0 < (q - 1) * (q + 2 - 2 * active) :=
        lt_of_le_of_lt (Nat.zero_le _) horder
      have hqNe : q ≠ 0 := by
        have hpredPos :
            0 < q - 1 :=
          pos_of_mul_pos_left hproductPos (Nat.zero_le _)
        omega
      obtain ⟨q₀, rfl⟩ :=
        Nat.exists_eq_succ_of_ne_zero hqNe
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel] at hsplit ⊢
      calc
        2 + 2 * active * q₀ +
              q₀ * (q₀ + 1 + 2 - 2 * active) =
            2 + q₀ *
              (2 * active + (q₀ + 1 + 2 - 2 * active)) := by
          ring
        _ = 2 + q₀ * (q₀ + 1 + 2) := by rw [hsplit]
        _ = (q₀ + 1) * (q₀ + 1 + 1) := by ring

/-- Half-density leaves the additional order comparison
`4*|O₂| < 3(q-1)`.  This theorem makes that residual explicit. -/
theorem distinguishedTwo_jointEnvelopeBudget_of_halfDensity
    {q active coreOrder : ℕ}
    (hq : 0 < q)
    (hactive : 2 * active ≤ q - 1)
    (horder : 4 * coreOrder < 3 * (q - 1)) :
    DistinguishedTwoCoreJointEnvelopeBudget q active coreOrder := by
  unfold DistinguishedTwoCoreJointEnvelopeBudget
  have hactiveMul :
      (2 * active) * (q - 1) ≤
        (q - 1) * (q - 1) :=
    Nat.mul_le_mul_right (q - 1) hactive
  calc
    2 * (1 + active * (q - 1)) + 4 * coreOrder =
        2 + (2 * active) * (q - 1) + 4 * coreOrder := by
      ring
    _ ≤ 2 + (q - 1) * (q - 1) + 4 * coreOrder :=
      Nat.add_le_add_right
        (Nat.add_le_add_left hactiveMul 2) (4 * coreOrder)
    _ < 2 + (q - 1) * (q - 1) + 3 * (q - 1) :=
      Nat.add_lt_add_left horder
        (2 + (q - 1) * (q - 1))
    _ = q * (q + 1) := by
      obtain ⟨q₀, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      ring

/-- A shape-sensitive active-count bound may be substituted directly
into the exact residual. -/
theorem distinguishedTwo_jointEnvelopeBudget_mono
    {q active activeBound coreOrder coreOrderBound : ℕ}
    (hactive : active ≤ activeBound)
    (horder : coreOrder ≤ coreOrderBound)
    (hbudget :
      DistinguishedTwoCoreJointEnvelopeBudget
        q activeBound coreOrderBound) :
    DistinguishedTwoCoreJointEnvelopeBudget q active coreOrder := by
  unfold DistinguishedTwoCoreJointEnvelopeBudget at hbudget ⊢
  refine lt_of_le_of_lt ?_ hbudget
  apply Nat.add_le_add
  · apply Nat.mul_le_mul_left
    apply Nat.add_le_add_left
    exact Nat.mul_le_mul_right (q - 1) hactive
  · exact Nat.mul_le_mul_left 4 horder

/-- Arithmetic for the nonexceptional semidihedral range.  Here `k`
parametrizes a group of order `16*k`, its active-involution envelope is
`4*k`, and `t` is the quotient `(q-1)/(8*k)`.  As soon as `t ≥ 2`, the
coarse odd-row bound and the exact shape data already close jointly. -/
theorem semidihedral_jointEnvelopeBudget_of_rotationQuotient_ge_two
    {q k t : ℕ}
    (hk : 0 < k)
    (ht : 2 ≤ t)
    (hq : q = 8 * k * t + 1) :
    DistinguishedTwoCoreJointEnvelopeBudget q (4 * k) (16 * k) := by
  subst q
  unfold DistinguishedTwoCoreJointEnvelopeBudget
  have htPred : 1 ≤ t - 1 := by omega
  have hproduct :
      2 ≤ k * t * (t - 1) := by
    calc
      2 = 1 * 2 * 1 := by norm_num
      _ ≤ k * t * (t - 1) :=
        Nat.mul_le_mul
          (Nat.mul_le_mul (Nat.one_le_iff_ne_zero.mpr hk.ne') ht)
          htPred
  have hgap :
      64 * k <
        64 * k * k * t * (t - 1) + 24 * k * t := by
    calc
      64 * k < 128 * k :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) hk
      _ = (64 * k) * 2 := by ring
      _ ≤ (64 * k) * (k * t * (t - 1)) :=
        Nat.mul_le_mul_left (64 * k) hproduct
      _ = 64 * k * k * t * (t - 1) := by ring
      _ ≤ 64 * k * k * t * (t - 1) + 24 * k * t :=
        Nat.le_add_right _ _
  have hleft :
      2 * (1 + 4 * k * ((8 * k * t + 1) - 1)) +
          4 * (16 * k) =
        2 + 64 * k * k * t + 64 * k := by
    simp only [Nat.add_sub_cancel]
    ring
  have hright :
      (8 * k * t + 1) * (8 * k * t + 1 + 1) =
        2 + 64 * k * k * t +
          (64 * k * k * t * (t - 1) + 24 * k * t) := by
    have htEq : t = (t - 1) + 1 := by omega
    rw [htEq]
    simp only [Nat.add_sub_cancel]
    ring
  rw [hleft, hright]
  exact Nat.add_lt_add_left hgap (2 + 64 * k * k * t)

/-- At rotation quotient one, the semidihedral `2`-core contribution
itself (bad locus plus two full orbits) fits.  What must then be shown
separately is that all odd rows vanish. -/
theorem semidihedral_twoCoreEnvelope_add_twoOrbits_lt_of_rotationQuotient_one
    {q k twoBad : ℕ}
    (hk : 0 < k)
    (hq : q = 8 * k + 1)
    (htwo : twoBad ≤ 1 + 4 * k * (q - 1)) :
    twoBad + 2 * (16 * k) < q * q := by
  subst q
  have hsmall : 16 * k < 32 * k * k := by
    calc
      16 * k < 32 * k :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) hk
      _ ≤ 32 * k * k := by
        nth_rewrite 1 [show 32 * k = 32 * k * 1 by ring]
        exact Nat.mul_le_mul_left (32 * k)
          (Nat.one_le_iff_ne_zero.mpr hk.ne')
  have hmiddle :
      32 * k + 32 * k * k <
        16 * k + 64 * k * k := by
    have :=
      Nat.add_lt_add_left hsmall (16 * k + 32 * k * k)
    calc
      32 * k + 32 * k * k =
          (16 * k + 32 * k * k) + 16 * k := by ring
      _ < (16 * k + 32 * k * k) + 32 * k * k := this
      _ = 16 * k + 64 * k * k := by ring
  calc
    twoBad + 2 * (16 * k) ≤
        (1 + 4 * k * (8 * k + 1 - 1)) + 2 * (16 * k) :=
      Nat.add_le_add_right htwo _
    _ = 1 + (32 * k + 32 * k * k) := by
      simp only [Nat.add_sub_cancel]
      ring
    _ < 1 + (16 * k + 64 * k * k) :=
      Nat.add_lt_add_left hmiddle 1
    _ = (8 * k + 1) * (8 * k + 1) := by ring

end LisiSabatini
