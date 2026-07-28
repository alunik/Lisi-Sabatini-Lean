module

public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Ring

/-!
# Arithmetic for regular ternary list colourings

For a regular permutation group on `m ≥ 2` points, every nonidentity
element is fixed-point-free and therefore has at most `m / 2` cycles.
With three available local colours, the deterministic-cycle union bound,
together with two prescribed external orbits, is

`(m - 1) * 3^(m / 2) + 2 * m`,

which is strictly smaller than the full ternary cube `3^m`.
-/

@[expose] public section

namespace LisiSabatini

/-- The two-external-orbit budget needed to propagate a three-colour
palette through successive imprimitive layers. -/
theorem regularTernaryListColoring_union_add_twoOrbits_lt_threePow
    (m : ℕ) (hm : 2 ≤ m) :
    (m - 1) * 3 ^ (m / 2) + 2 * m < 3 ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hsmall : m < 4
      · interval_cases m <;> norm_num
      · let n := m - 2
        have hnTwo : 2 ≤ n := by
          dsimp only [n]
          omega
        have hnLt : n < m := by
          dsimp only [n]
          omega
        have hind := ih n hnLt hnTwo
        have hmn : m = n + 2 := by
          dsimp only [n]
          omega
        have hdiv : (n + 2) / 2 = n / 2 + 1 := by omega
        have hstep :
            (n - 1) * 3 ^ (n / 2) + 2 * n + 1 ≤ 3 ^ n := by
          omega
        rw [hmn, hdiv, pow_succ, pow_add]
        norm_num only [pow_two]
        have hcoeff :
            3 * (n + 1) ≤ 9 * (n - 1) := by
          omega
        have hmain :
            (n + 1) * (3 ^ (n / 2) * 3) ≤
              ((n - 1) * 3 ^ (n / 2)) * 9 := by
          calc
            (n + 1) * (3 ^ (n / 2) * 3) =
                (3 * (n + 1)) * 3 ^ (n / 2) := by ring
            _ ≤ (9 * (n - 1)) * 3 ^ (n / 2) :=
              Nat.mul_le_mul_right _ hcoeff
            _ = ((n - 1) * 3 ^ (n / 2)) * 9 := by ring
        have hrest : 2 * (n + 2) < (2 * n + 1) * 9 := by
          omega
        have hcompare :
            (n + 2 - 1) * (3 ^ (n / 2) * 3) + 2 * (n + 2) <
              ((n - 1) * 3 ^ (n / 2) + 2 * n + 1) * 9 := by
          have hnSub : n + 2 - 1 = n + 1 := by omega
          rw [hnSub]
          calc
            (n + 1) * (3 ^ (n / 2) * 3) + 2 * (n + 2) ≤
                ((n - 1) * 3 ^ (n / 2)) * 9 + 2 * (n + 2) :=
              Nat.add_le_add_right hmain _
            _ < ((n - 1) * 3 ^ (n / 2)) * 9 +
                (2 * n + 1) * 9 :=
              Nat.add_lt_add_left hrest _
            _ = ((n - 1) * 3 ^ (n / 2) + 2 * n + 1) * 9 := by
              ring
        calc
          (n + 2 - 1) * (3 ^ (n / 2) * 3) + 2 * (n + 2) <
              ((n - 1) * 3 ^ (n / 2) + 2 * n + 1) * 9 :=
            hcompare
          _ ≤ 3 ^ n * 9 := Nat.mul_le_mul_right 9 hstep

end LisiSabatini
