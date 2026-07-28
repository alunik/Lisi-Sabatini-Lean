import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.Ring

/-!
# Arithmetic for odd regular list colourings

The list-colouring count at an odd regular permutation top leaves at least

`2 ^ m - (m - 1) * 2 ^ (m / 3)`

regular selections.  The lemma below records that this is strictly larger
than one full orbit when `m` is odd and nontrivial.
-/

namespace LisiSabatini

/-- For odd `m ≥ 3`, the union bound for non-distinguishing binary list
colourings, together with one prescribed regular orbit of size `m`, is
strictly smaller than the full binary cube. -/
theorem oddRegularListColoring_union_add_orbit_lt_twoPow
    (m : ℕ) (hodd : Odd m) (hm : 3 ≤ m) :
    (m - 1) * 2 ^ (m / 3) + m < 2 ^ m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      by_cases hsmall : m < 9
      · interval_cases m <;> norm_num
      · have hmNine : 9 ≤ m := by omega
        let n := m - 6
        have hnThree : 3 ≤ n := by
          dsimp only [n]
          omega
        have hnLt : n < m := by
          dsimp only [n]
          omega
        have hnOdd : Odd n := by
          dsimp only [n]
          exact Nat.Odd.sub_even (by omega) hodd (by norm_num)
        have hind := ih n hnLt hnOdd hnThree
        have hmn : m = n + 6 := by
          dsimp only [n]
          omega
        have hdiv : (n + 6) / 3 = n / 3 + 2 := by omega
        rw [hmn, hdiv, pow_add, pow_add]
        norm_num only [pow_two, mul_assoc]
        have hstep :
            (n - 1) * 2 ^ (n / 3) + n + 1 ≤ 2 ^ n := by
          omega
        have hscaled :
            ((n - 1) * 2 ^ (n / 3) + n + 1) * 64 ≤
              2 ^ n * 64 :=
          Nat.mul_le_mul_right 64 hstep
        have hcoeff : n + 5 ≤ 16 * (n - 1) := by omega
        have hmain :
            (n + 5) * (2 ^ (n / 3) * 4) ≤
              ((n - 1) * 2 ^ (n / 3)) * 64 := by
          calc
            (n + 5) * (2 ^ (n / 3) * 4) =
                (n + 5) * (4 * 2 ^ (n / 3)) := by ring
            _ ≤ (16 * (n - 1)) * (4 * 2 ^ (n / 3)) :=
              Nat.mul_le_mul_right _ hcoeff
            _ = ((n - 1) * 2 ^ (n / 3)) * 64 := by ring
        have hrest : n + 6 < (n + 1) * 64 := by omega
        have haddPred : n + 6 - 1 = n + 5 := by omega
        calc
          (n + 6 - 1) * (2 ^ (n / 3) * 4) + (n + 6) =
              (n + 5) * (2 ^ (n / 3) * 4) + (n + 6) := by
                rw [haddPred]
          _ ≤ ((n - 1) * 2 ^ (n / 3)) * 64 + (n + 6) :=
            Nat.add_le_add_right hmain _
          _ < ((n - 1) * 2 ^ (n / 3)) * 64 + (n + 1) * 64 :=
            Nat.add_lt_add_left hrest _
          _ = ((n - 1) * 2 ^ (n / 3) + n + 1) * 64 := by ring
          _ ≤ 2 ^ n * 64 := hscaled

end LisiSabatini
