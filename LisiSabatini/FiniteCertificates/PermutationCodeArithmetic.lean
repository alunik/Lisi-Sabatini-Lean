module

public import LisiSabatini.FiniteCertificates.PermutationTable

/-!
# Natural-number arithmetic for eight-point permutation codes

The stored code has eight base-eight digits, with the image of zero first.
Composition therefore reads each digit of the right-hand permutation and
uses it as the digit index in the left-hand permutation. The resulting
checker can evaluate natural-number expressions without constructing
permutation multiplication terms.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates

/-- Digit `i` of an eight-digit base-eight code, starting at its most
significant digit. Its intended index range is `0 ≤ i < 8`. -/
def digit8 (c i : ℕ) : ℕ := (c / 8 ^ (7 - i)) % 8

/-- The explicit eight-digit Horner encoding. -/
def encodeDigits8 (a0 a1 a2 a3 a4 a5 a6 a7 : ℕ) : ℕ :=
  ((((((a0 * 8 + a1) * 8 + a2) * 8 + a3) * 8 + a4) * 8 + a5) * 8 + a6) * 8 + a7

/-- Pure natural-number composition of two encoded eight-point
permutations. -/
def composeCode8 (c d : ℕ) : ℕ :=
  encodeDigits8
    (digit8 c (digit8 d 0)) (digit8 c (digit8 d 1))
    (digit8 c (digit8 d 2)) (digit8 c (digit8 d 3))
    (digit8 c (digit8 d 4)) (digit8 c (digit8 d 5))
    (digit8 c (digit8 d 6)) (digit8 c (digit8 d 7))

/-- The existing permutation-code definition is precisely the explicit
eight-digit arithmetic expression. -/
theorem permutationCode_eq_encodeDigits8 (g : Equiv.Perm (Fin 8)) :
    permutationCode g = encodeDigits8
      (g 0).val (g 1).val (g 2).val (g 3).val
      (g 4).val (g 5).val (g 6).val (g 7).val := by
  simp [permutationCode, List.ofFn_succ, encodeDigits8]

/-- Reading a digit of a permutation code recovers that image exactly. -/
theorem digit8_permutationCode (g : Equiv.Perm (Fin 8)) (i : Fin 8) :
    digit8 (permutationCode g) i.val = (g i).val := by
  have h0 := (g 0).isLt
  have h1 := (g 1).isLt
  have h2 := (g 2).isLt
  have h3 := (g 3).isLt
  have h4 := (g 4).isLt
  have h5 := (g 5).isLt
  have h6 := (g 6).isLt
  have h7 := (g 7).isLt
  rw [permutationCode_eq_encodeDigits8]
  fin_cases i <;> norm_num [digit8, encodeDigits8] <;> (try dsimp at *) <;> omega

/-- Multiplication of eight-point permutation codes is pure digit
arithmetic, with the same composition order as the group operation. -/
theorem permutationCode_mul_fin8 (g h : Equiv.Perm (Fin 8)) :
    permutationCode (g * h) = composeCode8 (permutationCode g) (permutationCode h) := by
  rw [permutationCode_eq_encodeDigits8]
  unfold composeCode8
  have hd (i : Fin 8) :
      digit8 (permutationCode g) (digit8 (permutationCode h) i.val) =
        (g (h i)).val := by
    rw [digit8_permutationCode h i, digit8_permutationCode g (h i)]
  congr 1 <;> exact (hd _).symm

end LisiSabatini.FiniteCertificates
