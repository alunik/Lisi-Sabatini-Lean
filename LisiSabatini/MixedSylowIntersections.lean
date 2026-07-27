import LisiSabatini.PCore

/-!
# Mixed intersections of Sylow subgroups

This file defines the two-row and three-row intersections used by the
three-conjugates programme.  The Sylow rows are independently prescribed.

Mathlib's action convention is

`x • P = x P x⁻¹`.

Thus `mixedSylowInter P Q x` denotes `P ∩ xQx⁻¹`, and
`mixedSylowTripleInter P Q R x y` denotes
`P ∩ xQx⁻¹ ∩ yRy⁻¹`.
-/

noncomputable section

namespace LisiSabatini

universe uG

variable {G : Type uG} [Group G]

/-- The intersection of a prescribed Sylow subgroup with a conjugate of an
independently prescribed Sylow subgroup at the same prime. -/
def mixedSylowInter {p : ℕ}
    (P Q : Sylow p G) (x : G) : Subgroup G :=
  (P : Subgroup G) ⊓ ((x • Q : Sylow p G) : Subgroup G)

/-- The intersection of three independently prescribed Sylow rows, with the
second and third rows conjugated by two common group elements. -/
def mixedSylowTripleInter {p : ℕ}
    (P Q R : Sylow p G) (x y : G) : Subgroup G :=
  ((P : Subgroup G) ⊓ ((x • Q : Sylow p G) : Subgroup G)) ⊓
    ((y • R : Sylow p G) : Subgroup G)

/-- The `p`-core is a lower bound for every mixed two-row Sylow
intersection. -/
theorem pCore_le_mixedSylowInter {p : ℕ}
    (P Q : Sylow p G) (x : G) :
    pCore p G ≤ mixedSylowInter P Q x :=
  le_inf (pCore_le_sylow P) (pCore_le_sylow (x • Q))

/-- The `p`-core is a lower bound for every mixed three-row Sylow
intersection. -/
theorem pCore_le_mixedSylowTripleInter {p : ℕ}
    (P Q R : Sylow p G) (x y : G) :
    pCore p G ≤ mixedSylowTripleInter P Q R x y :=
  le_inf (pCore_le_mixedSylowInter P Q x) (pCore_le_sylow (y • R))

/-- A normal Sylow subgroup is the `p`-core. -/
theorem pCore_eq_sylow_of_normal {p : ℕ} [Fact p.Prime] [Finite G]
    (P : Sylow p G) (hP : P.Normal) :
    pCore p G = (P : Subgroup G) :=
  le_antisymm (pCore_le_sylow P) (le_pCore P.isPGroup' hP)

/-- If a Sylow `p`-subgroup is normal, every mixed two-row intersection is
the `p`-core. -/
theorem mixedSylowInter_eq_of_normal {p : ℕ} [Fact p.Prime] [Finite G]
    (P Q : Sylow p G) (x : G) (hP : P.Normal) :
    mixedSylowInter P Q x = pCore p G := by
  letI : P.Normal := hP
  letI : Unique (Sylow p G) := Sylow.unique_of_normal P hP
  rw [mixedSylowInter, Subsingleton.elim Q P, Sylow.smul_eq_of_normal, inf_idem]
  exact (pCore_eq_sylow_of_normal P hP).symm

/-- If a Sylow `p`-subgroup is normal, every mixed three-row intersection is
the `p`-core. -/
theorem mixedSylowTripleInter_eq_of_normal
    {p : ℕ} [Fact p.Prime] [Finite G]
    (P Q R : Sylow p G) (x y : G) (hP : P.Normal) :
    mixedSylowTripleInter P Q R x y = pCore p G := by
  letI : P.Normal := hP
  letI : Unique (Sylow p G) := Sylow.unique_of_normal P hP
  have hx : x • P = P := Sylow.smul_eq_of_normal
  have hy : y • P = P := Sylow.smul_eq_of_normal
  rw [mixedSylowTripleInter, Subsingleton.elim Q P, Subsingleton.elim R P,
    hx, hy]
  simp only [inf_idem]
  exact (pCore_eq_sylow_of_normal P hP).symm

end LisiSabatini
