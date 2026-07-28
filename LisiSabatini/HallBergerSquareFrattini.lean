module

public import LisiSabatini.HallBergerFrattiniDichotomy

/-!
# Squares and the Frattini subgroup of a finite `2`-group

For `p = 2`, the quotient by the normal closure of all squares has
exponent two and is therefore commutative.  Thus the derived subgroup is
already contained in the square closure, and the Burnside--Frattini
identity simplifies to `Φ(G) = G²`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- The derived subgroup of any group lies in the normal closure of all
squares. -/
theorem commutator_le_primePowerNormalClosure_two
    (G : Type u) [Group G] :
    commutator G ≤ primePowerNormalClosure 2 G := by
  let N : Subgroup G :=
    primePowerNormalClosure 2 G
  letI : N.Normal := inferInstance
  let Q := G ⧸ N
  have hsq : ∀ q : Q, q ^ 2 = 1 := by
    intro q
    refine Quotient.inductionOn' q fun x ↦ ?_
    change (QuotientGroup.mk' N x) ^ 2 = 1
    rw [← map_pow, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk']
    exact
      Subgroup.subset_normalClosure ⟨x, rfl⟩
  have hcomm :
      Std.Commutative (· * · : Q → Q → Q) := by
    constructor
    intro a b
    have haInv : a⁻¹ = a := by
      have h : a = a⁻¹ :=
        (mul_eq_one_iff_eq_inv.mp
          (by simpa only [pow_two] using hsq a))
      exact h.symm
    have hbInv : b⁻¹ = b := by
      have h : b = b⁻¹ :=
        (mul_eq_one_iff_eq_inv.mp
          (by simpa only [pow_two] using hsq b))
      exact h.symm
    have habInv : (a * b)⁻¹ = a * b := by
      have h : a * b = (a * b)⁻¹ :=
        (mul_eq_one_iff_eq_inv.mp
          (by simpa only [pow_two] using hsq (a * b)))
      exact h.symm
    calc
      a * b = (a * b)⁻¹ := habInv.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [haInv, hbInv]
  exact
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      hcomm

/-- In a finite `2`-group, the Frattini subgroup is exactly the normal
closure of all squares. -/
theorem frattini_eq_primePowerNormalClosure_two
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G) :
    frattini G = primePowerNormalClosure 2 G := by
  rw [frattini_eq_commutator_sup_primePowerNormalClosure
    Nat.prime_two hG2]
  exact sup_eq_right.mpr
    (commutator_le_primePowerNormalClosure_two G)

end LisiSabatini
