module

public import LisiSabatini.InnerNormalRestrictionHomogeneous
public import LisiSabatini.TwoCoreSymplecticTypeMixedStructure

/-!
# The homogeneous extraspecial restriction in a mixed central product

For Berger's internal central product `P = EH`, the two factors commute.
Consequently conjugation by an arbitrary element `eh` of `P` acts on `E`
exactly as conjugation by `e`.  Thus `E ◁ P`, ambient conjugation on `E`
is inner, and every finite-dimensional irreducible `P`-representation
restricts homogeneously to `E`.

This is the Clifford-theoretic bridge needed before applying the
extraspecial Stone--von Neumann degree theorem.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uK uP uV

namespace BergerMixedCentralProductData

variable {P : Type uP} [Group P] [Finite P]

/-- In an internal mixed central product, ambient conjugation on the
extraspecial factor is inner. -/
theorem extraspecialPart_hasInnerConjugationOn
    (data : BergerMixedCentralProductData P) :
    Representation.HasInnerConjugationOn data.extraspecialPart := by
  intro g
  obtain ⟨e, h, heh⟩ := data.exists_extraspecial_mul_head g
  refine ⟨e, ?_⟩
  intro x
  have hremainder : e.1⁻¹ * g = h.1 := by
    rw [← heh]
    group
  rw [hremainder]
  exact (data.commute x h).symm

/-- The extraspecial factor is normal in the internal central product. -/
theorem extraspecialPart_normal
    (data : BergerMixedCentralProductData P) :
    data.extraspecialPart.Normal :=
  data.extraspecialPart_hasInnerConjugationOn.normal

/-- Every finite-dimensional irreducible representation of the mixed
central product restricts homogeneously to its extraspecial factor. -/
theorem extraspecialRestriction_isHomogeneous
    {k : Type uK} {V : Type uV}
    [Field k] [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (data : BergerMixedCentralProductData P)
    (rho : Representation k P V)
    (hirr : rho.IsIrreducible) :
    Representation.IsHomogeneous
      (rho.comp data.extraspecialPart.subtype) := by
  letI : data.extraspecialPart.Normal :=
    data.extraspecialPart_normal
  exact
    Representation.isHomogeneous_restrict_of_irreducible_of_innerConjugation
      rho data.extraspecialPart hirr
      data.extraspecialPart_hasInnerConjugationOn

end BergerMixedCentralProductData

end LisiSabatini
