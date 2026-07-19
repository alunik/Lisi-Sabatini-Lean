import LisiSabatini.ChiefActionStructuralDichotomy

/-!
# Strict dimension descent in the chief-action dichotomy

The Clifford extraction theorem produces a genuine primitive system of
imprimitivity, but recursive NCAS also needs a well-founded measure.  This
file derives that measure from the extracted coordinates: an action on
`Fin d → ZMod r` with `b` nonzero blocks of local dimension `e` satisfies
`d = b * e`; since `1 < b`, every recursive local problem has `e < d`.

The public endpoint strengthens the quasiprimitive/imprimitive dichotomy by
packaging the strict dimension decrease with the internal presentation.  No
new structural or representation-theoretic hypothesis is introduced.
-/

noncomputable section

namespace LisiSabatini

namespace PrimeFieldPrimitiveInternalImprimitivityPresentation

/-- Product coordinates force the ambient dimension to be the number of
blocks times the common local dimension. -/
theorem ambientDimension_eq_blockCount_mul_localDimension
    {r d b e : ℕ}
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e (Fin d → ZMod r) K) :
    d = b * e := by
  letI : Fact r.Prime := ⟨P.field_prime⟩
  have hfinrank := LinearEquiv.finrank_eq P.coordinates
  calc
    d = Module.finrank (ZMod r) (Fin b → Fin e → ZMod r) := by
      simpa [Module.finrank_fin_fun] using hfinrank
    _ = ∑ _i : Fin b,
          Module.finrank (ZMod r) (Fin e → ZMod r) :=
      Module.finrank_pi_fintype (ZMod r)
    _ = b * e := by simp

/-- Every genuine extracted block has strictly smaller dimension than the
ambient irreducible module. -/
theorem localDimension_lt_ambientDimension
    {r d b e : ℕ}
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e (Fin d → ZMod r) K) :
    e < d := by
  rw [P.ambientDimension_eq_blockCount_mul_localDimension]
  exact lt_mul_of_one_lt_left P.localDimension_pos
    P.blockCount_one_lt

/-- The block count is also bounded by the ambient dimension. -/
theorem blockCount_le_ambientDimension
    {r d b e : ℕ}
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e (Fin d → ZMod r) K) :
    b ≤ d := by
  rw [P.ambientDimension_eq_blockCount_mul_localDimension]
  exact Nat.le_mul_of_pos_right b P.localDimension_pos

end PrimeFieldPrimitiveInternalImprimitivityPresentation

/-- A primitive internal presentation together with the strict local
dimension decrease needed by well-founded recursive NCAS. -/
structure StrictPrimeFieldPrimitiveInternalImprimitivityPresentation
    (r d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) where
  blockCount : ℕ
  localDimension : ℕ
  presentation : PrimeFieldPrimitiveInternalImprimitivityPresentation
    r blockCount localDimension (Fin d → ZMod r) K
  localDimension_lt : localDimension < d

/-- Every irreducible prime-field action is quasiprimitive or has a fully
coordinated primitive imprimitive presentation whose local dimension is
strictly smaller than the ambient dimension. -/
theorem quasiprimitiveLinearAction_or_strictInternalImprimitivityPresentation
    (r d : ℕ) [Fact r.Prime]
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (hirr : IsIrreducibleLinearAction r d K) :
    IsQuasiprimitiveLinearAction r d K ∨
      Nonempty
        (StrictPrimeFieldPrimitiveInternalImprimitivityPresentation
          r d K) := by
  rcases quasiprimitiveLinearAction_or_internalImprimitivityPresentation
      r d K hirr with hqp | himp
  · exact Or.inl hqp
  · obtain ⟨b, e, P⟩ := himp
    exact Or.inr
      ⟨{
        blockCount := b
        localDimension := e
        presentation := P
        localDimension_lt := P.localDimension_lt_ambientDimension
      }⟩

end LisiSabatini
