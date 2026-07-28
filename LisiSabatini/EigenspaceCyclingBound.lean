module

public import LisiSabatini.ActiveFixedSpaceSpectrum
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.LinearAlgebra.Eigenspace.Basic

/-!
# Fixed-space bounds from cycling distinct eigenspaces

The representation-theoretic extraspecial argument ultimately uses one
elementary linear-algebra fact.  If a fixed subspace is carried isomorphically
onto `q` eigenspaces with distinct eigenvalues, those eigenspaces are
independent, so `q` times the fixed-space dimension is at most the ambient
dimension.  This file packages that fact independently of any group
classification.

The prime-field corollary is stated in exactly the cardinal form required by
the extraspecial prime-core row interface.  A later group-theoretic argument
only has to construct the eigenvalue cycle and its linear equivalences.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uK uV uI

open scoped DirectSum

/-- The underlying endomorphism of an invertible linear map. -/
abbrev generalLinearEnd
    {K : Type uK} {V : Type uV}
    [Semiring K] [AddCommMonoid V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) : Module.End K V :=
  Units.coeHom (Module.End K V) g

/-- Distinct, linearly equivalent eigenspaces fit independently in the
ambient finite-dimensional vector space. -/
theorem fintype_card_mul_finrank_le_of_equiv_eigenspaces
    {K : Type uK} {V : Type uV} {I : Type uI}
    [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Fintype I]
    (f : Module.End K V) (μ : I → K) (hμ : Function.Injective μ)
    (W : Submodule K V)
    (copies : ∀ i, W ≃ₗ[K] f.eigenspace (μ i)) :
    Fintype.card I * Module.finrank K W ≤ Module.finrank K V := by
  classical
  let E : I → Submodule K V := fun i ↦ f.eigenspace (μ i)
  have hind : iSupIndep E := f.eigenspaces_iSupIndep.comp hμ
  let inclusion : (⨁ i : I, E i) →ₗ[K] V :=
    DirectSum.coeLinearMap E
  have hinjective : Function.Injective inclusion := by
    exact hind.dfinsupp_lsum_injective
  have hfinrank := LinearMap.finrank_le_finrank_of_injective hinjective
  have hdim : ∀ i, Module.finrank K (E i) = Module.finrank K W := by
    intro i
    exact (copies i).finrank_eq.symm
  calc
    Fintype.card I * Module.finrank K W =
        ∑ _i : I, Module.finrank K W := by simp
    _ = ∑ i : I, Module.finrank K (E i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (hdim i).symm
    _ = Module.finrank K (⨁ i : I, E i) := by
      rw [Module.finrank_directSum]
    _ ≤ Module.finrank K V := hfinrank

/-- Prime-field cardinal form of the eigenspace-cycling estimate.  The
caller supplies `q` distinct eigenvalues and equivalences from the fixed
space of `g` to their eigenspaces. -/
theorem ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_eigenspace_copies
    {r d q : ℕ} [Fact r.Prime]
    (hq : 0 < q)
    (g : LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))
    (μ : Fin q → ZMod r) (hμ : Function.Injective μ)
    (copies : ∀ i,
      fixedSpace g ≃ₗ[ZMod r]
        (generalLinearEnd g).eigenspace (μ i)) :
    (nonzeroFixedVectorSet g).ncard ≤ r ^ (d / q) - 1 := by
  have hmul : q * Module.finrank (ZMod r) (fixedSpace g) ≤ d := by
    have h := fintype_card_mul_finrank_le_of_equiv_eigenspaces
      (generalLinearEnd g) μ hμ (fixedSpace g) copies
    simpa [Module.finrank_fin_fun] using h
  have hdim : Module.finrank (ZMod r) (fixedSpace g) ≤ d / q := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa [Nat.mul_comm] using hmul
  rw [ncard_nonzeroFixedVectorSet_eq_pow_finrank_sub_one_zmod]
  exact Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (Fact.out : r.Prime).pos hdim) 1

end LisiSabatini
