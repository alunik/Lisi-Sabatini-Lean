import LisiSabatini.CoprimeNormal

/-!
# Quotients by normal `p`-subgroups

The results in this file are unconditional group-theoretic infrastructure for
lifting Sylow-intersection statements through a quotient.  In particular,
they do not assume or assert an affine lifting theorem.
-/

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe u v

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- Pulling the quotient `p`-core back across a normal `p`-subgroup gives the
original `p`-core. -/
theorem pCore_comap_quotient_mk' {p : ℕ} (N : Subgroup G) [N.Normal]
    (hNp : IsPGroup p N) :
    (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) = pCore p G := by
  apply le_antisymm
  · apply le_pCore
    · apply (pCore_isPGroup p (G ⧸ N)).comap_of_ker_isPGroup
      rwa [QuotientGroup.ker_mk']
    · infer_instance
  · exact Subgroup.map_le_iff_le_comap.mp <|
      le_pCore ((pCore_isPGroup p G).map (QuotientGroup.mk' N))
        (Subgroup.Normal.map (pCore_normal p G) (QuotientGroup.mk' N)
          (QuotientGroup.mk'_surjective N))

/-- Mapping the `p`-core to a quotient by a normal `p`-subgroup gives the
quotient `p`-core. -/
theorem pCore_map_quotient_mk' {p : ℕ} (N : Subgroup G) [N.Normal]
    (hNp : IsPGroup p N) :
    (pCore p G).map (QuotientGroup.mk' N) = pCore p (G ⧸ N) := by
  rw [← Subgroup.map_comap_eq_self_of_surjective
    (QuotientGroup.mk'_surjective N) (pCore p (G ⧸ N)),
    pCore_comap_quotient_mk' N hNp]

/-- A quotient map preserves an intersection once its kernel is contained in
both subgroups. -/
theorem map_inf_quotient_mk' (N H K : Subgroup G) [N.Normal]
    (hNH : N ≤ H) (hNK : N ≤ K) :
    (H ⊓ K).map (QuotientGroup.mk' N) =
      H.map (QuotientGroup.mk' N) ⊓ K.map (QuotientGroup.mk' N) := by
  apply Subgroup.comap_injective (QuotientGroup.mk'_surjective N)
  rw [Subgroup.comap_inf, QuotientGroup.comap_map_mk',
    QuotientGroup.comap_map_mk', QuotientGroup.comap_map_mk']
  simp only [sup_eq_right.mpr hNH, sup_eq_right.mpr hNK,
    sup_eq_right.mpr (le_inf hNH hNK)]

/-- Pulling back the intersection of two quotient images recovers the
intersection, provided the quotient kernel lies in both subgroups. -/
theorem comap_inf_maps_quotient_mk' (N H K : Subgroup G) [N.Normal]
    (hNH : N ≤ H) (hNK : N ≤ K) :
    (H.map (QuotientGroup.mk' N) ⊓ K.map (QuotientGroup.mk' N)).comap
        (QuotientGroup.mk' N) = H ⊓ K := by
  rw [Subgroup.comap_inf, QuotientGroup.comap_map_mk',
    QuotientGroup.comap_map_mk']
  simp only [sup_eq_right.mpr hNH, sup_eq_right.mpr hNK]

/-- Group homomorphisms carry a conjugate subgroup to the corresponding
conjugate of its image.  This uses mathlib's `x P x⁻¹` convention. -/
theorem map_conj_smul (f : G →* H) (x : G) (P : Subgroup G) :
    (MulAut.conj x • P).map f = MulAut.conj (f x) • P.map f := by
  rw [Subgroup.pointwise_smul_def, Subgroup.pointwise_smul_def,
    Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

/-- The image of a conjugated Sylow subgroup is the conjugate of the image
Sylow subgroup. -/
theorem map_sylow_smul_quotient {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P : Sylow p G) (x : G) :
    (((x • P : Sylow p G) : Subgroup G).map (QuotientGroup.mk' N)) =
      (((QuotientGroup.mk' N x) •
        P.mapSurjective (QuotientGroup.mk'_surjective N) :
          Sylow p (G ⧸ N)) : Subgroup (G ⧸ N)) := by
  change (MulAut.conj x • (P : Subgroup G)).map (QuotientGroup.mk' N) =
    MulAut.conj (QuotientGroup.mk' N x) •
      (P : Subgroup G).map (QuotientGroup.mk' N)
  exact map_conj_smul (QuotientGroup.mk' N) x (P : Subgroup G)

/-- Two lifts in the same quotient fibre differ by left multiplication by an
element of the kernel.  The orientation is important for the `x P x⁻¹`
conjugation convention. -/
theorem exists_left_mul_of_quotient_mk'_eq (N : Subgroup G) [N.Normal]
    {x y : G} (hxy : QuotientGroup.mk' N y = QuotientGroup.mk' N x) :
    ∃ n ∈ N, y = n * x := by
  refine ⟨y * x⁻¹, ?_, by simp⟩
  rw [← QuotientGroup.ker_mk' N]
  change QuotientGroup.mk' N (y * x⁻¹) = 1
  rw [map_mul, map_inv, hxy, mul_inv_cancel]

/-- With mathlib's `x P x⁻¹` convention, changing a conjugator within a
quotient fibre is by *left* multiplication.  If `n` lies in `x • P`, then
`(n * x) • P = x • P`. -/
theorem sylow_smul_left_mul_eq_of_mem {p : ℕ} (P : Sylow p G)
    (x n : G) (hn : n ∈ ((x • P : Sylow p G) : Subgroup G)) :
    (n * x) • P = x • P := by
  rw [mul_smul, Sylow.smul_eq_iff_mem_normalizer]
  exact Subgroup.le_normalizer hn

/-- A normal `p`-subgroup supplies the membership hypothesis in
`sylow_smul_left_mul_eq_of_mem` for every Sylow `p`-subgroup. -/
theorem sylow_smul_left_mul_eq_of_normalPSubgroup {p : ℕ}
    (N : Subgroup G) (hNn : N.Normal) (hNp : IsPGroup p N)
    (P : Sylow p G) (x : G) {n : G} (hn : n ∈ N) :
    (n * x) • P = x • P :=
  sylow_smul_left_mul_eq_of_mem P x n
    (normalPSubgroup_le_sylow hNp hNn (x • P) hn)

/-- Consequently the Sylow intersection itself is unchanged by the same
left-multiplication at the kernel prime. -/
theorem sylowInter_left_mul_eq_of_normalPSubgroup {p : ℕ}
    (N : Subgroup G) (hNn : N.Normal) (hNp : IsPGroup p N)
    (P : Sylow p G) (x : G) {n : G} (hn : n ∈ N) :
    sylowInter P (n * x) = sylowInter P x := by
  rw [sylowInter, sylowInter,
    sylow_smul_left_mul_eq_of_normalPSubgroup N hNn hNp P x hn]

/-- A Sylow intersection maps exactly to the corresponding Sylow intersection
in a quotient when the kernel lies in both Sylow subgroups. -/
theorem sylowInter_map_quotient_mk' {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P : Sylow p G) (x : G)
    (hNP : N ≤ (P : Subgroup G))
    (hNPx : N ≤ ((x • P : Sylow p G) : Subgroup G)) :
    (sylowInter P x).map (QuotientGroup.mk' N) =
      sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) := by
  rw [sylowInter, map_inf_quotient_mk' N _ _ hNP hNPx,
    map_sylow_smul_quotient N P x]
  rfl

/-- Pulling the quotient Sylow intersection back recovers the original one
when the kernel lies in both Sylow subgroups. -/
theorem sylowInter_comap_quotient_mk' {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P : Sylow p G) (x : G)
    (hNP : N ≤ (P : Subgroup G))
    (hNPx : N ≤ ((x • P : Sylow p G) : Subgroup G)) :
    (sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
      (QuotientGroup.mk' N x)).comap (QuotientGroup.mk' N) =
        sylowInter P x := by
  rw [← sylowInter_map_quotient_mk' N P x hNP hNPx]
  exact Subgroup.comap_map_eq_self <| by
    rw [QuotientGroup.ker_mk']
    exact le_inf hNP hNPx

/-- If the quotient kernel is itself a normal `p`-subgroup, its containment in
both Sylow subgroups is automatic. -/
theorem sylowInter_map_quotient_of_normalPSubgroup {p : ℕ}
    [Fact p.Prime] [Finite G] (N : Subgroup G) [N.Normal]
    (hNp : IsPGroup p N) (P : Sylow p G) (x : G) :
    (sylowInter P x).map (QuotientGroup.mk' N) =
      sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) :=
  sylowInter_map_quotient_mk' N P x
    (normalPSubgroup_le_sylow hNp inferInstance P)
    (normalPSubgroup_le_sylow hNp inferInstance (x • P))

/-- Pullback form of `sylowInter_map_quotient_of_normalPSubgroup`.  This is
the exact quotient-intersection identity used for the kernel prime. -/
theorem sylowInter_comap_quotient_of_normalPSubgroup {p : ℕ}
    [Fact p.Prime] [Finite G] (N : Subgroup G) [N.Normal]
    (hNp : IsPGroup p N) (P : Sylow p G) (x : G) :
    (sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
      (QuotientGroup.mk' N x)).comap (QuotientGroup.mk' N) =
        sylowInter P x :=
  sylowInter_comap_quotient_mk' N P x
    (normalPSubgroup_le_sylow hNp inferInstance P)
    (normalPSubgroup_le_sylow hNp inferInstance (x • P))

/-- At the kernel prime, equality with the quotient `p`-core lifts to equality
with the original `p`-core.  This is only the single-prime quotient identity;
it makes no affine or synchronized lifting claim. -/
theorem sylowInter_eq_pCore_of_quotient_eq {p : ℕ}
    [Fact p.Prime] [Finite G] (N : Subgroup G) [N.Normal]
    (hNp : IsPGroup p N) (P : Sylow p G) (x : G)
    (hquot :
      sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) = pCore p (G ⧸ N)) :
    sylowInter P x = pCore p G := by
  calc
    sylowInter P x =
        (sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x)).comap (QuotientGroup.mk' N) :=
      (sylowInter_comap_quotient_of_normalPSubgroup N hNp P x).symm
    _ = (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) :=
      congrArg (fun K : Subgroup (G ⧸ N) ↦ K.comap (QuotientGroup.mk' N)) hquot
    _ = pCore p G := pCore_comap_quotient_mk' N hNp

end LisiSabatini
