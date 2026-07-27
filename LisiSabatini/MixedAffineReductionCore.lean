import LisiSabatini.AffineReductionCore
import LisiSabatini.MixedSylowIntersections

/-!
# Mixed-row affine reduction

Two Sylow `p`-subgroups are conjugate.  If `g • P = Q`, then

`P ∩ xQx⁻¹ = P ∩ (xg)P(xg)⁻¹`.

Thus an independently prescribed second Sylow row changes only the base
conjugator in the existing same-row affine-fibre theorem.  This file records
the exact intersection and quotient transports and derives the mixed
one-prime affine reduction without duplicating its group-theoretic core.
-/

noncomputable section

namespace LisiSabatini

universe uG

variable {G : Type uG} [Group G]

/-! ## Row-conjugator transport -/

/-- Replacing the second Sylow row by a conjugate of the first turns a mixed
intersection into an ordinary same-row Sylow intersection. -/
theorem mixedSylowInter_eq_sylowInter_mul_of_smul_eq
    {p : ℕ} (P Q : Sylow p G) (g x : G) (hg : g • P = Q) :
    mixedSylowInter P Q x = sylowInter P (x * g) := by
  rw [mixedSylowInter, sylowInter, mul_smul, hg]

/-- Every mixed Sylow intersection admits the same-row presentation used by
the existing affine reduction. -/
theorem exists_smul_eq_and_mixedSylowInter_eq_sylowInter_mul
    {p : ℕ} [Fact p.Prime] [Finite G] (P Q : Sylow p G) :
    ∃ g : G, g • P = Q ∧
      ∀ x : G, mixedSylowInter P Q x = sylowInter P (x * g) := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  exact ⟨g, hg, fun x ↦
    mixedSylowInter_eq_sylowInter_mul_of_smul_eq P Q g x hg⟩

/-- A row conjugator descends to the quotient conjugator between the mapped
Sylow rows. -/
theorem mapSurjective_smul_eq_of_smul_eq
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q : Sylow p G) (g : G)
    (hg : g • P = Q) :
    (QuotientGroup.mk' N g) •
        P.mapSurjective (QuotientGroup.mk'_surjective N) =
      Q.mapSurjective (QuotientGroup.mk'_surjective N) := by
  apply Sylow.ext
  calc
    (((QuotientGroup.mk' N g) •
        P.mapSurjective (QuotientGroup.mk'_surjective N) :
          Sylow p (G ⧸ N)) : Subgroup (G ⧸ N)) =
        (((g • P : Sylow p G) : Subgroup G).map
          (QuotientGroup.mk' N)) :=
      (map_sylow_smul_quotient N P g).symm
    _ = ((Q : Subgroup G).map (QuotientGroup.mk' N)) := by rw [hg]
    _ = (Q.mapSurjective (QuotientGroup.mk'_surjective N) :
        Subgroup (G ⧸ N)) := rfl

/-- Exact quotient transport: after a row conjugator `g` is chosen, the
mixed quotient intersection at `x` is the same-row quotient intersection at
`x * g`. -/
theorem sylowInter_quotient_mul_eq_mixedSylowInter_of_smul_eq
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q : Sylow p G) (g x : G)
    (hg : g • P = Q) :
    sylowInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N (x * g)) =
      mixedSylowInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) := by
  rw [map_mul]
  exact
    (mixedSylowInter_eq_sylowInter_mul_of_smul_eq
      (P.mapSurjective (QuotientGroup.mk'_surjective N))
      (Q.mapSurjective (QuotientGroup.mk'_surjective N))
      (QuotientGroup.mk' N g) (QuotientGroup.mk' N x)
      (mapSurjective_smul_eq_of_smul_eq N P Q g hg)).symm

/-! ## Exact quotient and exceptional-prime lifts -/

/-- A mixed Sylow intersection maps exactly to the corresponding mixed
intersection in a quotient when the quotient kernel lies in both rows. -/
theorem mixedSylowInter_map_quotient_mk'
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q : Sylow p G) (x : G)
    (hNP : N ≤ (P : Subgroup G))
    (hNQx : N ≤ ((x • Q : Sylow p G) : Subgroup G)) :
    (mixedSylowInter P Q x).map (QuotientGroup.mk' N) =
      mixedSylowInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) := by
  rw [mixedSylowInter, mixedSylowInter,
    map_inf_quotient_mk' N _ _ hNP hNQx,
    map_sylow_smul_quotient N Q x]
  rfl

/-- Pulling a mixed quotient intersection back recovers the original mixed
intersection when the quotient kernel lies in both rows. -/
theorem mixedSylowInter_comap_quotient_mk'
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P Q : Sylow p G) (x : G)
    (hNP : N ≤ (P : Subgroup G))
    (hNQx : N ≤ ((x • Q : Sylow p G) : Subgroup G)) :
    (mixedSylowInter
        (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x)).comap (QuotientGroup.mk' N) =
      mixedSylowInter P Q x := by
  rw [← mixedSylowInter_map_quotient_mk' N P Q x hNP hNQx]
  exact Subgroup.comap_map_eq_self <| by
    rw [QuotientGroup.ker_mk']
    exact le_inf hNP hNQx

/-- At the kernel prime, an exact mixed quotient equality lifts to the
ambient `p`-core.  The proof is the same-row quotient theorem after the
row-conjugator transport. -/
theorem mixedSylowInter_eq_pCore_of_quotient_eq
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (hNp : IsPGroup p N)
    (P Q : Sylow p G) (x : G)
    (hquot :
      mixedSylowInter
          (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x) =
        pCore p (G ⧸ N)) :
    mixedSylowInter P Q x = pCore p G := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  rw [mixedSylowInter_eq_sylowInter_mul_of_smul_eq P Q g x hg]
  apply sylowInter_eq_pCore_of_quotient_eq N hNp P (x * g)
  exact
    (sylowInter_quotient_mul_eq_mixedSylowInter_of_smul_eq
      N P Q g x hg).trans hquot

/-- The mixed `2`-primary coordinate is automatic in a finite odd-order
group, even for independently prescribed rows. -/
theorem mixedSylowInter_eq_pCore_of_eq_two
    [Finite G] (hodd : Odd (Nat.card G))
    {p : ℕ} (hp : p = 2) (P Q : Sylow p G) (x : G) :
    mixedSylowInter P Q x = pCore p G := by
  subst p
  rw [mixedSylowInter, pCore_two_eq_bot hodd,
    sylow_two_eq_bot hodd P, sylow_two_eq_bot hodd (x • Q)]
  simp

namespace ElementaryAbelianSection

/-! ## Mixed affine fibre reduction -/

/-- Exact mixed one-prime affine fibre reduction.  The independently
prescribed second row is absorbed into a fixed row conjugator; the existing
same-row theorem then supplies the affine translation in the section. -/
theorem exists_translation_mixedSylowInter_eq_pCore_iff_regular
    {p : ℕ} [Fact p.Prime] [Finite G]
    (S : ElementaryAbelianSection G) [S.N.Normal]
    (P Q : Sylow p G) (x : G) (hpr : p ≠ S.r)
    (hquot :
      mixedSylowInter
          (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N x) =
        pCore p (G ⧸ S.N)) :
    ∃ t : S.N, ∀ n : S.N,
      mixedSylowInter P Q ((n : G) * x) = pCore p G ↔
        MulAction.stabilizer
          (S.restrictedConjugation
            ((P : Subgroup G) ⊓
              (pCore p (G ⧸ S.N)).comap
                (QuotientGroup.mk' S.N))).range
          (S.coordinates (Additive.ofMul (n * t))) = ⊥ := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  have hquot' :
      sylowInter
          (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N (x * g)) =
        pCore p (G ⧸ S.N) :=
    (sylowInter_quotient_mul_eq_mixedSylowInter_of_smul_eq
      S.N P Q g x hg).trans hquot
  obtain ⟨t, ht⟩ :=
    S.exists_translation_sylowInter_eq_pCore_iff_regular
      P (x * g) hpr hquot'
  refine ⟨t, fun n ↦ ?_⟩
  rw [mixedSylowInter_eq_sylowInter_mul_of_smul_eq
    P Q g ((n : G) * x) hg]
  simpa only [mul_assoc] using ht n

end ElementaryAbelianSection

end LisiSabatini
