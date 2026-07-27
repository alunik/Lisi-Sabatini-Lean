import LisiSabatini.MixedAffineReductionCore
import LisiSabatini.NormalComponentReductionCore
import LisiSabatini.ThreeConjugatesSynchronization

/-!
# Mixed-row normal-component reduction

This file combines the exact mixed affine-fibre reduction with the existing
normal-component affine synchronization predicate.  It proves that, for a
finite odd-order group with a normal elementary-abelian section, mixed
two-row Sylow-core synchronization lifts from the quotient.

The first prescribed Sylow row determines each normal local component in the
common conjugation action.  The independently prescribed second row changes
only the affine translation supplied by the mixed fibre theorem.
-/

noncomputable section

namespace LisiSabatini

universe uG uI

variable {G : Type uG} [Group G]

namespace ElementaryAbelianSection

/-- An exact mixed quotient intersection contains the quotient `p`-core in
the image of its first prescribed Sylow row.  This is the input needed to
make the corresponding local action image a normal component. -/
theorem quotientCore_le_sylow_map_of_mixedSylowInter_eq
    (S : ElementaryAbelianSection G) [S.N.Normal] [Finite G]
    {p : ℕ} [Fact p.Prime] (P Q : Sylow p G) (x : G)
    (hquot :
      mixedSylowInter
          (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N x) =
        pCore p (G ⧸ S.N)) :
    pCore p (G ⧸ S.N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' S.N) := by
  intro y hy
  have hy' : y ∈
      mixedSylowInter
        (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
        (Q.mapSurjective (QuotientGroup.mk'_surjective S.N))
        (QuotientGroup.mk' S.N x) := by
    rw [hquot]
    exact hy
  exact hy'.1

/-- Elementary-abelian lifting for independently prescribed Sylow rows.

In the cross-characteristic coordinates, the existing normal-component
affine synchronization theorem selects one common section translation.  The
`p = 2` coordinates are automatic by odd order, while the section-prime
coordinates lift by the exact mixed quotient identity for a normal
`p`-subgroup. -/
theorem mixedTwoSylowCoreSynchronization_lift_normalComponents
    (S : ElementaryAbelianSection G) [S.N.Normal] [Finite G]
    (hodd : Odd (Nat.card G))
    (hquot :
      HasMixedTwoSylowCoreSynchronization.{uG, uI} (G ⧸ S.N))
    (hNCAS : NormalComponentAffineSynchronization.{uI}
      S.r S.d S.commonAction) :
    HasMixedTwoSylowCoreSynchronization.{uG, uI} G := by
  intro I _ p hp hinj P Q
  let Pbar : ∀ i, Sylow (p i) (G ⧸ S.N) := fun i ↦ by
    letI : Fact (p i).Prime := ⟨hp i⟩
    exact (P i).mapSurjective (QuotientGroup.mk'_surjective S.N)
  let Qbar : ∀ i, Sylow (p i) (G ⧸ S.N) := fun i ↦ by
    letI : Fact (p i).Prime := ⟨hp i⟩
    exact (Q i).mapSurjective (QuotientGroup.mk'_surjective S.N)
  obtain ⟨xbar, hxbar⟩ := hquot p hp hinj Pbar Qbar
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective S.N xbar
  have hxquot (i : I) :
      mixedSylowInter (Pbar i) (Qbar i)
          (QuotientGroup.mk' S.N x) =
        pCore (p i) (G ⧸ S.N) := by
    rw [hx]
    exact hxbar i
  let J := {i : I // p i ≠ 2 ∧ p i ≠ S.r}
  let H : J → Subgroup S.commonAction := fun j ↦
    S.normalComponent (P j.1)
  let localData := fun j : J ↦ by
    letI : Fact (p j.1).Prime := ⟨hp j.1⟩
    exact S.exists_translation_mixedSylowInter_eq_pCore_iff_regular
      (P j.1) (Q j.1) x j.2.2 (hxquot j.1)
  let t : J → S.N := fun j ↦ Classical.choose (localData j)
  have ht (j : J) := Classical.choose_spec (localData j)
  have himage (j : J) : pCore (p j.1) (G ⧸ S.N) ≤
      (P j.1 : Subgroup G).map (QuotientGroup.mk' S.N) := by
    letI : Fact (p j.1).Prime := ⟨hp j.1⟩
    exact S.quotientCore_le_sylow_map_of_mixedSylowInter_eq
      (P j.1) (Q j.1) x (hxquot j.1)
  have hpJ (j : J) : Nat.Prime (p j.1) := hp j.1
  have hinjJ : Function.Injective (fun j : J ↦ p j.1) := by
    intro i j hij
    apply Subtype.ext
    exact hinj hij
  have hnormal (j : J) : (H j).Normal := by
    dsimp [H]
    exact S.localImage_normal (P j.1) (himage j)
  have hHp (j : J) : IsPGroup (p j.1) (H j) := by
    dsimp [H]
    exact S.localImage_isPGroup (P j.1)
  obtain ⟨v, hv⟩ := hNCAS (fun j : J ↦ p j.1) hpJ hinjJ
    (fun j ↦ j.2.1) (fun j ↦ j.2.2) H hnormal hHp
    (fun j ↦ S.coordinates (Additive.ofMul (t j)))
  let n : S.N := Additive.toMul (S.coordinates.symm v)
  refine ⟨(n : G) * x, fun i ↦ ?_⟩
  by_cases hiTwo : p i = 2
  · exact mixedSylowInter_eq_pCore_of_eq_two
      hodd hiTwo (P i) (Q i) ((n : G) * x)
  by_cases hiSection : p i = S.r
  · letI : Fact (p i).Prime := ⟨hp i⟩
    have hNp : IsPGroup (p i) S.N := by
      simpa [hiSection] using S.isPGroup_N
    apply mixedSylowInter_eq_pCore_of_quotient_eq
      S.N hNp (P i) (Q i) ((n : G) * x)
    have hmn : QuotientGroup.mk' S.N (n : G) = 1 :=
      (QuotientGroup.eq_one_iff (n : G)).mpr n.2
    simpa [map_mul, hmn] using hxquot i
  · let j : J := ⟨i, hiTwo, hiSection⟩
    apply (ht j n).mpr
    have hvj := hv j
    dsimp [H] at hvj
    rw [S.localImage_ambient_eq_restrictedConjugation_range
      (P j.1)] at hvj
    simpa [t, n, quotientCoreComplement, quotientCorePullback] using hvj

end ElementaryAbelianSection

end LisiSabatini
