module

public import LisiSabatini.NormalComponentReductionCore
public import LisiSabatini.SylowCoreAttainment

/-!
# Individual regular vectors from Sylow-core attainment

Property (*) is needed here only for the ambient group, at the prime under
consideration. A witness for that property gives a regular vector for the
normal component extracted over any elementary-abelian normal subgroup.
There is no assumption that this witness is good in the quotient.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe uG

variable {G : Type uG} [Group G]

/-- Canonical Sylow sections over a quotient core are conjugate inside the
kernel for every ambient conjugator. The quotient witness hypothesis of the
older affine lifting lemma is not needed for this conjugacy statement. -/
theorem exists_kernel_conjugator_quotientCore_sections_of_any_conjugator
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (hNr : IsPGroup r N) (hpr : p ≠ r)
    (P : Sylow p G) (x : G) :
    ∃ t ∈ N,
      (((x • P : Sylow p G) : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) =
        MulAut.conj t •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) := by
  let L := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)
  let A : Subgroup G := (P : Subgroup G) ⊓ L
  let B : Subgroup G := ((x • P : Sylow p G) : Subgroup G) ⊓ L
  have himageP : pCore p (G ⧸ N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' N) := by
    simpa only [Sylow.coe_mapSurjective] using
      pCore_le_sylow (P.mapSurjective (QuotientGroup.mk'_surjective N))
  have himagePx : pCore p (G ⧸ N) ≤
      (((x • P : Sylow p G) : Subgroup G).map (QuotientGroup.mk' N)) := by
    simpa only [Sylow.coe_mapSurjective] using
      pCore_le_sylow ((x • P).mapSurjective (QuotientGroup.mk'_surjective N))
  let PA : Sylow p L := quotientCoreSectionSylow N hNr hpr P himageP
  let PB : Sylow p L := quotientCoreSectionSylow N hNr hpr (x • P) himagePx
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L PA PB
  have hlsub : MulAut.conj l • (PA : Subgroup L) = (PB : Subgroup L) := by
    change (((l • PA : Sylow p L) : Subgroup L)) = (PB : Subgroup L)
    exact congrArg (fun Q : Sylow p L ↦ (Q : Subgroup L)) hl
  have hlsections : MulAut.conj l • A.subgroupOf L = B.subgroupOf L := by
    simpa [PA, PB, A, B, L] using hlsub
  have hlambient : MulAut.conj (l : G) • A = B := by
    have hmap := congrArg (fun K : Subgroup L ↦ K.map L.subtype) hlsections
    simpa [map_conj_smul, Subgroup.map_subgroupOf_eq_of_le, A, B, L] using hmap
  obtain ⟨a, haP, haeq⟩ := himageP l.2
  have haL : a ∈ L := by
    change QuotientGroup.mk' N a ∈ pCore p (G ⧸ N)
    rw [haeq]
    exact l.2
  have haA : a ∈ A := ⟨haP, haL⟩
  let t : G := (l : G) * a⁻¹
  have htN : t ∈ N := by
    apply (QuotientGroup.eq_one_iff t).mp
    change QuotientGroup.mk' N ((l : G) * a⁻¹) = 1
    rw [map_mul, map_inv, haeq, mul_inv_cancel]
  refine ⟨t, htN, ?_⟩
  change B = MulAut.conj t • A
  calc
    B = MulAut.conj (l : G) • A := hlambient.symm
    _ = MulAut.conj (t * a) • A := by congr 2; simp [t]
    _ = MulAut.conj t • (MulAut.conj a • A) := by rw [← mul_smul, map_mul]
    _ = MulAut.conj t • A := by rw [Subgroup.conj_smul_eq_self_of_mem haA]

namespace ElementaryAbelianSection

/-- Individual Sylow-core attainment supplies a regular vector for the
faithful action of the canonical complement over the quotient core. -/
theorem exists_regular_quotientCore_range_of_sylowCoreAttainment
    [Finite G] (S : ElementaryAbelianSection G) [S.N.Normal]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hpr : p ≠ S.r)
    (hstar : SylowCoreAttainmentAt p G) :
    ∃ v : Fin S.d → ZMod S.r,
      MulAction.stabilizer
        (S.restrictedConjugation (S.quotientCoreComplement P)).range v = ⊥ := by
  let : Fact S.r.Prime := ⟨S.prime⟩
  let L := S.quotientCorePullback p
  let A := S.quotientCoreComplement P
  obtain ⟨x, hx⟩ := hstar P
  let B : Subgroup G := ((x • P : Sylow p G) : Subgroup G) ⊓ L
  have himage : pCore p (G ⧸ S.N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' S.N) := by
    simpa only [Sylow.coe_mapSurjective] using
      pCore_le_sylow (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
  have hmapCore : (pCore p G).map (QuotientGroup.mk' S.N) ≤
      pCore p (G ⧸ S.N) :=
    le_pCore ((pCore_isPGroup p G).map (QuotientGroup.mk' S.N))
      (Subgroup.Normal.map (pCore_normal p G) (QuotientGroup.mk' S.N)
        (QuotientGroup.mk'_surjective S.N))
  have hcoreL : pCore p G ≤ L := Subgroup.map_le_iff_le_comap.mp hmapCore
  have hAB : A ⊓ B = pCore p G := by
    apply le_antisymm
    · exact (inf_le_inf inf_le_left inf_le_left).trans hx.le
    · exact le_inf (le_inf (pCore_le_sylow P) hcoreL)
        (le_inf (pCore_le_sylow (x • P)) hcoreL)
  obtain ⟨t, htN, ht⟩ :=
    exists_kernel_conjugator_quotientCore_sections_of_any_conjugator
      S.N S.isPGroup_N hpr P x
  change B = MulAut.conj t • A at ht
  rw [ht] at hAB
  have hAN : Disjoint A S.N :=
    pSubgroups_disjoint_of_ne hpr P.isPGroup'.to_inf_left S.isPGroup_N
  have hcore : pCore p G = (S.restrictedConjugation A).ker.map A.subtype :=
    S.pCore_eq_map_restrictedConjugation_ker_quotientCore P hpr himage
  refine ⟨S.coordinates (Additive.ofMul (⟨t, htN⟩ : S.N)), ?_⟩
  exact (S.inf_conjugate_complement_eq_pCore_iff_range_stabilizer_eq_bot
    A hAN ⟨t, htN⟩ hcore).mp hAB

/-- Common-action form of the individual regular-vector extraction. -/
theorem exists_regular_normalComponent_of_sylowCoreAttainment
    [Finite G] (S : ElementaryAbelianSection G) [S.N.Normal]
    {p : ℕ} [Fact p.Prime] (P : Sylow p G) (hpr : p ≠ S.r)
    (hstar : SylowCoreAttainmentAt p G) :
    ∃ v : Fin S.d → ZMod S.r,
      MulAction.stabilizer ((S.normalComponent P).map S.commonAction.subtype) v = ⊥ := by
  rw [S.localImage_ambient_eq_restrictedConjugation_range P]
  exact S.exists_regular_quotientCore_range_of_sylowCoreAttainment P hpr hstar

end ElementaryAbelianSection

end LisiSabatini
