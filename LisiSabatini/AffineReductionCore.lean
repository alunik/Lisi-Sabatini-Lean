import LisiSabatini.CoprimeNormal
import LisiSabatini.ElementarySection
import LisiSabatini.OddOrder
import LisiSabatini.Quotient
import LisiSabatini.Strong

/-!
# The group-theoretic affine reduction

This file isolates the part of the elementary-abelian lifting argument which
does not depend on a dimension bound or on counting regular vectors.

If `N` is normal and a subgroup `A` is disjoint from `N`, then conjugating
`A` by `n ∈ N` cuts `A` down exactly to the elements centralizing `n`.
After elementary-abelian coordinates are chosen, this is the point stabilizer
for the restricted linear conjugation action.  The action kernel is the
pointwise centralizer of `N`; consequently equality with that kernel is
equivalent to regularity in the faithful action image.
-/

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe uG uI

variable {G : Type uG} [Group G]

namespace ElementaryAbelianSection

/-- Restrict the conjugation representation of a section to a subgroup. -/
def restrictedConjugation (S : ElementaryAbelianSection G) (A : Subgroup G) :
    A →* LinearMap.GeneralLinearGroup (ZMod S.r) (Fin S.d → ZMod S.r) :=
  S.conjugation.comp A.subtype

@[simp]
theorem restrictedConjugation_apply (S : ElementaryAbelianSection G)
    (A : Subgroup G) (a : A) :
    S.restrictedConjugation A a = S.conjugation (a : G) :=
  rfl

end ElementaryAbelianSection

/-- Membership in a conjugate of a complement is equivalent to centralizing
the conjugating element.  The conjugate is `n A n⁻¹`, in agreement with
mathlib's pointwise-conjugation convention. -/
theorem mem_conjugate_complement_iff_commute
    (N A : Subgroup G) (hN : N.Normal) (hAN : Disjoint A N)
    {n a : G} (hn : n ∈ N) (ha : a ∈ A) :
    a ∈ (MulAut.conj n • A) ↔ Commute a n := by
  constructor
  · intro haConj
    have ha' : n⁻¹ * a * n ∈ A := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at haConj
      simpa [MulAut.conj_apply, mul_assoc] using haConj
    have hdiffA : (n⁻¹ * a * n) * a⁻¹ ∈ A := A.mul_mem ha' (A.inv_mem ha)
    have hdiffN : (n⁻¹ * a * n) * a⁻¹ ∈ N := by
      simpa only [mul_assoc] using
        N.mul_mem (N.inv_mem hn) (hN.conj_mem n hn a)
    have hdiff : (n⁻¹ * a * n) * a⁻¹ = 1 :=
      Subgroup.disjoint_def.mp hAN hdiffA hdiffN
    have heq : n⁻¹ * (a * n) = a := by
      simpa only [mul_assoc] using mul_inv_eq_one.mp hdiff
    exact inv_mul_eq_iff_eq_mul.mp heq
  · intro han
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    have hconj : n⁻¹ * a * n = a := by
      calc
        n⁻¹ * a * n = n⁻¹ * (a * n) := by rw [mul_assoc]
        _ = n⁻¹ * (n * a) := by rw [han.eq]
        _ = a := by simp
    simpa [MulAut.conj_apply, mul_assoc, hconj] using ha

/-- Subgroup form of `mem_conjugate_complement_iff_commute`. -/
theorem inf_conjugate_complement_eq_inf_centralizer
    (N A : Subgroup G) (hN : N.Normal) (hAN : Disjoint A N)
    {n : G} (hn : n ∈ N) :
    A ⊓ (MulAut.conj n • A) = A ⊓ Subgroup.centralizer {n} := by
  ext a
  constructor
  · rintro ⟨ha, haConj⟩
    refine ⟨ha, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact (mem_conjugate_complement_iff_commute N A hN hAN hn ha).mp haConj
  · rintro ⟨ha, haCent⟩
    refine ⟨ha, (mem_conjugate_complement_iff_commute N A hN hAN hn ha).mpr ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp haCent

/-- Left multiplication of a conjugator becomes left conjugation of the
already-conjugated Sylow subgroup. -/
theorem sylowInter_left_mul_eq_inf_conj_smul {p : ℕ}
    (P : Sylow p G) (x n : G) :
    sylowInter P (n * x) =
      (P : Subgroup G) ⊓
        (MulAut.conj n • (((x • P : Sylow p G) : Subgroup G))) := by
  rw [sylowInter, mul_smul, Sylow.coe_subgroup_smul]

/-- Dependent-index wrapper for the automatic two-primary coordinate in an
odd-order group. -/
theorem sylowInter_eq_pCore_of_eq_two [Finite G]
    (hodd : Odd (Nat.card G)) {p : ℕ} (hp : p = 2)
    (P : Sylow p G) (x : G) : sylowInter P x = pCore p G := by
  subst p
  exact sylowInter_two_eq_pCore hodd P x

/-- If an intersection is already contained in a normal subgroup `L`, it can
be computed after cutting both factors down to `L`. -/
theorem inf_conj_smul_eq_inf_sections_of_le
    (P B L : Subgroup G) (hL : L.Normal) (n : G)
    (hle : P ⊓ (MulAut.conj n • B) ≤ L) :
    P ⊓ (MulAut.conj n • B) =
      (P ⊓ L) ⊓ (MulAut.conj n • (B ⊓ L)) := by
  letI : L.Normal := hL
  ext g
  constructor
  · intro hg
    have hgL : g ∈ L := hle hg
    refine ⟨⟨hg.1, hgL⟩, ?_⟩
    rw [Subgroup.smul_inf, Subgroup.Normal.conj_smul_eq_self n L]
    exact ⟨hg.2, hgL⟩
  · rintro ⟨⟨hgP, _hgL⟩, hg⟩
    refine ⟨hgP, ?_⟩
    rw [Subgroup.smul_inf, Subgroup.Normal.conj_smul_eq_self n L] at hg
    exact hg.1

/-- A quotient strong witness forces every lift in the same fibre to have
its Sylow intersection inside the pullback of the quotient `p`-core. -/
theorem sylowInter_le_comap_quotient_pCore_of_quotient_eq
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P : Sylow p G) (x : G)
    (hquot :
      sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) = pCore p (G ⧸ N))
    {n : G} (hn : n ∈ N) :
    sylowInter P (n * x) ≤
      (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  intro g hg
  change QuotientGroup.mk' N g ∈ pCore p (G ⧸ N)
  rw [← hquot]
  refine ⟨?_, ?_⟩
  · exact ⟨g, hg.1, rfl⟩
  · have hgmap : QuotientGroup.mk' N g ∈
        (((QuotientGroup.mk' N (n * x)) •
          P.mapSurjective (QuotientGroup.mk'_surjective N) :
            Sylow p (G ⧸ N)) : Subgroup (G ⧸ N)) := by
      rw [← map_sylow_smul_quotient N P (n * x)]
      exact ⟨g, hg.2, rfl⟩
    have hmn : QuotientGroup.mk' N n = 1 := by
      rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact hn
    simpa [map_mul, hmn] using hgmap

/-- A Sylow subgroup whose quotient image contains the quotient `p`-core
cuts the pullback of that core in a Sylow `p`-subgroup.  The proof uses only
the coprimality of the quotient kernel, not a cardinality calculation. -/
noncomputable def quotientCoreSectionSylow
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (N : Subgroup G) [N.Normal] (hNr : IsPGroup r N) (hpr : p ≠ r)
    (P : Sylow p G)
    (himage : pCore p (G ⧸ N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' N)) :
    Sylow p ((pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) := by
  let L := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)
  let A : Subgroup G := (P : Subgroup G) ⊓ L
  have hAL : A ≤ L := inf_le_right
  refine
    { toSubgroup := A.subgroupOf L
      isPGroup' := ?_
      is_maximal' := ?_ }
  · exact (P.isPGroup'.to_inf_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe hAL).symm
  · intro Q hQ hAQ
    apply le_antisymm ?_ hAQ
    intro q hq
    have hqCore : QuotientGroup.mk' N (q : G) ∈ pCore p (G ⧸ N) := q.2
    obtain ⟨a, haP, haeq⟩ := himage hqCore
    have haL : a ∈ L := by
      change QuotientGroup.mk' N a ∈ pCore p (G ⧸ N)
      rw [haeq]
      exact hqCore
    let aL : L := ⟨a, haL⟩
    have haA : aL ∈ A.subgroupOf L := ⟨haP, haL⟩
    have haQ : aL ∈ Q := hAQ haA
    have hdiffN : (q : G) * a⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff ((q : G) * a⁻¹)).mp
      change QuotientGroup.mk' N ((q : G) * a⁻¹) = 1
      rw [map_mul, map_inv, haeq, mul_inv_cancel]
    have hdiffQ : (q : G) * a⁻¹ ∈ Q.map L.subtype := by
      refine ⟨q * aL⁻¹, Q.mul_mem hq (Q.inv_mem haQ), ?_⟩
      rfl
    have hdiff : (q : G) * a⁻¹ = 1 :=
      Subgroup.disjoint_def.mp
        (pSubgroups_disjoint_of_ne hpr (hQ.map L.subtype) hNr)
        hdiffQ hdiffN
    have hqa : (q : G) = a := mul_inv_eq_one.mp hdiff
    have hqP : (q : G) ∈ (P : Subgroup G) := by
      rw [hqa]
      exact haP
    exact ⟨hqP, q.2⟩

@[simp]
theorem coe_quotientCoreSectionSylow
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    (N : Subgroup G) [N.Normal] (hNr : IsPGroup r N) (hpr : p ≠ r)
    (P : Sylow p G)
    (himage : pCore p (G ⧸ N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' N)) :
    (quotientCoreSectionSylow N hNr hpr P himage :
      Subgroup ((pCore p (G ⧸ N)).comap (QuotientGroup.mk' N))) =
      (((P : Subgroup G) ⊓
        (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)).subgroupOf
          ((pCore p (G ⧸ N)).comap (QuotientGroup.mk' N))) :=
  rfl

/-- The quotient-kernel and a section cut out by a Sylow subgroup generate
the full pullback of the quotient `p`-core. -/
theorem sup_inf_comap_quotient_pCore_eq
    {p : ℕ} (N : Subgroup G) [N.Normal] (P : Sylow p G)
    (himage : pCore p (G ⧸ N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' N)) :
    N ⊔ ((P : Subgroup G) ⊓
        (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) =
      (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N) := by
  let L := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)
  apply le_antisymm
  · refine sup_le ?_ inf_le_right
    intro n hn
    change QuotientGroup.mk' N n ∈ pCore p (G ⧸ N)
    have hmn : QuotientGroup.mk' N n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr hn
    rw [hmn]
    exact Subgroup.one_mem _
  · intro l hl
    obtain ⟨a, haP, haeq⟩ := himage hl
    have haL : a ∈ L := by
      change QuotientGroup.mk' N a ∈ pCore p (G ⧸ N)
      rw [haeq]
      exact hl
    have hnN : l * a⁻¹ ∈ N := by
      apply (QuotientGroup.eq_one_iff (l * a⁻¹)).mp
      change QuotientGroup.mk' N (l * a⁻¹) = 1
      rw [map_mul, map_inv, haeq, mul_inv_cancel]
    rw [Subgroup.mem_sup_of_normal_left]
    exact ⟨l * a⁻¹, hnN, a, ⟨haP, haL⟩, by simp⟩

/-- The two complement sections selected by a quotient strong witness are
conjugate by an element of the quotient kernel.  This is the precise Sylow
conjugacy input used to manufacture the affine translation `t`. -/
theorem exists_kernel_conjugator_quotientCore_sections
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (hNr : IsPGroup r N) (hpr : p ≠ r)
    (P : Sylow p G) (x : G)
    (hquot :
      sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) = pCore p (G ⧸ N)) :
    ∃ t ∈ N,
      (((x • P : Sylow p G) : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) =
        MulAut.conj t •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) := by
  let L := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)
  let A : Subgroup G := (P : Subgroup G) ⊓ L
  let B : Subgroup G :=
    ((x • P : Sylow p G) : Subgroup G) ⊓ L
  have himageP : pCore p (G ⧸ N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' N) := by
    intro y hy
    have hy' : y ∈
        sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x) := by
      rw [hquot]
      exact hy
    exact hy'.1
  have himagePx : pCore p (G ⧸ N) ≤
      (((x • P : Sylow p G) : Subgroup G).map
        (QuotientGroup.mk' N)) := by
    intro y hy
    have hy' : y ∈
        sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
          (QuotientGroup.mk' N x) := by
      rw [hquot]
      exact hy
    rw [map_sylow_smul_quotient N P x]
    exact hy'.2
  let PA : Sylow p L := quotientCoreSectionSylow N hNr hpr P himageP
  let PB : Sylow p L :=
    quotientCoreSectionSylow N hNr hpr (x • P) himagePx
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L PA PB
  have hlsub : MulAut.conj l • (PA : Subgroup L) = (PB : Subgroup L) := by
    change (((l • PA : Sylow p L) : Subgroup L)) = (PB : Subgroup L)
    exact congrArg (fun Q : Sylow p L ↦ (Q : Subgroup L)) hl
  have hlsections :
      MulAut.conj l • A.subgroupOf L = B.subgroupOf L := by
    simpa [PA, PB, A, B, L] using hlsub
  have hlambient : MulAut.conj (l : G) • A = B := by
    have hmap := congrArg (fun K : Subgroup L ↦ K.map L.subtype) hlsections
    simpa [map_conj_smul, Subgroup.map_subgroupOf_eq_of_le,
      A, B, L] using hmap
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
    _ = MulAut.conj (t * a) • A := by
      congr 2
      simp [t]
    _ = MulAut.conj t • (MulAut.conj a • A) := by
      rw [← mul_smul, map_mul]
    _ = MulAut.conj t • A := by
      rw [Subgroup.conj_smul_eq_self_of_mem haA]

/-- Exact local affine model extracted from a quotient strong witness.

Here `A = P ∩ L`, while the second complement
`(xPx⁻¹) ∩ L` is assumed to be `tAt⁻¹`.  Sylow conjugacy in `L`
is what supplies `t ∈ N` in the chief-factor application; this lemma
performs all remaining quotient and conjugation bookkeeping. -/
theorem sylowInter_left_mul_eq_complement_translate_of_quotient_eq
    {p : ℕ} [Fact p.Prime] [Finite G]
    (N : Subgroup G) [N.Normal] (P : Sylow p G) (x : G)
    (hquot :
      sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective N))
        (QuotientGroup.mk' N x) = pCore p (G ⧸ N))
    (t : G)
    (hconj :
      (((x • P : Sylow p G) : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) =
        MulAut.conj t •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)))
    {n : G} (hn : n ∈ N) :
    sylowInter P (n * x) =
      ((P : Subgroup G) ⊓
          (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)) ⊓
        (MulAut.conj (n * t) •
          ((P : Subgroup G) ⊓
            (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N))) := by
  let L := (pCore p (G ⧸ N)).comap (QuotientGroup.mk' N)
  have hL : L.Normal := inferInstance
  have hraw :
      (P : Subgroup G) ⊓
          (MulAut.conj n • (((x • P : Sylow p G) : Subgroup G))) ≤ L := by
    rw [← sylowInter_left_mul_eq_inf_conj_smul P x n]
    exact sylowInter_le_comap_quotient_pCore_of_quotient_eq N P x hquot hn
  calc
    sylowInter P (n * x) =
        (P : Subgroup G) ⊓
          (MulAut.conj n • (((x • P : Sylow p G) : Subgroup G))) :=
      sylowInter_left_mul_eq_inf_conj_smul P x n
    _ = ((P : Subgroup G) ⊓ L) ⊓
          (MulAut.conj n •
            ((((x • P : Sylow p G) : Subgroup G)) ⊓ L)) :=
      inf_conj_smul_eq_inf_sections_of_le _ _ L hL n
        hraw
    _ = ((P : Subgroup G) ⊓ L) ⊓
          (MulAut.conj n •
            (MulAut.conj t • ((P : Subgroup G) ⊓ L))) := by
      rw [hconj]
    _ = ((P : Subgroup G) ⊓ L) ⊓
          (MulAut.conj (n * t) • ((P : Subgroup G) ⊓ L)) := by
      rw [← mul_smul, map_mul]

namespace ElementaryAbelianSection

/-- The supplied additive coordinates imply that the section subgroup is
abelian, without requiring a separate `CommGroup` instance on the subtype. -/
theorem commute_N (S : ElementaryAbelianSection G) (n m : S.N) :
    Commute (n : G) (m : G) := by
  have hcoords :
      S.coordinates (Additive.ofMul (n * m)) =
        S.coordinates (Additive.ofMul (m * n)) := by
    simpa using add_comm
      (S.coordinates (Additive.ofMul n))
      (S.coordinates (Additive.ofMul m))
  have hnm : n * m = m * n :=
    Additive.ofMul.injective (S.coordinates.injective hcoords)
  exact congrArg Subtype.val hnm

/-- In elementary-abelian coordinates, fixing a vector represented by
`n ∈ N` is the same thing as commuting with `n` in the ambient group. -/
theorem restrictedConjugation_fixes_coordinates_iff_commute
    (S : ElementaryAbelianSection G) (A : Subgroup G) (a : A) (n : S.N) :
    S.restrictedConjugation A a • S.coordinates (Additive.ofMul n) =
        S.coordinates (Additive.ofMul n) ↔
      Commute (a : G) (n : G) := by
  constructor
  · intro hfix
    have hcompat := S.conjugation_apply (a : G) n
    have hcoords :
        S.coordinates
            (Additive.ofMul (normalConj S.N S.normal (a : G) n)) =
          S.coordinates (Additive.ofMul n) :=
      hcompat.symm.trans hfix
    have hn : normalConj S.N S.normal (a : G) n = n :=
      Additive.ofMul.injective (S.coordinates.injective hcoords)
    have hconj : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := by
      simpa using congrArg Subtype.val hn
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · intro han
    have hconj : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) :=
      mul_inv_eq_iff_eq_mul.mpr han.eq
    have hn : normalConj S.N S.normal (a : G) n = n := by
      apply Subtype.ext
      simpa using hconj
    calc
      S.restrictedConjugation A a • S.coordinates (Additive.ofMul n) =
          S.coordinates
            (Additive.ofMul (normalConj S.N S.normal (a : G) n)) :=
        S.conjugation_apply (a : G) n
      _ = S.coordinates (Additive.ofMul n) := by rw [hn]

/-- The conjugated complement, pulled back to `A`, is exactly the point
stabilizer of the coordinate vector. -/
theorem conjugate_complement_comap_eq_actionPointStabilizer
    (S : ElementaryAbelianSection G) (A : Subgroup G)
    (hAN : Disjoint A S.N) (n : S.N) :
    (MulAut.conj (n : G) • A).comap A.subtype =
      actionPointStabilizer (S.restrictedConjugation A)
        (S.coordinates (Additive.ofMul n)) := by
  ext a
  rw [Subgroup.mem_comap, mem_actionPointStabilizer,
    S.restrictedConjugation_fixes_coordinates_iff_commute A]
  exact mem_conjugate_complement_iff_commute S.N A S.normal hAN n.2 a.2

/-- The intersection `A ∩ nAn⁻¹` is the ambient copy of the point
stabilizer of `n`. -/
theorem map_actionPointStabilizer_eq_inf_conjugate_complement
    (S : ElementaryAbelianSection G) (A : Subgroup G)
    (hAN : Disjoint A S.N) (n : S.N) :
    (actionPointStabilizer (S.restrictedConjugation A)
        (S.coordinates (Additive.ofMul n))).map A.subtype =
      A ⊓ (MulAut.conj (n : G) • A) := by
  rw [← S.conjugate_complement_comap_eq_actionPointStabilizer A hAN n,
    Subgroup.map_comap_eq, Subgroup.range_subtype]

/-- The kernel of the restricted linear action is the pointwise centralizer
of `N`, viewed as a subgroup of `A`. -/
theorem restrictedConjugation_ker_eq_comap_centralizer
    (S : ElementaryAbelianSection G) (A : Subgroup G) :
    (S.restrictedConjugation A).ker =
      (Subgroup.centralizer (S.N : Set G)).comap A.subtype := by
  ext a
  constructor
  · intro ha
    have ha' : (a : G) ∈ S.conjugation.ker := ha
    have hfix := (S.mem_conjugation_ker_iff (a : G)).mp ha'
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro n hn
    let n' : S.N := ⟨n, hn⟩
    have hn' := hfix n'
    have hconj : (a : G) * n * (a : G)⁻¹ = n := by
      simpa [n'] using congrArg Subtype.val hn'
    exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
  · intro ha
    have haCent : (a : G) ∈ Subgroup.centralizer (S.N : Set G) := ha
    have haKer : (a : G) ∈ S.conjugation.ker :=
      (S.mem_conjugation_ker_iff (a : G)).mpr fun n ↦ by
        apply Subtype.ext
        have hcomm : (a : G) * (n : G) = (n : G) * (a : G) :=
          (Subgroup.mem_centralizer_iff.mp haCent (n : G) n.2).symm
        simpa using mul_inv_eq_iff_eq_mul.mpr hcomm
    exact haKer

/-- Ambient form of the kernel/centralizer identity. -/
theorem map_restrictedConjugation_ker_eq_inf_centralizer
    (S : ElementaryAbelianSection G) (A : Subgroup G) :
    (S.restrictedConjugation A).ker.map A.subtype =
      A ⊓ Subgroup.centralizer (S.N : Set G) := by
  rw [S.restrictedConjugation_ker_eq_comap_centralizer A,
    Subgroup.map_comap_eq, Subgroup.range_subtype]

/-- The abstract affine reduction: cutting a complement by its translate is
the action kernel exactly when the corresponding vector is regular for the
faithful action image. -/
theorem inf_conjugate_complement_eq_map_ker_iff_range_stabilizer_eq_bot
    (S : ElementaryAbelianSection G) (A : Subgroup G)
    (hAN : Disjoint A S.N) (n : S.N) :
    A ⊓ (MulAut.conj (n : G) • A) =
        (S.restrictedConjugation A).ker.map A.subtype ↔
      MulAction.stabilizer (S.restrictedConjugation A).range
          (S.coordinates (Additive.ofMul n)) = ⊥ := by
  let ρ := S.restrictedConjugation A
  let v := S.coordinates (Additive.ofMul n)
  have hmap : (actionPointStabilizer ρ v).map A.subtype =
      A ⊓ (MulAut.conj (n : G) • A) :=
    S.map_actionPointStabilizer_eq_inf_conjugate_complement A hAN n
  constructor
  · intro h
    apply (actionPointStabilizer_eq_ker_iff_range_stabilizer_eq_bot ρ v).mp
    exact Subgroup.map_subtype_inj.mp (hmap.trans h)
  · intro h
    have hstab : actionPointStabilizer ρ v = ρ.ker :=
      (actionPointStabilizer_eq_ker_iff_range_stabilizer_eq_bot ρ v).mpr h
    exact hmap.symm.trans (congrArg (fun K : Subgroup A ↦ K.map A.subtype) hstab)

/-- The exponent field of an elementary-abelian section supplies the
`r`-group fact needed by the coprime centralizer lemmas. -/
theorem isPGroup_N (S : ElementaryAbelianSection G) : IsPGroup S.r S.N := by
  intro n
  refine ⟨1, ?_⟩
  simpa using S.exponent_eq_one n

/-- For the canonical complement inside the pullback of a quotient `p`-core,
the ambient copy of the action kernel is normal in `G`.

This discharges the normality hypothesis in
`pCore_eq_map_restrictedConjugation_ker`.  The argument is the internal
direct-product calculation from the paper proof: the centralizer of `N`
inside the pullback is `N` times the action kernel, and coprimality forces the
kernel factor to be invariant under ambient conjugation. -/
theorem map_restrictedConjugation_ker_normal_of_quotientCore
    {p : ℕ} [Fact p.Prime] [Finite G]
    (S : ElementaryAbelianSection G) [S.N.Normal] (P : Sylow p G)
    (hpr : p ≠ S.r)
    (himage : pCore p (G ⧸ S.N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' S.N)) :
    ((S.restrictedConjugation
        ((P : Subgroup G) ⊓
          (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N))).ker.map
      ((P : Subgroup G) ⊓
        (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N)).subtype).Normal := by
  letI : Fact S.r.Prime := ⟨S.prime⟩
  let L := (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N)
  let A : Subgroup G := (P : Subgroup G) ⊓ L
  rw [S.map_restrictedConjugation_ker_eq_inf_centralizer A]
  have hsup : S.N ⊔ A = L :=
    sup_inf_comap_quotient_pCore_eq S.N P himage
  have hLNormal : L.Normal := inferInstance
  have hAp : IsPGroup p A := P.isPGroup'.to_inf_left
  constructor
  intro k hk g
  let c : G := g * k * g⁻¹
  have hcL : c ∈ L :=
    hLNormal.conj_mem k hk.1.2 g
  have hcCent : c ∈ Subgroup.centralizer (S.N : Set G) := by
    letI : (Subgroup.centralizer (S.N : Set G)).Normal := inferInstance
    exact Subgroup.Normal.conj_mem inferInstance k hk.2 g
  have hcSup : c ∈ S.N ⊔ A := by
    rw [hsup]
    exact hcL
  rw [Subgroup.mem_sup_of_normal_left] at hcSup
  obtain ⟨n, hnN, a, haA, hna⟩ := hcSup
  have hnCent : n ∈ Subgroup.centralizer (S.N : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (S.commute_N ⟨n, hnN⟩ ⟨z, hz⟩).eq.symm
  have haeq : a = n⁻¹ * c := eq_inv_mul_iff_mul_eq.mpr hna
  have haCent : a ∈ Subgroup.centralizer (S.N : Set G) := by
    rw [haeq]
    exact (Subgroup.centralizer (S.N : Set G)).mul_mem
      ((Subgroup.centralizer (S.N : Set G)).inv_mem hnCent) hcCent
  have hnaComm : Commute n a :=
    Subgroup.mem_centralizer_iff.mp haCent n hnN
  have hca : Commute c a := by
    rw [← hna]
    exact hnaComm.mul_left (Commute.refl a)
  obtain ⟨m, hkm⟩ := hAp ⟨k, hk.1⟩
  have hkpow : k ^ p ^ m = 1 := by
    simpa using congrArg Subtype.val hkm
  have hcpow : c ^ p ^ m = 1 := by
    simpa [c] using congrArg (MulAut.conj g) hkpow
  obtain ⟨j, haj⟩ := hAp ⟨a, haA⟩
  have hapow : a ^ p ^ j = 1 := by
    simpa using congrArg Subtype.val haj
  have hcBig : c ^ p ^ (m + j) = 1 := by
    rw [Nat.pow_add, pow_mul, hcpow, one_pow]
  have haBig : a ^ p ^ (m + j) = 1 := by
    rw [add_comm m j, Nat.pow_add, pow_mul, hapow, one_pow]
  have hainvBig : a⁻¹ ^ p ^ (m + j) = 1 := by
    rw [inv_pow, haBig, inv_one]
  have hnexpr : n = c * a⁻¹ := eq_mul_inv_iff_mul_eq.mpr hna
  have hnPpow : n ^ p ^ (m + j) = 1 := by
    rw [hnexpr, (hca.inv_right).mul_pow, hcBig, hainvBig, mul_one]
  obtain ⟨jR, hnjR⟩ := S.isPGroup_N ⟨n, hnN⟩
  have hnRpow : n ^ S.r ^ jR = 1 := by
    simpa using congrArg Subtype.val hnjR
  have hordP : orderOf n ∣ p ^ (m + j) :=
    orderOf_dvd_of_pow_eq_one hnPpow
  have hordR : orderOf n ∣ S.r ^ jR :=
    orderOf_dvd_of_pow_eq_one hnRpow
  have hcop : Nat.Coprime (p ^ (m + j)) (S.r ^ jR) :=
    Nat.coprime_pow_primes (m + j) jR Fact.out S.prime hpr
  have hnOne : n = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hordP hordR)
  have hac : a = c := by
    simpa [hnOne] using hna
  have hcA : c ∈ A := by
    rw [← hac]
    exact haA
  exact ⟨hcA, hcCent⟩

/-- A reusable form of the kernel calculation.  Normality of the ambient
copy of the action kernel is the only structural hypothesis left explicit;
in the affine chief-factor application it is obtained from the normal
preimage of the quotient `p`-core and uniqueness of its Sylow `p`-subgroup. -/
theorem pCore_eq_map_restrictedConjugation_ker
    {p : ℕ} [Fact p.Prime] (S : ElementaryAbelianSection G)
    (A : Subgroup G) (hpr : p ≠ S.r) (hAp : IsPGroup p A)
    (hcoreA : pCore p G ≤ A)
    (hkerNormal : ((S.restrictedConjugation A).ker.map A.subtype).Normal) :
    pCore p G = (S.restrictedConjugation A).ker.map A.subtype := by
  letI : Fact S.r.Prime := ⟨S.prime⟩
  apply le_antisymm
  · rw [S.map_restrictedConjugation_ker_eq_inf_centralizer A]
    exact le_inf hcoreA
      (pCore_le_centralizer_normalPSubgroup_of_ne hpr S.isPGroup_N S.normal)
  · exact le_pCore
      ((hAp.to_subgroup (S.restrictedConjugation A).ker).map A.subtype)
      hkerNormal

/-- The complete kernel calculation for the canonical complement over a
quotient `p`-core. -/
theorem pCore_eq_map_restrictedConjugation_ker_quotientCore
    {p : ℕ} [Fact p.Prime] [Finite G]
    (S : ElementaryAbelianSection G) [S.N.Normal] (P : Sylow p G)
    (hpr : p ≠ S.r)
    (himage : pCore p (G ⧸ S.N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' S.N)) :
    pCore p G =
      (S.restrictedConjugation
        ((P : Subgroup G) ⊓
          (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N))).ker.map
        ((P : Subgroup G) ⊓
          (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N)).subtype := by
  let L := (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N)
  let A : Subgroup G := (P : Subgroup G) ⊓ L
  have hmapCore : (pCore p G).map (QuotientGroup.mk' S.N) ≤
      pCore p (G ⧸ S.N) :=
    le_pCore ((pCore_isPGroup p G).map (QuotientGroup.mk' S.N))
      (Subgroup.Normal.map (pCore_normal p G) (QuotientGroup.mk' S.N)
        (QuotientGroup.mk'_surjective S.N))
  have hcoreL : pCore p G ≤ L :=
    Subgroup.map_le_iff_le_comap.mp hmapCore
  have hnormal : ((S.restrictedConjugation A).ker.map A.subtype).Normal :=
    S.map_restrictedConjugation_ker_normal_of_quotientCore P hpr himage
  exact S.pCore_eq_map_restrictedConjugation_ker A hpr
    P.isPGroup'.to_inf_left (le_inf (pCore_le_sylow P) hcoreL) hnormal

/-- Once the kernel has been identified with the `p`-core, the desired
Sylow-intersection equality is precisely the regular-vector condition in the
faithful image. -/
theorem inf_conjugate_complement_eq_pCore_iff_range_stabilizer_eq_bot
    {p : ℕ} (S : ElementaryAbelianSection G) (A : Subgroup G)
    (hAN : Disjoint A S.N) (n : S.N)
    (hcore : pCore p G = (S.restrictedConjugation A).ker.map A.subtype) :
    A ⊓ (MulAut.conj (n : G) • A) = pCore p G ↔
      MulAction.stabilizer (S.restrictedConjugation A).range
          (S.coordinates (Additive.ofMul n)) = ⊥ := by
  rw [hcore]
  exact S.inf_conjugate_complement_eq_map_ker_iff_range_stabilizer_eq_bot
    A hAN n

/-- Exact one-prime affine fibre reduction, with all structural hypotheses
discharged.  A quotient strong witness produces a translation `t ∈ N`; for
every left fibre shift `n * x`, the desired intersection equality is
equivalent to regularity of the vector represented by `n * t`. -/
theorem exists_translation_sylowInter_eq_pCore_iff_regular
    {p : ℕ} [Fact p.Prime] [Finite G]
    (S : ElementaryAbelianSection G) [S.N.Normal]
    (P : Sylow p G) (x : G) (hpr : p ≠ S.r)
    (hquot :
      sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
        (QuotientGroup.mk' S.N x) = pCore p (G ⧸ S.N)) :
    ∃ t : S.N, ∀ n : S.N,
      sylowInter P ((n : G) * x) = pCore p G ↔
        MulAction.stabilizer
          (S.restrictedConjugation
            ((P : Subgroup G) ⊓
              (pCore p (G ⧸ S.N)).comap
                (QuotientGroup.mk' S.N))).range
          (S.coordinates (Additive.ofMul (n * t))) = ⊥ := by
  letI : Fact S.r.Prime := ⟨S.prime⟩
  let L := (pCore p (G ⧸ S.N)).comap (QuotientGroup.mk' S.N)
  let A : Subgroup G := (P : Subgroup G) ⊓ L
  have himage : pCore p (G ⧸ S.N) ≤
      (P : Subgroup G).map (QuotientGroup.mk' S.N) := by
    intro y hy
    have hy' : y ∈
        sylowInter (P.mapSurjective (QuotientGroup.mk'_surjective S.N))
          (QuotientGroup.mk' S.N x) := by
      rw [hquot]
      exact hy
    exact hy'.1
  have hcore : pCore p G =
      (S.restrictedConjugation A).ker.map A.subtype :=
    S.pCore_eq_map_restrictedConjugation_ker_quotientCore P hpr himage
  have hAN : Disjoint A S.N :=
    pSubgroups_disjoint_of_ne hpr P.isPGroup'.to_inf_left S.isPGroup_N
  obtain ⟨t, htN, ht⟩ :=
    exists_kernel_conjugator_quotientCore_sections S.N S.isPGroup_N
      hpr P x hquot
  let tN : S.N := ⟨t, htN⟩
  refine ⟨tN, fun n ↦ ?_⟩
  rw [sylowInter_left_mul_eq_complement_translate_of_quotient_eq
    S.N P x hquot t ht n.2]
  exact S.inf_conjugate_complement_eq_pCore_iff_range_stabilizer_eq_bot
    (p := p) A hAN (n * tN) hcore

end ElementaryAbelianSection

end LisiSabatini
