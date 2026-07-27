import LisiSabatini.LinearAction
import LisiSabatini.NormalComponentReductionCore
import LisiSabatini.CommonTranslateCore
import Mathlib.LinearAlgebra.Prod

/-!
# Common affine two-base translates

This is the linear statement singled out by the mixed three-row
chief-factor reduction.  For each distinct prime label, two independently
translated points must have trivial common stabilizer in the corresponding
normal prime-power component.

Unlike the one-point odd-order theorem, the definition permits the prime
`2` and imposes no parity condition on the field characteristic.
-/

noncomputable section

namespace LisiSabatini

universe uI uV

/-- Diagonal copy of a general linear group on the product of two copies of
its module.  CATB is one-point affine regularity for these diagonal images. -/
def diagonalGeneralLinearHom
    (R : Type*) (V : Type uV)
    [Semiring R] [AddCommMonoid V] [Module R V] :
    LinearMap.GeneralLinearGroup R V →*
      LinearMap.GeneralLinearGroup R (V × V) where
  toFun g :=
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      (g.toLinearEquiv.prodCongr g.toLinearEquiv)
  map_one' := by
    ext z <;> rfl
  map_mul' g h := by
    ext z <;> rfl

@[simp]
theorem diagonalGeneralLinearHom_smul
    {R : Type*} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (g : LinearMap.GeneralLinearGroup R V) (z : V × V) :
    diagonalGeneralLinearHom R V g • z =
      (g • z.1, g • z.2) :=
  rfl

theorem diagonalGeneralLinearHom_injective
    (R : Type*) (V : Type uV)
    [Semiring R] [AddCommMonoid V] [Module R V] :
    Function.Injective (diagonalGeneralLinearHom R V) := by
  intro g h hgh
  ext v
  have hpair := congrArg (fun k ↦ k • (v, (0 : V))) hgh
  simpa using congrArg Prod.fst hpair

/-- A diagonal-image stabilizer is trivial exactly when the original group
has trivial common stabilizer on the two coordinates. -/
theorem stabilizer_map_diagonalGeneralLinearHom_eq_bot_iff
    {R : Type*} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (A : Subgroup (LinearMap.GeneralLinearGroup R V))
    (v w : V) :
    MulAction.stabilizer
          (A.map (diagonalGeneralLinearHom R V)) (v, w) =
        ⊥ ↔
      MulAction.stabilizer A v ⊓
          MulAction.stabilizer A w =
        ⊥ := by
  let D := diagonalGeneralLinearHom R V
  constructor
  · intro hdiag
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    let gd : A.map D := ⟨D g.1, ⟨g.1, g.2, rfl⟩⟩
    have hgdMem :
        gd ∈ MulAction.stabilizer (A.map D) (v, w) := by
      rw [MulAction.mem_stabilizer_iff]
      apply Prod.ext
      · exact MulAction.mem_stabilizer_iff.mp hg.1
      · exact MulAction.mem_stabilizer_iff.mp hg.2
    have hgdOne : gd = 1 :=
      (Subgroup.eq_bot_iff_forall _).mp hdiag gd hgdMem
    apply Subtype.ext
    apply (diagonalGeneralLinearHom_injective R V)
    simpa [D, gd] using congrArg Subtype.val hgdOne
  · intro hsource
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro gd hgd
    obtain ⟨g, hgA, hg⟩ := gd.2
    let ga : A := ⟨g, hgA⟩
    have hfix : D g • (v, w) = (v, w) := by
      rw [hg]
      exact MulAction.mem_stabilizer_iff.mp hgd
    have hgaMem :
        ga ∈ MulAction.stabilizer A v ⊓
          MulAction.stabilizer A w := by
      constructor
      · change ga • v = v
        simpa [D] using congrArg Prod.fst hfix
      · change ga • w = w
        simpa [D] using congrArg Prod.snd hfix
    have hgaOne : ga = 1 :=
      (Subgroup.eq_bot_iff_forall _).mp hsource ga hgaMem
    apply Subtype.ext
    calc
      gd.1 = D g := hg.symm
      _ = D (1 : LinearMap.GeneralLinearGroup R V) := by
        congr 1
        exact congrArg Subtype.val hgaOne
      _ = 1 := D.map_one

/-- Common affine two-base synchronization on an arbitrary `ZMod r` module.

The acting subgroups are normal prime-power subgroups of one common linear
group.  Their images in the ambient general linear group act on the two
translated points. -/
def CommonAffineTwoBaseTranslatesOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    ∀ H : I → Subgroup K,
      (∀ i, (H i).Normal) →
      (∀ i, IsPGroup (p i) (H i)) →
      ∀ a b : I → V,
        ∃ v w : V, ∀ i,
          MulAction.stabilizer ((H i).map K.subtype) (v + a i) ⊓
          MulAction.stabilizer ((H i).map K.subtype) (w + b i) =
            ⊥

/-- One-point formulation of CATB on the diagonal representation
`V × V`.  It retains the original normal-component data in `K`, while the
actual acting subgroups are their diagonal images. -/
def CommonDiagonalAffineRegularTranslatesOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    ∀ H : I → Subgroup K,
      (∀ i, (H i).Normal) →
      (∀ i, IsPGroup (p i) (H i)) →
      ∀ t : I → V × V,
        ∃ z : V × V, ∀ i,
          MulAction.stabilizer
              (((H i).map K.subtype).map
                (diagonalGeneralLinearHom (ZMod r) V))
              (z + t i) =
            ⊥

/-- Maximal-normal-component form of CATB.  Since every normal `p`-subgroup
of `K` lies in `O_p(K)`, these prime cores are the only component family
which needs to be proved. -/
def PrimeCoreCommonAffineTwoBaseTranslatesOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    ∀ a b : I → V,
      ∃ v w : V, ∀ i,
        MulAction.stabilizer
              ((pCore (p i) K).map K.subtype) (v + a i) ⊓
            MulAction.stabilizer
              ((pCore (p i) K).map K.subtype) (w + b i) =
          ⊥

/-- CATB is exactly common affine regularity for the diagonal images on the
product module. -/
theorem commonAffineTwoBaseTranslatesOn_iff_diagonal
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    CommonAffineTwoBaseTranslatesOn.{uI} r V K ↔
      CommonDiagonalAffineRegularTranslatesOn.{uI} r V K := by
  constructor
  · intro h I _ p hp hinj hcross H hHnormal hHp t
    obtain ⟨v, w, hvw⟩ :=
      h p hp hinj hcross H hHnormal hHp
        (fun i ↦ (t i).1) (fun i ↦ (t i).2)
    refine ⟨(v, w), fun i ↦ ?_⟩
    apply
      (stabilizer_map_diagonalGeneralLinearHom_eq_bot_iff
        ((H i).map K.subtype)
        (v + (t i).1) (w + (t i).2)).2
    simpa using hvw i
  · intro h I _ p hp hinj hcross H hHnormal hHp a b
    obtain ⟨z, hz⟩ :=
      h p hp hinj hcross H hHnormal hHp
        (fun i ↦ (a i, b i))
    refine ⟨z.1, z.2, fun i ↦ ?_⟩
    apply
      (stabilizer_map_diagonalGeneralLinearHom_eq_bot_iff
        ((H i).map K.subtype)
        (z.1 + a i) (z.2 + b i)).1
    simpa using hz i

/-- Coordinate-space form of common affine two-base synchronization. -/
def CommonAffineTwoBaseTranslates
    (r d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop :=
  CommonAffineTwoBaseTranslatesOn.{uI} r (Fin d → ZMod r) K

/-- The coordinate and arbitrary-module formulations agree definitionally. -/
theorem commonAffineTwoBaseTranslates_iff_on
    (r d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    CommonAffineTwoBaseTranslates.{uI} r d K ↔
      CommonAffineTwoBaseTranslatesOn.{uI} r
        (Fin d → ZMod r) K :=
  Iff.rfl

/-- For one acting subgroup, prescribing independent affine translations
does not strengthen the ordinary base-two assertion: translate the two base
vectors back coordinatewise.  The genuinely new content of CATB is therefore
the use of one pair for several labelled subgroups. -/
theorem exists_affineTwoBaseTranslates_iff_exists_baseTwo
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : V) :
    (∃ v w : V,
      MulAction.stabilizer A (v + a) ⊓
          MulAction.stabilizer A (w + b) =
        ⊥) ↔
      ∃ u z : V,
        MulAction.stabilizer A u ⊓
            MulAction.stabilizer A z =
          ⊥ := by
  constructor
  · rintro ⟨v, w, h⟩
    exact ⟨v + a, w + b, h⟩
  · rintro ⟨u, z, h⟩
    refine ⟨u - a, z - b, ?_⟩
    simpa using h

/-- The existing one-point normal-component synchronization theorem already
settles every family whose acting primes are odd: make the first coordinate
regular and leave the second coordinate arbitrary.  Thus the genuinely new
two-base work begins only at the parity cases excluded from NCAS. -/
theorem exists_commonAffineTwoBaseTranslates_of_normalComponentAffineSynchronizationOn
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hNCAS :
      NormalComponentAffineSynchronizationOn.{uI} r V K)
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p)
    (hpTwo : ∀ i, p i ≠ 2)
    (hcross : ∀ i, p i ≠ r)
    (H : I → Subgroup K)
    (hHnormal : ∀ i, (H i).Normal)
    (hHp : ∀ i, IsPGroup (p i) (H i))
    (a b : I → V) :
    ∃ v w : V, ∀ i,
      MulAction.stabilizer ((H i).map K.subtype) (v + a i) ⊓
          MulAction.stabilizer ((H i).map K.subtype) (w + b i) =
        ⊥ := by
  letI := Fintype.ofFinite I
  obtain ⟨v, hv⟩ :=
    hNCAS p hp hinj hpTwo hcross H hHnormal hHp a
  exact ⟨v, 0, fun i ↦ by simp [hv i]⟩

/-- The part of CATB in which the family contains the prime `2`.

Because the prime labels are injective, such a family has exactly one
`2`-label.  This is the only family type left over in odd characteristic
after applying the existing one-point synchronization theorem to families
of odd acting primes. -/
def CommonAffineTwoBaseTranslatesOnForTwoComponent
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    (∃ i, p i = 2) →
    ∀ H : I → Subgroup K,
      (∀ i, (H i).Normal) →
      (∀ i, IsPGroup (p i) (H i)) →
      ∀ a b : I → V,
        ∃ v w : V, ∀ i,
          MulAction.stabilizer ((H i).map K.subtype) (v + a i) ⊓
              MulAction.stabilizer ((H i).map K.subtype) (w + b i) =
            ⊥

/-- Once one-point synchronization is known for odd acting primes, full
CATB reduces exactly to the families containing the unique possible
`2`-component. -/
theorem commonAffineTwoBaseTranslatesOn_iff_forTwoComponent_of_NCAS
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hNCAS :
      NormalComponentAffineSynchronizationOn.{uI} r V K) :
    CommonAffineTwoBaseTranslatesOn.{uI} r V K ↔
      CommonAffineTwoBaseTranslatesOnForTwoComponent.{uI} r V K := by
  constructor
  · intro h I _ p hp hinj hcross _ H hHnormal hHp a b
    exact h p hp hinj hcross H hHnormal hHp a b
  · intro h I _ p hp hinj hcross H hHnormal hHp a b
    by_cases hTwo : ∃ i, p i = 2
    · exact h p hp hinj hcross hTwo H hHnormal hHp a b
    · have hpTwo : ∀ i, p i ≠ 2 := by
        intro i hi
        exact hTwo ⟨i, hi⟩
      exact
        exists_commonAffineTwoBaseTranslates_of_normalComponentAffineSynchronizationOn
          hNCAS p hp hinj hpTwo hcross H hHnormal hHp a b

/-- Bad pairs for one translated two-base constraint. -/
def affineTwoBaseBadSet
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : V) : Set (V × V) :=
  {z | MulAction.stabilizer A (z.1 + a) ⊓
      MulAction.stabilizer A (z.2 + b) ≠ ⊥}

@[simp]
theorem not_mem_affineTwoBaseBadSet_iff
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : V) (z : V × V) :
    z ∉ affineTwoBaseBadSet A a b ↔
      MulAction.stabilizer A (z.1 + a) ⊓
          MulAction.stabilizer A (z.2 + b) =
        ⊥ := by
  simp [affineTwoBaseBadSet]

/-- CATB's bad-pair predicate is exactly ordinary nonregularity for the
diagonal image on `V × V`, after translating the two coordinates. -/
theorem mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : V) (z : V × V) :
    z ∈ affineTwoBaseBadSet A a b ↔
      (z.1 + a, z.2 + b) ∈
        nonregularVectors
          (A.map (diagonalGeneralLinearHom (ZMod r) V)) := by
  change
    (MulAction.stabilizer A (z.1 + a) ⊓
          MulAction.stabilizer A (z.2 + b) ≠
        ⊥) ↔
      MulAction.stabilizer
          (A.map (diagonalGeneralLinearHom (ZMod r) V))
          (z.1 + a, z.2 + b) ≠
        ⊥
  exact not_congr
    (stabilizer_map_diagonalGeneralLinearHom_eq_bot_iff
      A (z.1 + a) (z.2 + b)).symm

/-- Set-level diagonal reformulation of one affine bad locus. -/
theorem affineTwoBaseBadSet_eq_preimage_nonregularVectors_diagonal
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : V) :
    affineTwoBaseBadSet A a b =
      (fun z : V × V ↦ (z.1 + a, z.2 + b)) ⁻¹'
        nonregularVectors
          (A.map (diagonalGeneralLinearHom (ZMod r) V)) := by
  ext z
  exact
    mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
      A a b z

/-- Enlarging the acting subgroup enlarges its affine two-base bad locus. -/
theorem affineTwoBaseBadSet_mono
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    {A B : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hAB : A ≤ B) (a b : V) :
    affineTwoBaseBadSet A a b ⊆
      affineTwoBaseBadSet B a b := by
  intro z hz
  rw [mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal]
  rw [mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal] at hz
  exact nonregularVectors_mono (Subgroup.map_mono hAB) hz

/-- Cardinal monotonicity for nested acting subgroups. -/
theorem affineTwoBaseBadSet_ncard_mono
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {A B : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hAB : A ≤ B) (a b : V) :
    (affineTwoBaseBadSet A a b).ncard ≤
      (affineTwoBaseBadSet B a b).ncard :=
  Set.ncard_le_ncard (affineTwoBaseBadSet_mono hAB a b)

/-- It is equivalent to prove CATB for the maximal normal prime components
`O_p(K)` only. -/
theorem commonAffineTwoBaseTranslatesOn_iff_primeCores
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    CommonAffineTwoBaseTranslatesOn.{uI} r V K ↔
      PrimeCoreCommonAffineTwoBaseTranslatesOn.{uI} r V K := by
  constructor
  · intro h I _ p hp hinj hcross a b
    exact h p hp hinj hcross
      (fun i ↦ pCore (p i) K)
      (fun _ ↦ inferInstance)
      (fun i ↦ pCore_isPGroup (p i) K)
      a b
  · intro h I _ p hp hinj hcross H hHnormal hHp a b
    obtain ⟨v, w, hvw⟩ := h p hp hinj hcross a b
    refine ⟨v, w, fun i ↦ ?_⟩
    apply
      (not_mem_affineTwoBaseBadSet_iff
        ((H i).map K.subtype) (a i) (b i) (v, w)).1
    intro hbad
    have hle :
        (H i).map K.subtype ≤
          (pCore (p i) K).map K.subtype :=
      map_normalPSubgroup_le_map_pCore (hHp i) (hHnormal i)
    have hcoreBad :=
      affineTwoBaseBadSet_mono hle (a i) (b i) hbad
    exact
      ((not_mem_affineTwoBaseBadSet_iff
        ((pCore (p i) K).map K.subtype)
        (a i) (b i) (v, w)).2 (hvw i))
        hcoreBad

/-- Translating the two coordinates does not change the cardinality of an
individual bad locus. -/
theorem affineTwoBaseBadSet_ncard_eq_untranslated
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : V) :
    (affineTwoBaseBadSet A a b).ncard =
      (affineTwoBaseBadSet A 0 0).ncard := by
  let shift : V × V → V × V := fun z ↦ z + (a, b)
  have hshift : Function.Bijective shift := by
    simpa [shift] using (Equiv.addRight (a, b)).bijective
  have hset :
      affineTwoBaseBadSet A a b =
        shift ⁻¹' affineTwoBaseBadSet A 0 0 := by
    ext z
    simp [shift, affineTwoBaseBadSet]
  rw [hset]
  exact Set.ncard_preimage_of_injective_subset_range
    hshift.injective (by simp [hshift.surjective.range_eq])

/-- An untranslated bad pair has both coordinates in the ordinary
nonregular locus.  The converse need not hold: the two point stabilizers may
be nontrivial with trivial intersection. -/
theorem affineTwoBaseBadSet_zero_subset_nonregular_prod
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) :
    affineTwoBaseBadSet A 0 0 ⊆
      nonregularVectors A ×ˢ nonregularVectors A := by
  intro z hz
  change
    MulAction.stabilizer A z.1 ≠ ⊥ ∧
      MulAction.stabilizer A z.2 ≠ ⊥
  constructor
  · intro hfirst
    apply hz
    simp [hfirst]
  · intro hsecond
    apply hz
    simp [hsecond]

/-- Squared one-point bound for every translated two-base bad locus.

This is the bridge from the existing quasiprimitive fixed-spectrum estimates
to a prospective CATB leaf theorem.  It is intentionally only a rowwise
bound; imprimitive examples show that summing it over all rows can exceed
`|V|²`. -/
theorem ncard_affineTwoBaseBadSet_le_nonregular_sq
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : V) :
    (affineTwoBaseBadSet A a b).ncard ≤
      (nonregularVectors A).ncard * (nonregularVectors A).ncard := by
  rw [affineTwoBaseBadSet_ncard_eq_untranslated A a b]
  calc
    (affineTwoBaseBadSet A 0 0).ncard ≤
        (nonregularVectors A ×ˢ nonregularVectors A).ncard :=
      Set.ncard_le_ncard
        (affineTwoBaseBadSet_zero_subset_nonregular_prod A)
    _ = (nonregularVectors A).ncard *
        (nonregularVectors A).ncard := Set.ncard_prod

/-- For a finite `p`-group, a pair is bad exactly when an element of order
`p` fixes both translated coordinates.  This is the prime-order witness
form behind the exact union of affine fixed-space rectangles. -/
theorem mem_affineTwoBaseBadSet_iff_exists_primeOrder_fixed
    {r p : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    [Fact p.Prime]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Finite A] (hA : IsPGroup p A)
    (a b : V) (z : V × V) :
    z ∈ affineTwoBaseBadSet A a b ↔
      ∃ g : A,
        orderOf g = p ∧
          g • (z.1 + a) = z.1 + a ∧
          g • (z.2 + b) = z.2 + b := by
  let S :=
    MulAction.stabilizer A (z.1 + a) ⊓
      MulAction.stabilizer A (z.2 + b)
  change S ≠ ⊥ ↔ _
  constructor
  · intro hS
    have hpCard : p ∣ Nat.card S := by
      rcases (hA.to_subgroup S).card_eq_or_dvd with hcard | hpCard
      · exact (hS (S.eq_bot_of_card_eq hcard)).elim
      · exact hpCard
    obtain ⟨g, hgOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := S) p hpCard
    refine ⟨g.1, ?_, ?_, ?_⟩
    · exact (Subgroup.orderOf_coe g).trans hgOrder
    · exact MulAction.mem_stabilizer_iff.mp g.2.1
    · exact MulAction.mem_stabilizer_iff.mp g.2.2
  · rintro ⟨g, hgOrder, hgFirst, hgSecond⟩
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let gS : S :=
      ⟨g, MulAction.mem_stabilizer_iff.mpr hgFirst,
        MulAction.mem_stabilizer_iff.mpr hgSecond⟩
    refine ⟨gS, ?_⟩
    intro hgOne
    have hgOne' : g = 1 := by
      simpa [gS] using congrArg Subtype.val hgOne
    have hOrderOne : orderOf g = 1 :=
      orderOf_eq_one_iff.mpr hgOne'
    exact (Fact.out : p.Prime).ne_one (hgOrder.symm.trans hOrderOne)

/-- The affine fixed-space rectangle belonging to one acting element. -/
def affineTwoBaseFixedRectangle
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (g : A) (a b : V) : Set (V × V) :=
  {z |
    g • (z.1 + a) = z.1 + a ∧
      g • (z.2 + b) = z.2 + b}

/-- Exact prime-order rectangle decomposition of one bad locus. -/
theorem affineTwoBaseBadSet_eq_iUnion_primeOrder_fixedRectangles
    {r p : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    [Fact p.Prime]
    (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Finite A] (hA : IsPGroup p A)
    (a b : V) :
    affineTwoBaseBadSet A a b =
      ⋃ g : {g : A // orderOf g = p},
        affineTwoBaseFixedRectangle A g.1 a b := by
  ext z
  rw [mem_affineTwoBaseBadSet_iff_exists_primeOrder_fixed A hA]
  simp only [Set.mem_iUnion, affineTwoBaseFixedRectangle, Set.mem_setOf_eq]
  constructor
  · rintro ⟨g, hgOrder, hgFirst, hgSecond⟩
    exact ⟨⟨g, hgOrder⟩, hgFirst, hgSecond⟩
  · rintro ⟨g, hgFirst, hgSecond⟩
    exact ⟨g.1, g.2, hgFirst, hgSecond⟩

/-- The exact bad locus for a labelled family is the union of its individual
bad loci.  No cardinality estimate or union bound is built into this
definition. -/
def affineTwoBaseBadUnion
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    {I : Type uI}
    (A : I → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : I → V) : Set (V × V) :=
  ⋃ i, affineTwoBaseBadSet (A i) (a i) (b i)

@[simp]
theorem not_mem_affineTwoBaseBadUnion_iff
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    {I : Type uI}
    (A : I → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : I → V) (z : V × V) :
    z ∉ affineTwoBaseBadUnion A a b ↔
      ∀ i,
        MulAction.stabilizer (A i) (z.1 + a i) ⊓
            MulAction.stabilizer (A i) (z.2 + b i) =
          ⊥ := by
  simp [affineTwoBaseBadUnion, not_mem_affineTwoBaseBadSet_iff]

/-- Exact finite-set reformulation of simultaneous affine two-base
synchronization: a common pair exists precisely when the union of the bad
loci does not cover the product space. -/
theorem exists_common_affineTwoBaseTranslates_iff_badUnion_ne_univ
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    {I : Type uI}
    (A : I → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : I → V) :
    (∃ v w : V, ∀ i,
      MulAction.stabilizer (A i) (v + a i) ⊓
          MulAction.stabilizer (A i) (w + b i) =
        ⊥) ↔
      affineTwoBaseBadUnion A a b ≠ Set.univ := by
  constructor
  · rintro ⟨v, w, h⟩ hcover
    have hmem : (v, w) ∈ affineTwoBaseBadUnion A a b := by
      rw [hcover]
      exact Set.mem_univ (v, w)
    exact
      ((not_mem_affineTwoBaseBadUnion_iff A a b (v, w)).2 h)
        hmem
  · intro hproper
    by_contra hnone
    apply hproper
    apply Set.eq_univ_of_forall
    intro z
    by_contra hz
    apply hnone
    exact ⟨z.1, z.2,
      (not_mem_affineTwoBaseBadUnion_iff A a b z).1 hz⟩

/-- The strict sum-of-bad-cardinalities certificate used by the finite
census is a sufficient condition for a common translated two-base. -/
theorem exists_commonAffineTwoBaseTranslates_of_sum_bad_ncard_lt
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {I : Type uI} [Fintype I]
    (A : I → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : I → V)
    (hcard :
      ∑ i, (affineTwoBaseBadSet (A i) (a i) (b i)).ncard <
        Nat.card (V × V)) :
    ∃ v w : V, ∀ i,
      MulAction.stabilizer (A i) (v + a i) ⊓
          MulAction.stabilizer (A i) (w + b i) =
        ⊥ := by
  obtain ⟨z, hz⟩ :=
    exists_avoids_of_sum_ncard_lt
      (fun i ↦ affineTwoBaseBadSet (A i) (a i) (b i)) hcard
  exact ⟨z.1, z.2, fun i ↦
    (not_mem_affineTwoBaseBadSet_iff
      (A i) (a i) (b i) z).1 (hz i)⟩

/-- A strict sum of squared ordinary nonregular-set bounds is sufficient for
a common translated two-base.  This is the quantitative entry point for a
quasiprimitive CATB leaf; it is not asserted for arbitrary imprimitive
actions. -/
theorem exists_commonAffineTwoBaseTranslates_of_sum_nonregular_sq_lt
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {I : Type uI} [Fintype I]
    (A : I → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (a b : I → V)
    (hcard :
      ∑ i,
          (nonregularVectors (A i)).ncard *
            (nonregularVectors (A i)).ncard <
        Nat.card (V × V)) :
    ∃ v w : V, ∀ i,
      MulAction.stabilizer (A i) (v + a i) ⊓
          MulAction.stabilizer (A i) (w + b i) =
        ⊥ := by
  apply exists_commonAffineTwoBaseTranslates_of_sum_bad_ncard_lt A a b
  exact
    (Finset.sum_le_sum fun i _ ↦
      ncard_affineTwoBaseBadSet_le_nonregular_sq
        (A i) (a i) (b i)).trans_lt hcard

/-- Uniform cardinal certificate for all normal prime-component families in
one common action. -/
def CommonAffineTwoBaseBadCardinalityBoundOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    ∀ H : I → Subgroup K,
      (∀ i, (H i).Normal) →
      (∀ i, IsPGroup (p i) (H i)) →
      ∀ a b : I → V,
        ∑ i,
            (affineTwoBaseBadSet
              ((H i).map K.subtype) (a i) (b i)).ncard <
          Nat.card (V × V)

/-- Translation-free form of the cardinal certificate. -/
def CommonAffineTwoBaseUntranslatedBadCardinalityBoundOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    ∀ H : I → Subgroup K,
      (∀ i, (H i).Normal) →
      (∀ i, IsPGroup (p i) (H i)) →
        ∑ i,
            (affineTwoBaseBadSet
              ((H i).map K.subtype) 0 0).ncard <
          Nat.card (V × V)

/-- Since each affine shift preserves bad-locus cardinality, it suffices to
prove the strict sum bound at zero translations. -/
theorem CommonAffineTwoBaseUntranslatedBadCardinalityBoundOn.translated
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (h :
      CommonAffineTwoBaseUntranslatedBadCardinalityBoundOn.{uI}
        r V K) :
    CommonAffineTwoBaseBadCardinalityBoundOn.{uI} r V K := by
  intro I _ p hp hinj hcross H hHnormal hHp a b
  simpa only [affineTwoBaseBadSet_ncard_eq_untranslated] using
    h p hp hinj hcross H hHnormal hHp

/-- A uniform strict bad-cardinality bound proves CATB. -/
theorem CommonAffineTwoBaseBadCardinalityBoundOn.commonAffineTwoBaseTranslatesOn
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (h :
      CommonAffineTwoBaseBadCardinalityBoundOn.{uI} r V K) :
    CommonAffineTwoBaseTranslatesOn.{uI} r V K := by
  intro I _ p hp hinj hcross H hHnormal hHp a b
  exact exists_commonAffineTwoBaseTranslates_of_sum_bad_ncard_lt
    (fun i ↦ (H i).map K.subtype) a b
    (h p hp hinj hcross H hHnormal hHp a b)

end LisiSabatini
