module

public import LisiSabatini.TwoCoreSymplecticTypeDihedral
public import LisiSabatini.TwoCoreSymplecticTypeSemidihedral
public import LisiSabatini.TwoCoreSymplecticTypeCentralProductCount
public import LisiSabatini.MappedPCoreHall

/-!
# The exact Hall--Berger two-core frontier

Berger's Lemma 1.1 does **not** give a five-way classification into a
cyclic group, an extraspecial--cyclic product, or one of the three
maximal-class families.  In characteristic two it says that the group is
a central product `E ∘ C`, where `E` is extraspecial and `C` is cyclic,
dihedral of order at least sixteen, semidihedral, or generalized
quaternion.  In particular, a nontrivial extraspecial factor may occur
together with a noncyclic maximal-class head.

This file records that mixed case explicitly.  It proves all consequences
of the nonmixed branches and gives separate machine-readable names to the
three genuinely missing mixed inputs:

* the internal-central-product active-involution count;
* the mixed fixed-rectangle estimate;
* the characteristic-two Stone--von Neumann/head-field degree data.

None of those statements, and not the Hall--Berger classification itself,
is asserted as an axiom or theorem here.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-! ## The structural output of Berger's lemma -/

/-- The noncyclic maximal-class head in Berger's two-group
classification.

The parameters agree with the normal forms used in the dedicated files:
the rotation orders are respectively `4*k`, `8*k`, and `2*n`.  In a
mixed central product the quaternion head is taken of order at least
sixteen; a `Q₈` factor can instead be absorbed into the extraspecial
factor. -/
inductive BergerMaximalClassHead
    (H : Type u) [Group H] [Finite H] : Type (u + 1)
  | dihedral
      (k : ℕ) (hk : 2 ≤ k)
      (equiv : H ≃* DihedralGroup (4 * k))
  | semidihedral
      (k : ℕ) (hk : 0 < k)
      (presentation : IsSemidihedralPresentation H k)
  | generalizedQuaternion
      (n : ℕ) (hn : 4 ≤ n)
      (equiv : H ≃* QuaternionGroup n)

namespace BergerMaximalClassHead

variable {H : Type u} [Group H] [Finite H]

/-- The order of the distinguished cyclic rotation subgroup. -/
def rotationOrder (head : BergerMaximalClassHead H) : ℕ :=
  match head with
  | .dihedral k _ _ => 4 * k
  | .semidihedral k _ _ => 8 * k
  | .generalizedQuaternion n _ _ => 2 * n

/-- Berger's exact noncentral-involution envelope for a maximal-class
head centrally multiplied by an extraspecial group of degree `e`.

Writing `N` for `rotationOrder`, the three rows are

* dihedral: `(N/2+2)e² + (N/2)e - 2`;
* semidihedral: `(N/2+2)e² - 2`;
* quaternion: `(N/2+2)e² - (N/2)e - 2`.
-/
def activeEnvelope
    (head : BergerMaximalClassHead H) (e : ℕ) : ℕ :=
  let N := head.rotationOrder
  match head with
  | .dihedral _ _ _ =>
      (N / 2 + 2) * (e * e) + (N / 2) * e - 2
  | .semidihedral _ _ _ =>
      (N / 2 + 2) * (e * e) - 2
  | .generalizedQuaternion _ _ _ =>
      (N / 2 + 2) * (e * e) - (N / 2) * e - 2

/-- Every mixed maximal-class head has rotation order at least eight. -/
theorem eight_le_rotationOrder
    (head : BergerMaximalClassHead H) :
    8 ≤ head.rotationOrder := by
  cases head with
  | dihedral k hk _ =>
      simp only [rotationOrder]
      omega
  | semidihedral k hk _ =>
      simp only [rotationOrder]
      omega
  | generalizedQuaternion n hn _ =>
      simp only [rotationOrder]
      omega

end BergerMaximalClassHead

/-- An internal mixed central product `E ∘ C` inside `P`.

The extraspecial center is precisely the amalgamated intersection.  The
commuting and generation fields express `P = EC`; no external
central-product quotient construction is introduced. -/
structure BergerMixedCentralProductData
    (P : Type u) [Group P] [Finite P] where
  extraspecialPart : Subgroup P
  headPart : Subgroup P
  extraspecial : IsExtraspecial 2 extraspecialPart
  head : BergerMaximalClassHead headPart
  commute :
    ∀ (x : extraspecialPart) (y : headPart),
      x.1 * y.1 = y.1 * x.1
  generate :
    extraspecialPart ⊔ headPart = ⊤
  overlap :
    (Subgroup.center extraspecialPart).map
        extraspecialPart.subtype =
      extraspecialPart ⊓ headPart

/-- The proof-relevant reduction supplied by Hall--Berger.

The `extraspecialCyclicProduct` branch records the exact intrinsic
consequence used in the cyclic-head case.  The final constructor is the
mixed case omitted by the earlier frontier. -/
inductive HallBergerTwoCoreShape
    (P : Type u) [Group P] [Finite P] : Type (u + 1)
  | cyclic
      (hcyclic : IsCyclic P)
  | extraspecialCyclicProduct
      (hcommutator : HasCentralCommutatorOfOrderTwo P)
  | dihedral
      (k : ℕ) (hk : 0 < k)
      (equiv : P ≃* DihedralGroup (4 * k))
  | semidihedral
      (k : ℕ) (hk : 0 < k)
      (presentation : IsSemidihedralPresentation P k)
  | generalizedQuaternion
      (n : ℕ) (hn : 0 < n)
      (equiv : P ≃* QuaternionGroup n)
  | mixedMaximalClass
      (data : BergerMixedCentralProductData P)

/-- The corrected Hall--Berger classification target.

This is a proposition definition, not a theorem or axiom. -/
def HallBergerTwoGroupClassificationStatement : Prop :=
  ∀ (P : Type u) [Group P] [Finite P],
    IsPGroup 2 P →
    HasCyclicCharacteristicAbelianSubgroups P →
    Nonempty (HallBergerTwoCoreShape P)

/-! ## The three mixed inputs, kept separate -/

/-- The exact active-involution count still required for an internal
mixed central product. -/
def MixedCentralProductActiveCountStatement : Prop :=
  ∀ {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (data : BergerMixedCentralProductData P)
    (e : ℕ),
    2 ≤ e →
    Nat.card data.extraspecialPart = 2 * e * e →
    CenterFixedPointFreeAction r d P →
    (activePrimeOrderElements 2 P).card ≤
      data.head.activeEnvelope e

/-- The half-dimensional fixed-rectangle theorem still required for
mixed maximal-class heads. -/
def MixedCentralProductFixedRectangleStatement : Prop :=
  ∀ {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P],
    Nonempty (BergerMixedCentralProductData P) →
    Even d →
    CenterFixedPointFreeAction r d P →
    ∀ x : P, x ∈ activePrimeOrderElements 2 P →
      (fixedVectorSet x.1).ncard *
          (fixedVectorSet x.1).ncard ≤
        r ^ d

/-- Numerical output of the characteristic-two
Stone--von Neumann/head-field argument.

Here `e` is the degree of the extraspecial factor and `a` is the degree of
the relevant head field over the prime field. -/
structure MixedCentralProductHeadFieldData
    {r d : ℕ}
    {P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    [Finite P]
    (data : BergerMixedCentralProductData P)
    (e : ℕ) where
  fieldDegree : ℕ
  fieldDegree_pos : 0 < fieldDegree
  rotationOrder_dvd :
    data.head.rotationOrder ∣ r ^ fieldDegree - 1
  constituentDimension_le :
    e * fieldDegree ≤ d
  doubledDegree_le :
    2 * e ≤ d

/-- The exact representation-theoretic statement still required for a
mixed central product.

Homogeneity is stated explicitly; it is the hypothesis supplied when the
group is a normal prime core of a quasiprimitive action. -/
def MixedCentralProductHeadFieldDegreeStatement : Prop :=
  ∀ {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (data : BergerMixedCentralProductData P)
    (e : ℕ),
    IsPGroup 2 P →
    r ≠ 2 →
    0 < d →
    2 ≤ e →
    Nat.card data.extraspecialPart = 2 * e * e →
    Representation.IsHomogeneous
      (linearSubgroupRepresentation P) →
    Nonempty (MixedCentralProductHeadFieldData data e)

/-! ## The cyclic-head subcase -/

/-- The pure central-commutator representation comparison.

Unlike the mixed statements above, the ordinary inequality is now proved
in `TwoCoreSymplecticTypeRepresentationComparison`; only its sharp
`F₃²` active-involution edge remains visible in this interface. -/
def CentralCommutatorRepresentationComparisonStatement : Prop :=
  ∀ (r d : ℕ) [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P],
    r ≠ 2 →
    0 < d →
    IsPGroup 2 P →
    HasCyclicCharacteristicAbelianSubgroups P →
    HasCentralCommutatorOfOrderTwo P →
    CenterFixedPointFreeAction r d P →
      4 * (Nat.card (P ⧸ Subgroup.center P) - 1) ≤
          r ^ d - 1 ∨
        (r = 3 ∧ d = 2 ∧
          (activePrimeOrderElements 2 P).card ≤ 4)

/-- The central-coset count and a supplied representation comparison give
the active-involution half-density estimate in the cyclic-head subcase. -/
theorem active_halfDensity_of_centralCommutator_representationComparison
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hhall : HasCyclicCharacteristicAbelianSubgroups P)
    (C : CenterFixedPointFreeAction r d P)
    (hcomparison :
      4 * (Nat.card (P ⧸ Subgroup.center P) - 1) ≤
          r ^ d - 1 ∨
        (r = 3 ∧ d = 2 ∧
          (activePrimeOrderElements 2 P).card ≤ 4)) :
    2 * (activePrimeOrderElements 2 P).card ≤
      r ^ d - 1 := by
  have hactive :=
    card_activePrimeOrderElements_two_le_two_mul_quotientCenter_pred_of_hall
      P hcomm hhall C
  rcases hcomparison with hordinary | ⟨hr, hd, hedge⟩
  · calc
      2 * (activePrimeOrderElements 2 P).card ≤
          4 * (Nat.card (P ⧸ Subgroup.center P) - 1) := by
        omega
      _ ≤ r ^ d - 1 := hordinary
  · subst r
    subst d
    norm_num at hedge ⊢
    omega

/-! ## Consequences of a supplied corrected shape -/

namespace HallBergerTwoCoreShape

variable
  {r d : ℕ} [Fact r.Prime]
  {P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
  [Fintype P]

/-- Once the separately named mixed fixed-rectangle statement is
supplied, every corrected Hall--Berger branch has the required
fixed-rectangle estimate. -/
theorem activeInvolution_fixedVectorSet_sq_le
    (hmixed : MixedCentralProductFixedRectangleStatement)
    (shape : HallBergerTwoCoreShape P)
    (hdeven : Even d)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    (fixedVectorSet x.1).ncard *
        (fixedVectorSet x.1).ncard ≤
      r ^ d := by
  cases shape with
  | cyclic hcyclic =>
      letI : IsCyclic P := hcyclic
      have hcentral : AllInvolutionsCentral P := by
        intro g _hg
        rw [Subgroup.mem_center_iff]
        intro y
        exact mul_comm y g
      have hempty :=
        activePrimeOrderElements_two_eq_empty_of_allInvolutionsCentral
          P hcentral C
      rw [hempty] at hx
      simp at hx
  | extraspecialCyclicProduct hcommutator =>
      exact
        activeInvolution_fixedVectorSet_sq_le_of_centralCommutator
          hdeven P hcommutator C x hx
  | dihedral k hk e =>
      exact
        activeInvolution_fixedVectorSet_sq_le_of_dihedral
          hdeven hk P e C x hx
  | semidihedral k hk presentation =>
      exact
        activeInvolution_fixedVectorSet_sq_le_of_semidihedral
          hdeven hk P presentation C x hx
  | generalizedQuaternion n hn e =>
      letI : NeZero n := ⟨hn.ne'⟩
      have hempty :=
        activePrimeOrderElements_two_eq_empty_of_quaternion P e C
      rw [hempty] at hx
      simp at hx
  | mixedMaximalClass data =>
      exact hmixed P ⟨data⟩ hdeven C x hx

/-- The already formalized branches reduce the active count to zero, one
normal-form parameter, or the cyclic-head central-commutator count.  The
last disjunct exposes the genuinely mixed branch rather than silently
dismissing it. -/
theorem active_card_zero_or_explicit_or_centralCommutator_or_mixed
    (shape : HallBergerTwoCoreShape P)
    (C : CenterFixedPointFreeAction r d P) :
    (activePrimeOrderElements 2 P).card = 0 ∨
      (∃ k : ℕ,
        (activePrimeOrderElements 2 P).card ≤ 4 * k) ∨
      HasCentralCommutatorOfOrderTwo P ∨
      (∃ data : BergerMixedCentralProductData P,
        shape = .mixedMaximalClass data) := by
  cases shape with
  | cyclic hcyclic =>
      left
      letI : IsCyclic P := hcyclic
      have hcentral : AllInvolutionsCentral P := by
        intro g _hg
        rw [Subgroup.mem_center_iff]
        intro y
        exact mul_comm y g
      rw [activePrimeOrderElements_two_eq_empty_of_allInvolutionsCentral
        P hcentral C]
      simp
  | extraspecialCyclicProduct hcommutator =>
      exact Or.inr (Or.inr (Or.inl hcommutator))
  | dihedral k hk e =>
      exact Or.inr (Or.inl
        ⟨k,
          card_activePrimeOrderElements_two_le_of_dihedral
            (by omega) P e C⟩)
  | semidihedral k hk presentation =>
      exact Or.inr (Or.inl
        ⟨k,
          card_activePrimeOrderElements_two_le_of_semidihedral
            hk P presentation C⟩)
  | generalizedQuaternion n hn e =>
      left
      letI : NeZero n := ⟨hn.ne'⟩
      rw [activePrimeOrderElements_two_eq_empty_of_quaternion P e C]
      simp
  | mixedMaximalClass data =>
      exact Or.inr (Or.inr (Or.inr ⟨data, rfl⟩))

end HallBergerTwoCoreShape

end LisiSabatini
