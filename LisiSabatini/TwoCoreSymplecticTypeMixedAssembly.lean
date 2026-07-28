module

public import LisiSabatini.TwoCoreSymplecticTypeExtraspecialCount
public import LisiSabatini.TwoCoreSymplecticTypeHeadFieldAssembly
public import LisiSabatini.TwoCoreSymplecticTypeMixedArithmetic
public import LisiSabatini.TwoCoreSymplecticTypeRepresentationComparison

/-!
# Assembly of the mixed symplectic-type two-core bounds

The finite central-product count and the head arithmetic are combined
here.  After the intrinsic extraspecial square count, the sole remaining
input is the characteristic-two Stone--von Neumann/head-field degree
datum.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- A nontrivial central involution lying in the derived subgroup forces
even dimension in odd characteristic. -/
theorem even_dimension_of_centralInvolution_mem_commutator
    {r d : ℕ} [Fact r.Prime]
    (hrTwo : r ≠ 2)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (C : CenterFixedPointFreeAction r d P)
    (z : Subgroup.center P)
    (hzNe : z ≠ 1) (hzSq : z ^ 2 = 1)
    (hzComm : z.1 ∈ commutator P) :
    Even d := by
  have hzOperator :
      z.1.1.1 =
        -(1 : Module.End (ZMod r) (Fin d → ZMod r)) :=
    centralInvolution_eq_neg_one_of_centerFixedPointFree
      P C z hzNe hzSq
  let detP : P →* (ZMod r)ˣ :=
    LinearEquiv.det.comp
      ((LinearMap.GeneralLinearGroup.generalLinearEquiv
        (ZMod r) (Fin d → ZMod r)).toMonoidHom.comp
          P.subtype)
  have hzDetUnits : detP z.1 = 1 :=
    MonoidHom.mem_ker.mp
      (Abelianization.commutator_subset_ker detP hzComm)
  have hzDet := congrArg Units.val hzDetUnits
  dsimp only [detP] at hzDet
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    LinearEquiv.coe_det] at hzDet
  have hzDet' : LinearMap.det z.1.1.1 = 1 := by
    simpa using hzDet
  have hnegAsSmul :
      -(1 : Module.End (ZMod r) (Fin d → ZMod r)) =
        (-1 : ZMod r) •
          (1 : Module.End (ZMod r) (Fin d → ZMod r)) := by
    ext v i
    simp
  have hpow : (-1 : ZMod r) ^ d = 1 := by
    rw [hzOperator, hnegAsSmul, LinearMap.det_smul] at hzDet'
    simpa using hzDet'
  have hnegOne : (-1 : ZMod r) ≠ 1 := by
    intro h
    have htwo : (2 : ZMod r) = 0 := by
      calc
        (2 : ZMod r) = 1 + 1 := by norm_num
        _ = 1 + -1 :=
          congrArg (fun t : ZMod r ↦ 1 + t) h.symm
        _ = 0 := by simp
    exact
      (two_ne_zero_zmod_of_prime_ne_two
        (Fact.out : r.Prime) hrTwo) htwo
  exact (neg_one_pow_eq_one_iff_even hnegOne).mp hpow

namespace BergerMixedCentralProductData

variable {r d : ℕ} [Fact r.Prime]
  (P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
  [Fintype P]

/-- The extraspecial central involution of a mixed product lies in the
derived subgroup of the ambient group. -/
private theorem extraspecialCentralInvolution_mem_commutator
    {Q : Type*} [Group Q] [Finite Q]
    (data : BergerMixedCentralProductData Q)
    (e : ℕ)
    (extra : ExtraspecialTwoSquareCountData
      data.extraspecialPart e) :
    extra.centralInvolution.1.1 ∈ commutator Q := by
  have hzExtra :
      extra.centralInvolution.1 ∈
        commutator data.extraspecialPart := by
    rw [data.extraspecial.commutator_eq_center]
    exact extra.centralInvolution.2
  have hzMap :
      extra.centralInvolution.1.1 ∈
        (commutator data.extraspecialPart).map
          data.extraspecialPart.subtype := by
    exact ⟨extra.centralInvolution.1, hzExtra, rfl⟩
  rw [Subgroup.map_subtype_commutator] at hzMap
  exact
    (Subgroup.commutator_mono
      (show data.extraspecialPart ≤ ⊤ from le_top)
      (show data.extraspecialPart ≤ ⊤ from le_top)) hzMap

/-- The complete mixed half-density pair, conditional only on the
head-field degree datum. -/
theorem halfDensity_of_headFieldData
    (hrTwo : r ≠ 2)
    (data : BergerMixedCentralProductData P)
    (e : ℕ) (he : 2 ≤ e)
    (hcard :
      Nat.card data.extraspecialPart = 2 * e * e)
    (C : CenterFixedPointFreeAction r d P)
    (H : MixedCentralProductHeadFieldData data e) :
    2 * (activePrimeOrderElements 2 P).card ≤
        r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d := by
  let extra :=
    data.extraspecial.extraspecialTwoSquareCountData e hcard
  let z : Subgroup.center P :=
    ⟨extra.centralInvolution.1.1,
      data.extraspecialCenter_le_center
        extra.centralInvolution⟩
  have hzNe : z ≠ 1 := by
    intro hz
    apply extra.centralInvolution_ne_one
    apply Subtype.ext
    apply Subtype.ext
    simpa only [z] using
      congrArg (fun w : Subgroup.center P ↦ w.1) hz
  have hzSq : z ^ 2 = 1 := by
    apply Subtype.ext
    exact congrArg
      (fun w : Subgroup.center data.extraspecialPart ↦
        w.1.1) extra.centralInvolution_sq
  have hzComm : z.1 ∈ commutator P := by
    exact data.extraspecialCentralInvolution_mem_commutator
      e extra
  have hdeven : Even d :=
    even_dimension_of_centralInvolution_mem_commutator
      hrTwo P C z hzNe hzSq hzComm
  constructor
  · have hactive :=
      data.active_card_le_countingEnvelope_of_extraspecialOrder
        P e hcard
    exact (Nat.mul_le_mul_left 2 hactive).trans
      (two_mul_countingEnvelope_le_nonzero_of_headFieldData
        hrTwo data e he H)
  · intro g hg
    exact mixedCentralProductFixedRectangle
      P ⟨data⟩ hdeven C g hg

/-- The complete mixed half-density pair for a homogeneous faithful
odd-characteristic representation, given an explicit extraspecial
degree. -/
theorem halfDensity_of_homogeneous_of_degree
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hP : IsPGroup 2 P)
    (data : BergerMixedCentralProductData P)
    (e : ℕ) (he : 2 ≤ e)
    (hcard :
      Nat.card data.extraspecialPart = 2 * e * e)
    (hhom :
      Representation.IsHomogeneous
        (linearSubgroupRepresentation P))
    (C : CenterFixedPointFreeAction r d P) :
    2 * (activePrimeOrderElements 2 P).card ≤
        r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d := by
  let H :=
    (data.headFieldData P e hP hrTwo hd he hcard hhom).some
  exact
    data.halfDensity_of_headFieldData
      P hrTwo e he hcard C H

/-- The complete mixed half-density pair for a homogeneous faithful
odd-characteristic representation.

The extraspecial degree and its cardinal identity are intrinsic and are
derived from the extraspecial factor rather than supplied by the caller. -/
theorem halfDensity_of_homogeneous
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (hP : IsPGroup 2 P)
    (data : BergerMixedCentralProductData P)
    (hhom :
      Representation.IsHomogeneous
        (linearSubgroupRepresentation P))
    (C : CenterFixedPointFreeAction r d P) :
    2 * (activePrimeOrderElements 2 P).card ≤
        r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d := by
  obtain ⟨e, he, hcard⟩ :=
    data.extraspecial.exists_degree_card_eq_two_mul_sq
  exact data.halfDensity_of_homogeneous_of_degree
    P hrTwo hd hP e he hcard hhom C

end BergerMixedCentralProductData

end LisiSabatini
