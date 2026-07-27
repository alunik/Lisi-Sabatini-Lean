import LisiSabatini.TwoCoreSymplecticTypeHeadField
import LisiSabatini.QuasiprimitivePrimeCoreCore

/-!
# Assembly of the mixed head-field degree

This file combines the homogeneous extraspecial restriction, the exact
extraspecial Schur degree, and the free rotation action on the
multiplicity space.
-/

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

namespace BergerMixedCentralProductData

variable {r d : ℕ} [Fact r.Prime]
  (P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
  [Finite P]

set_option maxHeartbeats 1500000 in
-- The orbit action and its exact finite-cardinality calculation elaborate
-- in one dependent theorem over the concrete representation dimension.
set_option synthInstance.maxHeartbeats 100000 in
-- The restricted rotation action is definitionally nested through the
-- homogeneous representation module and needs a larger instance budget.
/-- The head-field data attached to a homogeneous faithful
cross-characteristic mixed central product. -/
theorem headFieldData
    (data : BergerMixedCentralProductData P)
    (e : ℕ)
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2)
    (hd : 0 < d)
    (_he : 2 ≤ e)
    (hcard :
      Nat.card data.extraspecialPart = 2 * e * e)
    (hhom :
      Representation.IsHomogeneous
        (linearSubgroupRepresentation P)) :
    Nonempty (MixedCentralProductHeadFieldData data e) := by
  classical
  letI : Fintype P := Fintype.ofFinite P
  let rhoP :
      Representation (ZMod r) P (Fin d → ZMod r) :=
    linearSubgroupRepresentation P
  let rhoE :
      Representation (ZMod r) data.extraspecialPart
        (Fin d → ZMod r) :=
    rhoP.comp data.extraspecialPart.subtype
  have hEP :
      IsPGroup 2 data.extraspecialPart :=
    hP.to_subgroup data.extraspecialPart
  letI :
      NeZero
        (Nat.card data.extraspecialPart : ZMod r) :=
    ⟨natCard_cast_ne_zero_of_isPGroup_of_distinct_primes
      (Fact.out : r.Prime) Nat.prime_two
      (by omega) hEP⟩
  have hsemi :
      IsSemisimpleModule
        (ZMod r)[data.extraspecialPart]
        rhoE.asModule := by
    infer_instance
  have hhomE :
      Representation.IsHomogeneous rhoE :=
    Representation.isHomogeneous_restrict_of_homogeneous_of_innerConjugation
      rhoP data.extraspecialPart hhom hsemi
      data.extraspecialPart_hasInnerConjugationOn
  let H :=
    homogeneousDimensionData rhoE hd hhomE
  have hfaithE : Function.Injective rhoE :=
    (linearSubgroupRepresentation_faithful P).comp
      data.extraspecialPart.subtype_injective
  obtain ⟨a, ha, hEndCard, hSdim⟩ :=
    HomogeneousDimensionData.exists_extraspecialTwo_schurDegree
      rhoE H hfaithE data.extraspecial hcard
  have hbPos : 0 < H.multiplicity :=
    Nat.pos_of_ne_zero H.multiplicity_neZero.out
  have hbNeOne : H.multiplicity ≠ 1 :=
    data.multiplicity_ne_one P H
  have hbTwo : 2 ≤ H.multiplicity := by
    omega
  have hdim :
      d = e * (a * H.multiplicity) := by
    calc
      d =
          H.multiplicity *
            Module.finrank (ZMod r) H.constituent :=
        H.dimension_eq
      _ = H.multiplicity * (a * e) := by
        rw [hSdim]
      _ = e * (a * H.multiplicity) := by
        ac_rfl
  have habTwo : 2 ≤ a * H.multiplicity := by
    calc
      2 = 1 * 2 := by omega
      _ ≤ a * H.multiplicity :=
        Nat.mul_le_mul (by omega) hbTwo
  let M :=
    H.constituent →ₗ[(ZMod r)[data.extraspecialPart]]
      rhoE.asModule
  letI : Finite rhoE.asModule :=
    rhoE.asModuleEquiv.toEquiv.finite_iff.mpr inferInstance
  letI : Finite H.constituent :=
    Finite.of_injective H.constituent.subtype
      H.constituent.subtype_injective
  letI : Finite M := by
    exact
      Finite.of_injective
        (fun f : M ↦
          (f : H.constituent → rhoE.asModule))
        LinearMap.coe_injective
  letI : DistribMulAction data.headPart M :=
    data.multiplicityMulAction P H.constituent
  let R := Subgroup.zpowers data.head.rotation
  letI : DistribMulAction R M :=
    DistribMulAction.compHom M (Subgroup.subtype R)
  letI : IsCyclic R := inferInstance
  have hRP : IsPGroup 2 R :=
    (hP.to_subgroup data.headPart).to_subgroup R
  let zR : R :=
    ⟨data.head.halfTurn, by
      change
        data.head.rotation ^
            (data.head.rotationOrder / 2) ∈
          Subgroup.zpowers data.head.rotation
      exact
        (Subgroup.zpowers data.head.rotation).pow_mem
          (Subgroup.mem_zpowers data.head.rotation) _⟩
  have hzRNe : zR ≠ 1 := by
    intro hz
    apply data.head.halfTurn_ne_one
    exact congrArg Subtype.val hz
  have hzRSq : zR ^ 2 = 1 := by
    apply Subtype.ext
    exact data.head.halfTurn_sq
  have hzROrder : orderOf zR = 2 := by
    apply orderOf_eq_prime
    · exact hzRSq
    · exact hzRNe
  let extra :=
    data.extraspecial.extraspecialTwoSquareCountData
      e hcard
  have hhalfEnd :=
    data.headRestrictedEnd_halfTurn_eq_neg_one
      P H extra
  have hhalfAction (f : M) :
      data.head.halfTurn • f = -f := by
    apply LinearMap.ext
    intro u
    change
      (data.headRestrictedEnd P data.head.halfTurn).comp
          f u =
        (-f) u
    rw [hhalfEnd]
    change -(f u) = -(f u)
    rfl
  have hzAction (f : M) : zR • f = -f :=
    hhalfAction f
  have htwo : (2 : ZMod r) ≠ 0 :=
    two_ne_zero_zmod_of_prime_ne_two
      (Fact.out : r.Prime) hrTwo
  have hnegFixed (f : M) (hf : -f = f) :
      f = 0 := by
    apply LinearMap.ext
    intro u
    have hfu : -(f u) = f u := by
      simpa using LinearMap.congr_fun hf u
    have hadd : f u + f u = 0 := by
      calc
        f u + f u = -(f u) + f u := by
          rw [hfu]
        _ = 0 := neg_add_cancel (f u)
    have htwoSmul :
        (2 : ZMod r) • f u = 0 := by
      have htwoCast :
          (2 : ZMod r) = 1 + 1 := by
        norm_num
      rw [htwoCast, add_smul, one_smul]
      exact hadd
    exact
      (smul_eq_zero.mp htwoSmul).resolve_left htwo
  let M0 := {f : M // f ≠ 0}
  letI : SMul R M0 :=
    ⟨fun g f ↦
      ⟨g • f.1, by
        intro hzero
        apply f.2
        apply MulAction.injective g
        exact hzero.trans (smul_zero g).symm⟩⟩
  letI : MulAction R M0 :=
    Subtype.coe_injective.mulAction
      (fun f : M0 ↦ (f.1 : M))
      (fun _ _ ↦ rfl)
  letI : Finite M0 := inferInstance
  have hstab (x : M0) :
      MulAction.stabilizer R x = ⊥ := by
    have hxBase :
        MulAction.stabilizer R x.1 = ⊥ :=
      stabilizer_eq_bot_of_cyclic_twoGroup_of_involution_neg
        hRP zR hzROrder hzAction hnegFixed x.1 x.2
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    have hgBase :
        g ∈ MulAction.stabilizer R x.1 := by
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      exact congrArg Subtype.val hg
    rw [hxBase] at hgBase
    simpa using hgBase
  have hdiv :
      Nat.card R ∣ Nat.card M0 :=
    natCard_dvd_natCard_of_stabilizers_bot hstab
  have hRcard :
      Nat.card R = data.head.rotationOrder := by
    dsimp only [R]
    rw [Nat.card_zpowers, data.head.orderOf_rotation]
  have hMcard :
      Nat.card M = r ^ (a * H.multiplicity) := by
    simpa only [M, rhoE] using
      data.natCard_multiplicitySpace
        P H a hEndCard
  have hM0card :
      Nat.card M0 = Nat.card M - 1 := by
    letI : Fintype M := Fintype.ofFinite M
    letI : Fintype M0 := Fintype.ofFinite M0
    rw [Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    change
      Fintype.card {f : M // f ≠ 0} =
        Fintype.card M - 1
    calc
      Fintype.card {f : M // f ≠ 0} =
          Fintype.card M -
            Fintype.card {f : M // f = 0} :=
        Fintype.card_subtype_compl
          (fun f : M ↦ f = 0)
      _ = Fintype.card M - 1 := by
        simp
  have hrotationDvd :
      data.head.rotationOrder ∣
        r ^ (a * H.multiplicity) - 1 := by
    rw [hRcard, hM0card, hMcard] at hdiv
    exact hdiv
  refine
    ⟨{
      fieldDegree := a * H.multiplicity
      fieldDegree_pos := Nat.mul_pos ha hbPos
      rotationOrder_dvd := hrotationDvd
      constituentDimension_le := hdim.ge
      doubledDegree_le := ?_ }⟩
  rw [hdim]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    Nat.mul_le_mul_right e habTwo

end BergerMixedCentralProductData

/-- The exact mixed head-field statement required by the counting
assembly. -/
theorem mixedCentralProductHeadFieldDegree :
    MixedCentralProductHeadFieldDegreeStatement := by
  intro r d _ P _ data e hP hrTwo hd he hcard hhom
  exact
    data.headFieldData P e hP hrTwo hd he hcard hhom

end LisiSabatini
