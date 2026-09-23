module

public import LisiSabatini.CyclicCenterSymplectic
public import LisiSabatini.OperatorFixedSpaceCycle
public import LisiSabatini.CentralCosetActiveCount
public import LisiSabatini.QuasiprimitivePrimeCoreCore

/-!
# Unsplit cyclic-center rows from fixed-point-free center action

The scalar realization used in `CyclicCenterFixedSpaceRow` is stronger than
the fixed-space argument needs.  This file retains only the intrinsic
condition that every nonidentity element of the full center fixes no
nonzero vector.  The commutator cycle is then handled by the operator-valued
cycle theorem, so no central element need split over the prime field.

This proves the sharp active-element and fixed-space bounds for an odd
class-two `q`-group with cyclic center.  To package the current `a = 1`
prime-core row, `q ∣ r - 1` remains an explicit arithmetic input: center
fixed-point-freeness alone does not imply it (a nonsplit cyclic action can
have degree greater than one).
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped commutatorElement

set_option backward.isDefEq.respectTransparency false

local instance finiteConcreteLinearSubgroupForCyclicCenterOperatorRow
    (r d : ℕ) [NeZero r]
    (H : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    Finite H :=
  finite_linearSubgroup_of_finite H

/-- The weakest center-action hypothesis used by the unsplit row: every
nonidentity central element fixes only zero.  It contains neither a scalar
character nor a splitting-field assumption. -/
structure CenterFixedPointFreeAction
    (r d : ℕ) [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop where
  fixedPointFree : ∀ (z : Subgroup.center P), z ≠ 1 →
    ∀ v : Fin d → ZMod r, z.1.1.toLinearEquiv v = v → v = 0

namespace CenterFixedPointFreeAction

variable {r d q : ℕ} [Fact r.Prime]
  {P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}

/-- A fixed-point-free action of the entire group restricts to a
fixed-point-free action of its center. -/
theorem of_fixedPointFreeOffZero
    (hP : FixedPointFreeOffZero P) :
    CenterFixedPointFreeAction r d P := by
  refine ⟨?_⟩
  intro z hz v hfix
  have hzP : (z.1 : P) ≠ 1 := by
    intro h
    apply hz
    exact Subtype.ext h
  apply hP z.1 hzP v
  exact hfix

/-- No active element belongs to a center acting fixed-point-freely. -/
theorem active_not_mem_center
    [Fintype P]
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ nonzeroFixingElements P) :
    x ∉ Subgroup.center P := by
  intro hxcenter
  obtain ⟨hxne, v, hvfix, hvne⟩ :=
    (mem_nonzeroFixingElements P x).mp hx
  have hfix : x.1.toLinearEquiv v = v := by
    exact hvfix
  exact hvne (C.fixedPointFree ⟨x, hxcenter⟩
    (by simpa using hxne) v hfix)

/-- In the unsplit class-two core, every active element has `q`-th power
one.  Its `q`-th power is central, and fixes the same nonzero vector. -/
theorem active_pow_prime_eq_one
    [Fintype P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ nonzeroFixingElements P) :
    x ^ q = 1 := by
  obtain ⟨_hxne, v, hvfix, hvne⟩ :=
    (mem_nonzeroFixingElements P x).mp hx
  let z : Subgroup.center P := ⟨x ^ q, hP.pow_prime_mem_center x⟩
  have hzfix : z.1.1.toLinearEquiv v = v := by
    have hpowfix : ∀ n : ℕ, x.1 ^ n • v = v := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          rw [pow_succ, mul_smul, hvfix, ih]
    change ((x ^ q : P).1 : LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r)).toLinearEquiv v = v
    exact hpowfix q
  by_contra hz
  have hzsub : z ≠ 1 := by
    intro heq
    apply hz
    exact congrArg Subtype.val heq
  exact hvne (C.fixedPointFree z hzsub v hzfix)

/-- The canonical inclusion of the central prime kernel into the center. -/
def centerPrimeKernelToCenter
    (q : ℕ) (G : Type*) [Group G] :
    centerPrimeKernel q G →* Subgroup.center G :=
  Subgroup.inclusion (centerPrimeKernel_le_center q G)

/-- A nontrivial element of the canonical central order-`q` kernel has
order exactly `q`. -/
theorem orderOf_centerPrimeKernel_eq_prime
    {q : ℕ} {G : Type*} [Group G] [Finite G]
    (hP : IsOddCyclicCenterClassTwo q G)
    (z : centerPrimeKernel q G) (hz : z ≠ 1) :
    orderOf z = q := by
  have hzpow : z ^ q = 1 := by
    apply Subtype.ext
    exact hP.commutator_pow_prime_eq_one
      ⟨z, by rw [hP.commutator_eq_centerPrimeKernel]; exact z.2⟩
  have horderDvd : orderOf z ∣ q :=
    orderOf_dvd_of_pow_eq_one hzpow
  have horderNeOne : orderOf z ≠ 1 := by
    intro ho
    exact hz (orderOf_eq_one_iff.mp ho)
  exact ((Nat.dvd_prime hP.prime).mp horderDvd).resolve_left horderNeOne

/-- Every active fiber of the quotient by the full center injects into the
canonical central subgroup of order `q`. -/
theorem centralCoset_active_ncard_le_prime
    [Fintype P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (C : CenterFixedPointFreeAction r d P)
    (c : P ⧸ Subgroup.center P) :
    {x : P | x ∈ nonzeroFixingElements P ∧
      QuotientGroup.mk' (Subgroup.center P) x = c}.ncard ≤ q := by
  classical
  let S : Set P := {x : P | x ∈ nonzeroFixingElements P ∧
    QuotientGroup.mk' (Subgroup.center P) x = c}
  by_cases hS : S.Nonempty
  · let x₀ : S := ⟨Classical.choose hS, Classical.choose_spec hS⟩
    let f : S → centerPrimeKernel q P := fun x ↦ ⟨x₀.1⁻¹ * x.1, by
      have hxcenter : x₀.1⁻¹ * x.1 ∈ Subgroup.center P := by
        rw [← QuotientGroup.eq_one_iff]
        change (QuotientGroup.mk' (Subgroup.center P) x₀.1)⁻¹ *
          QuotientGroup.mk' (Subgroup.center P) x.1 = 1
        rw [x₀.2.2, x.2.2, inv_mul_cancel]
      let z : Subgroup.center P := ⟨x₀.1⁻¹ * x.1, hxcenter⟩
      have hx₀pow := C.active_pow_prime_eq_one hP x₀.1 x₀.2.1
      have hxpow := C.active_pow_prime_eq_one hP x.1 x.2.1
      have hcomm : Commute x₀.1 z.1 :=
        Subgroup.mem_center_iff.mp z.2 x₀.1
      have hx_eq : x.1 = x₀.1 * z.1 := by
        dsimp only [z]
        group
      have hzpow : z ^ q = 1 := by
        apply Subtype.ext
        have hmul := hcomm.mul_pow q
        rw [← hx_eq, hxpow, hx₀pow, one_mul] at hmul
        exact hmul.symm
      apply Subgroup.mem_map.mpr
      refine ⟨z, ?_, rfl⟩
      exact MonoidHom.mem_ker.mpr hzpow⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hval := congrArg Subtype.val hxy
      dsimp only [f] at hval
      exact mul_left_cancel hval
    calc
      S.ncard = Nat.card S := Nat.card_coe_set_eq S
      _ ≤ Nat.card (centerPrimeKernel q P) :=
        Nat.card_le_card_of_injective f hf
      _ = q := hP.card_centerPrimeKernel
  · change S.ncard ≤ q
    rw [Set.not_nonempty_iff_eq_empty.mp hS]
    simp

/-! ## Operator-valued commutator cycles -/

set_option synthInstance.maxHeartbeats 100000 in
-- Nested center-kernel subtypes require extra deterministic instance search.
/-- The commutator pairing supplies the sharp fixed-space estimate without
identifying the central order-`q` element with a scalar in `ZMod r`. -/
theorem active_fixed_le_of_cyclicCenterClassTwo
    [Fintype P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ nonzeroFixingElements P) :
    (nonzeroFixedVectorSet x.1).ncard ≤ r ^ (d / q) - 1 := by
  have hxnotcenter : x ∉ Subgroup.center P :=
    C.active_not_mem_center x hx
  have hnotall : ¬ ∀ y : P, hP.kernelCommutator x y = 1 := by
    intro hall
    exact hxnotcenter ((hP.kernelCommutator_left_radical x).mp hall)
  push Not at hnotall
  obtain ⟨y, hy⟩ := hnotall
  let zK : centerPrimeKernel q P := hP.kernelCommutator x y
  let zC : Subgroup.center P := centerPrimeKernelToCenter q P zK
  have hzKne : zK ≠ 1 := by simpa only [zK] using hy
  have hzKorder : orderOf zK = q :=
    orderOf_centerPrimeKernel_eq_prime hP zK hzKne
  have hgroup : x * y = (zK : P) * y * x := by
    change x * y = ⁅x, y⁆ * y * x
    simp only [commutatorElement_def]
    group
  have hxy : x.1 * y.1 = (zK : P).1 * y.1 * x.1 :=
    congrArg Subtype.val hgroup
  have hzcenter : (zK : P) ∈ Subgroup.center P :=
    centerPrimeKernel_le_center q P zK.2
  have hxzP : Commute x (zK : P) :=
    Subgroup.mem_center_iff.mp hzcenter x
  have hyzP : Commute y (zK : P) :=
    Subgroup.mem_center_iff.mp hzcenter y
  have hxz : Commute x.1 (zK : P).1 := hxzP.map P.subtype
  have hzy : Commute (zK : P).1 y.1 := hyzP.symm.map P.subtype
  have hzqP : (zK : P) ^ q = 1 := by
    exact hP.commutator_pow_prime_eq_one
      ⟨zK, by rw [hP.commutator_eq_centerPrimeKernel]; exact zK.2⟩
  have hzq : (zK : P).1 ^ q = 1 := congrArg Subtype.val hzqP
  apply ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_GL_fixedPointFree_cycle
    hP.prime.pos x.1 y.1 (zK : P).1 hxy hxz hzy hzq
  intro k hkpos hklt v hfix
  have hpowneK : zK ^ k ≠ 1 := by
    apply pow_ne_one_of_lt_orderOf hkpos.ne'
    simpa only [hzKorder] using hklt
  have hpowne : zC ^ k ≠ 1 := by
    intro hpow
    apply hpowneK
    apply (Subgroup.inclusion_injective
      (centerPrimeKernel_le_center q P))
    exact hpow
  apply C.fixedPointFree (zC ^ k) hpowne v
  exact hfix

/-! ## Global active-element budget -/

/-- Counting only nonidentity central cosets gives the sharp
`q^(2*n+1)-1` active-element bound. -/
theorem card_nonzeroFixingElements_le_prime_pow_two_mul_add_one_sub_one
    [Fintype P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (C : CenterFixedPointFreeAction r d P)
    {n : ℕ}
    (hquot : Nat.card (P ⧸ Subgroup.center P) = q ^ (2 * n)) :
    (nonzeroFixingElements P).card ≤ q ^ (2 * n + 1) - 1 := by
  classical
  let Q := P ⧸ Subgroup.center P
  have hmaps : ∀ x ∈ nonzeroFixingElements P,
      QuotientGroup.mk' (Subgroup.center P) x ∈
        (Finset.univ.erase 1 : Finset Q) := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hqone
    apply C.active_not_mem_center x hx
    rw [← QuotientGroup.eq_one_iff]
    exact hqone
  have hfiber : ∀ c ∈ (Finset.univ.erase 1 : Finset Q),
      ((nonzeroFixingElements P).filter fun x ↦
        QuotientGroup.mk' (Subgroup.center P) x = c).card ≤ q := by
    intro c _hc
    simpa [← Set.ncard_coe_finset] using
      C.centralCoset_active_ncard_le_prime hP c
  have hcount := Finset.card_le_card_mul_of_fiber_card_le
    (nonzeroFixingElements P)
    (QuotientGroup.mk' (Subgroup.center P))
    (Finset.univ.erase 1 : Finset Q) q hmaps hfiber
  have hQcard : Fintype.card Q = q ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card]
    exact hquot
  have hpre : (nonzeroFixingElements P).card ≤
      (q ^ (2 * n) - 1) * q := by
    dsimp only [Q] at hQcard hcount
    have herase :
        (Finset.univ.erase 1 :
          Finset (P ⧸ Subgroup.center P)).card =
            Fintype.card (P ⧸ Subgroup.center P) - 1 := by
      simp
    rw [herase, hQcard] at hcount
    exact hcount
  have hpowpos : 0 < q ^ (2 * n) := pow_pos hP.prime.pos _
  have hstrict : (q ^ (2 * n) - 1) * q < q ^ (2 * n) * q :=
    Nat.mul_lt_mul_of_pos_right
      (Nat.sub_one_lt hpowpos.ne') hP.prime.pos
  calc
    (nonzeroFixingElements P).card ≤
        (q ^ (2 * n) - 1) * q := hpre
    _ ≤ q ^ (2 * n) * q - 1 := Nat.le_sub_one_of_lt hstrict
    _ = q ^ (2 * n + 1) - 1 := by rw [pow_succ]

/-- Rank-normalized active-element bound from the intrinsic symplectic
quotient of the unsplit cyclic-center core. -/
theorem card_nonzeroFixingElements_le_cyclicCenterStructuralRank_bound
    [Fintype P]
    (hP : IsOddCyclicCenterClassTwo q P)
    (C : CenterFixedPointFreeAction r d P) :
    (nonzeroFixingElements P).card ≤
      q ^ (2 * hP.cyclicCenterStructuralRank + 1) - 1 := by
  exact C.card_nonzeroFixingElements_le_prime_pow_two_mul_add_one_sub_one
    hP hP.cyclicCenterStructuralRank_card_quotient_center

end CenterFixedPointFreeAction

/-! ## Quasiprimitive source of the center hypothesis -/

/-- Quasiprimitivity makes the center of an embedded cross-characteristic
prime core fixed-point-free.  The proof transports the center through the
injective inclusion of the abstract `pCore` and applies the existing normal
abelian subgroup theorem to `pCoreCenter`. -/
theorem centerFixedPointFreeAction_pCore_of_quasiprimitive
    {r d q : ℕ} [Fact r.Prime]
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hq : Nat.Prime q) (hqr : q ≠ r)
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    CenterFixedPointFreeAction r d
      ((pCore q K).map K.subtype) := by
  let Q : Subgroup K := pCore q K
  let P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
    Q.map K.subtype
  have hfp : FixedPointFreeOffZero
      ((pCoreCenter q K).map K.subtype) :=
    map_normalAbelianPSubgroup_fixedPointFree_of_quasiprimitive
      (Fact.out : r.Prime) hq hqr hqp (pCoreCenter q K)
      inferInstance (pCoreCenter_isPGroup q K)
      (pCoreCenter_pairwise_commute q K)
  change CenterFixedPointFreeAction r d P
  refine ⟨?_⟩
  intro z hz v hfix
  obtain ⟨k, hkQ, hkz⟩ := z.1.2
  let kQ : Q := ⟨k, hkQ⟩
  have hkcenter : kQ ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro y
    let yP : P := ⟨y.1.1, by
      apply Subgroup.mem_map.mpr
      exact ⟨y.1, y.2, rfl⟩⟩
    have hyz : yP * z.1 = z.1 * yP :=
      Subgroup.mem_center_iff.mp z.2 yP
    apply Subtype.ext
    apply K.subtype_injective
    have hyzval := congrArg Subtype.val hyz
    change y.1.1 * z.1.1 = z.1.1 * y.1.1 at hyzval
    change y.1.1 * k.1 = k.1 * y.1.1
    change k.1 = z.1.1 at hkz
    simpa only [hkz] using hyzval
  have hkCenterImage : k ∈ pCoreCenter q K := by
    apply Subgroup.mem_map.mpr
    exact ⟨kQ, hkcenter, rfl⟩
  let g : (pCoreCenter q K).map K.subtype :=
    ⟨z.1.1, by
      apply Subgroup.mem_map.mpr
      exact ⟨k, hkCenterImage, hkz⟩⟩
  have hgne : g ≠ 1 := by
    intro hg
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    have hgval := congrArg Subtype.val hg
    exact hgval
  apply hfp g hgne v
  exact hfix

end LisiSabatini
