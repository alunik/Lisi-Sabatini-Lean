import LisiSabatini.QuasiprimitiveRepresentation
import LisiSabatini.FixedPointFreeOffZero
import LisiSabatini.FiniteLinearSubgroup

/-!
# Core prime-core consequences of quasiprimitivity

This module contains only the structural fixed-point-free, cyclicity, center,
and admissibility facts used by the publication proof. Automatic mixed-profile
constructors remain in the compatibility profile module.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- The order of a finite `q`-group is nonzero in characteristic `r` when
`r` and `q` are distinct primes. -/
theorem natCard_cast_ne_zero_of_isPGroup_of_distinct_primes
    {r q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {A : Type*} [Group A] [Finite A] (hA : IsPGroup q A) :
    (Nat.card A : ZMod r) ≠ 0 := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  have hr_not_dvd_q : ¬ r ∣ q := by
    intro hdvd
    rcases (Nat.dvd_prime hq).mp hdvd with hrOne | hrq
    · exact hr.ne_one hrOne
    · exact hqr hrq.symm
  have hqcast : (q : ZMod r) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hr_not_dvd_q
  obtain ⟨e, hcard⟩ := IsPGroup.iff_card.mp hA
  rw [hcard, Nat.cast_pow]
  exact pow_ne_zero e hqcast

/-- A normal commuting `q`-subgroup of a quasiprimitive concrete linear
group acts fixed-point-freely after mapping to the ambient general linear
group. -/
theorem map_normalAbelianPSubgroup_fixedPointFree_of_quasiprimitive
    {r d q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (H : Subgroup K) (hHnormal : H.Normal) (hHp : IsPGroup q H)
    (hHcomm : ∀ a b : H, Commute a b) :
    FixedPointFreeOffZero (H.map K.subtype) := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : Finite K := finite_linearSubgroup_of_finite K
  letI : Finite H := inferInstance
  letI : NeZero (Nat.card H : ZMod r) :=
    ⟨natCard_cast_ne_zero_of_isPGroup_of_distinct_primes
      hr hq hqr hHp⟩
  let rho : Representation (ZMod r) H (Fin d → ZMod r) :=
    (linearSubgroupRepresentation K).comp H.subtype
  have hrhoFaith : Function.Injective rho :=
    (linearSubgroupRepresentation_faithful K).comp H.subtype_injective
  have hrhoFixedPointFree :=
    fixedPointFree_of_faithful_isIsotypic_of_commuting
      rho (hqp.2 H hHnormal).2 hHcomm hrhoFaith
  rintro ⟨g, hg⟩ hgOne x hfix
  obtain ⟨h, hh, rfl⟩ := hg
  let hH : H := ⟨h, hh⟩
  have hHOne : hH ≠ 1 := by
    intro heq
    apply hgOne
    apply Subtype.ext
    change (h : LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r)) = 1
    have hEqK : h = 1 := congrArg Subtype.val heq
    exact congrArg Subtype.val hEqK
  exact hrhoFixedPointFree hH hHOne x hfix

/-- The same hypotheses force the abstract normal commuting `q`-subgroup
itself to be cyclic. -/
theorem normalAbelianPSubgroup_isCyclic_of_quasiprimitive
    {r d q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (H : Subgroup K) (hHnormal : H.Normal) (hHp : IsPGroup q H)
    (hHcomm : ∀ a b : H, Commute a b) :
    IsCyclic H := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  letI : Finite K := finite_linearSubgroup_of_finite K
  letI : Finite H := inferInstance
  letI : NeZero (Nat.card H : ZMod r) :=
    ⟨natCard_cast_ne_zero_of_isPGroup_of_distinct_primes
      hr hq hqr hHp⟩
  let rho : Representation (ZMod r) H (Fin d → ZMod r) :=
    (linearSubgroupRepresentation K).comp H.subtype
  exact isCyclic_of_faithful_isIsotypic_of_commuting
    rho (hqp.2 H hHnormal).2 hHcomm
      ((linearSubgroupRepresentation_faithful K).comp
        H.subtype_injective)

/-- Pairwise commutativity of the abstract `q`-core. -/
def IsCommutingPrimeCore
    {r d : ℕ}
    (q : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop :=
  ∀ a b : pCore q K, Commute a b

/-- Every commuting cross-characteristic prime core of a quasiprimitive
action lies on the automatic profile's fixed-point-free side. -/
theorem pCore_fixedPointFree_of_quasiprimitive_of_commuting
    {r d q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcomm : IsCommutingPrimeCore q K) :
    FixedPointFreeOffZero ((pCore q K).map K.subtype) :=
  map_normalAbelianPSubgroup_fixedPointFree_of_quasiprimitive
    hr hq hqr hqp (pCore q K) inferInstance
      (pCore_isPGroup q K) hcomm

/-- Every commuting cross-characteristic prime core of a quasiprimitive
action is cyclic. -/
theorem pCore_isCyclic_of_quasiprimitive_of_commuting
    {r d q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K)
    (hcomm : IsCommutingPrimeCore q K) :
    IsCyclic (pCore q K) :=
  normalAbelianPSubgroup_isCyclic_of_quasiprimitive
    hr hq hqr hqp (pCore q K) inferInstance
      (pCore_isPGroup q K) hcomm

/-- The center of a prime core, embedded back into the acting group. -/
def pCoreCenter
    {r d : ℕ}
    (q : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    Subgroup K :=
  (Subgroup.center (pCore q K)).map (pCore q K).subtype

/-- The embedded center of a prime core is normal in the acting group. -/
instance pCoreCenter_normal
    {r d : ℕ} (q : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    (pCoreCenter q K).Normal := by
  exact ConjAct.normal_of_characteristic_of_normal

/-- The embedded center remains a `q`-group. -/
theorem pCoreCenter_isPGroup
    {r d : ℕ} (q : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    IsPGroup q (pCoreCenter q K) := by
  exact ((pCore_isPGroup q K).to_subgroup
    (Subgroup.center (pCore q K))).map (pCore q K).subtype

/-- The embedded center is pairwise commuting. -/
theorem pCoreCenter_pairwise_commute
    {r d : ℕ} (q : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) :
    ∀ a b : pCoreCenter q K, Commute a b := by
  letI : IsMulCommutative (Subgroup.center (pCore q K)) :=
    Subgroup.center.isMulCommutative (pCore q K)
  letI : IsMulCommutative (pCoreCenter q K) :=
    Subgroup.map_isMulCommutative
      (Subgroup.center (pCore q K)) (pCore q K).subtype
  intro a b
  exact Commute.all a b

/-- Quasiprimitivity makes the embedded center of every
cross-characteristic prime core cyclic. -/
theorem pCoreCenter_isCyclic_of_quasiprimitive
    {r d q : ℕ} (hr : Nat.Prime r) (hq : Nat.Prime q) (hqr : q ≠ r)
    {K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    IsCyclic (pCoreCenter q K) :=
  normalAbelianPSubgroup_isCyclic_of_quasiprimitive
    hr hq hqr hqp (pCoreCenter q K) inferInstance
      (pCoreCenter_isPGroup q K) (pCoreCenter_pairwise_commute q K)

/-- The admissible active prime cores that genuinely require a nonabelian
row certificate. -/
def IsAdmissibleNoncommutingPrimeCore
    (r d q : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))) : Prop :=
  Nat.Prime q ∧ q ≠ 2 ∧ q ≠ r ∧
    (pCore q K).map K.subtype ≠ ⊥ ∧
      ¬ IsCommutingPrimeCore q K

end LisiSabatini
