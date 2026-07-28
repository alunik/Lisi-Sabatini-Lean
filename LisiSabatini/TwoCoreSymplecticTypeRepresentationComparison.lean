module

public import LisiSabatini.TwoCoreSymplecticTypeFrontier
public import LisiSabatini.SchurWeylBasis
public import Mathlib.LinearAlgebra.Center
public import Mathlib.LinearAlgebra.Determinant

/-!
# The representation comparison for symplectic-type two-cores

This file proves the representation-theoretic input isolated in
`TwoCoreSymplecticTypeFrontier`.

The key point is elementary.  If `P'` is central of order two and the
center acts fixed-point-freely in odd characteristic, then the unique
nontrivial element of `P'` acts as `-1`.  Conjugation therefore gives
distinct sign characters on the operators indexed by `P / Z(P)`.  Those
operators are linearly independent in `End(V)`, so

`|P / Z(P)| ≤ (dim V)²`.

The same central involution has determinant one because it belongs to the
derived subgroup, while its action is `-1`; hence `dim V` is even.  These
two facts give the required numerical comparison outside the single
module `F₃²`.
-/

@[expose] public section

noncomputable section

open scoped commutatorElement

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- A nontrivial central involution in a fixed-point-free center acts as
the scalar `-1`. -/
theorem centralInvolution_eq_neg_one_of_centerFixedPointFree
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (C : CenterFixedPointFreeAction r d P)
    (z : Subgroup.center P)
    (hzNe : z ≠ 1) (hzSq : z ^ 2 = 1) :
    z.1.1.1 = -(1 :
      Module.End (ZMod r) (Fin d → ZMod r)) := by
  apply LinearMap.ext
  intro v
  let w : Fin d → ZMod r := z.1.1.1 v + v
  have hwFix : z.1.1.toLinearEquiv w = w := by
    change z.1.1.1 (z.1.1.1 v + v) = z.1.1.1 v + v
    rw [map_add]
    have hzSqGL : z.1.1 ^ 2 = 1 := by
      simpa using congrArg
        (fun x : Subgroup.center P ↦ x.1.1) hzSq
    have hzSqApply := congrArg
      (fun g :
        LinearMap.GeneralLinearGroup
          (ZMod r) (Fin d → ZMod r) ↦ g.1 v) hzSqGL
    rw [show z.1.1.1 (z.1.1.1 v) = v by
      simpa [pow_two] using hzSqApply]
    exact add_comm v (z.1.1.1 v)
  have hwZero : w = 0 :=
    C.fixedPointFree z hzNe w hwFix
  have hzv : z.1.1.1 v = -v := by
    dsimp only [w] at hwZero
    exact eq_neg_of_add_eq_zero_left hwZero
  simpa using hzv

/-- The sign of an element in a subgroup of order two. -/
private def twoCoreElementSign
    {r : ℕ} {P : Type*} [Group P]
    (x : P) : ZMod r := by
  classical
  exact if x = 1 then 1 else -1

/-- On a subgroup of order two, the commutator sign distinguishes
elements in odd characteristic. -/
private theorem twoCoreCommutatorSign_injective
    {r : ℕ} [Fact r.Prime] (hrTwo : r ≠ 2)
    {P : Type*} [Group P] [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (a b : P)
    (ha : a ∈ commutator P) (hb : b ∈ commutator P)
    (hsign :
      twoCoreElementSign (r := r) a =
        twoCoreElementSign (r := r) b) :
    a = b := by
  classical
  have hOneNeg : (1 : ZMod r) ≠ -1 := by
    intro h
    have htwo : (2 : ZMod r) = 0 := by
      calc
        (2 : ZMod r) = 1 + 1 := by norm_num
        _ = -1 + 1 := congrArg (fun t : ZMod r ↦ t + 1) h
        _ = 0 := by simp
    exact (two_ne_zero_zmod_of_prime_ne_two
      (Fact.out : r.Prime) hrTwo) htwo
  have hunique :=
    (Nat.card_eq_two_iff' (1 : commutator P)).mp
      hcomm.card_commutator
  by_cases haOne : a = 1
  · by_cases hbOne : b = 1
    · exact haOne.trans hbOne.symm
    · change (if a = 1 then 1 else -1) =
        (if b = 1 then 1 else -1) at hsign
      rw [if_pos haOne, if_neg hbOne] at hsign
      exact False.elim (hOneNeg hsign)
  · by_cases hbOne : b = 1
    · change (if a = 1 then 1 else -1) =
        (if b = 1 then 1 else -1) at hsign
      rw [if_neg haOne, if_pos hbOne] at hsign
      exact False.elim (hOneNeg hsign.symm)
    · obtain ⟨z, _hzNe, hzUnique⟩ := hunique
      have haSub : (⟨a, ha⟩ : commutator P) ≠ 1 := by
        intro h
        exact haOne (congrArg Subtype.val h)
      have hbSub : (⟨b, hb⟩ : commutator P) ≠ 1 := by
        intro h
        exact hbOne (congrArg Subtype.val h)
      exact congrArg Subtype.val
        ((hzUnique ⟨a, ha⟩ haSub).trans
          (hzUnique ⟨b, hb⟩ hbSub).symm)

/-- The operator attached to a chosen representative of a central
coset. -/
def twoCoreCentralCosetOperator
    {r d : ℕ}
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (u : P ⧸ Subgroup.center P) :
    Module.End (ZMod r) (Fin d → ZMod r) :=
  (centralQuotientLift u).1.1

/-- Conjugation by a group element on the linear endomorphism algebra. -/
private def twoCoreConjugationOperator
    {r d : ℕ}
    {P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))}
    (g : P) :
    Module.End (ZMod r)
      (Module.End (ZMod r) (Fin d → ZMod r)) where
  toFun f := g.1.1 * f * (g⁻¹).1.1
  map_add' f h := by
    simp only [mul_add, add_mul]
  map_smul' c f := by
    apply LinearMap.ext
    intro v
    change
      g.1.1 (c • f ((g⁻¹).1.1 v)) =
        c • g.1.1 (f ((g⁻¹).1.1 v))
    exact LinearMap.map_smul g.1.1 c _

/-- A central-coset operator is a joint sign eigenvector for
conjugation. -/
private theorem twoCoreConjugationOperator_centralCoset
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (C : CenterFixedPointFreeAction r d P)
    (g : P) (u : P ⧸ Subgroup.center P) :
    twoCoreConjugationOperator g
        (twoCoreCentralCosetOperator P u) =
      twoCoreElementSign (r := r)
          ⁅g, centralQuotientLift u⁆ •
        twoCoreCentralCosetOperator P u := by
  let x : P := centralQuotientLift u
  have hconj :
      g * x * g⁻¹ = ⁅g, x⁆ * x := by
    simp only [commutatorElement_def]
    group
  by_cases hc : ⁅g, x⁆ = 1
  · have hc' : ⁅g, centralQuotientLift u⁆ = 1 := by
      simpa only [x] using hc
    rw [twoCoreElementSign, if_pos hc', one_smul]
    apply LinearMap.ext
    intro v
    change
      (g * x * g⁻¹).1.1 v = x.1.1 v
    rw [hconj, hc, one_mul]
  · have hcMem :
        ⁅g, x⁆ ∈ commutator P :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top g) (Subgroup.mem_top x)
    let c : commutator P := ⟨⁅g, x⁆, hcMem⟩
    let z : Subgroup.center P :=
      ⟨⁅g, x⁆, hcomm.commutator_le_center hcMem⟩
    have hzNe : z ≠ 1 := by
      intro hz
      exact hc (congrArg Subtype.val hz)
    have hcSq : c ^ 2 = 1 := by
      have hpow :
          c ^ Nat.card (commutator P) = 1 :=
        pow_card_eq_one'
      simpa [hcomm.card_commutator] using hpow
    have hzSq : z ^ 2 = 1 := by
      apply Subtype.ext
      simpa only [z, c, Subgroup.coe_pow, Subgroup.coe_one] using
        congrArg Subtype.val hcSq
    have hzOperator :
        z.1.1.1 =
          -(1 : Module.End (ZMod r) (Fin d → ZMod r)) :=
      centralInvolution_eq_neg_one_of_centerFixedPointFree
        P C z hzNe hzSq
    have hc' : ⁅g, centralQuotientLift u⁆ ≠ 1 := by
      simpa only [x] using hc
    rw [twoCoreElementSign, if_neg hc']
    apply LinearMap.ext
    intro v
    change
      (g * x * g⁻¹).1.1 v =
        ((-1 : ZMod r) • x.1.1) v
    rw [hconj]
    change z.1.1.1 (x.1.1 v) =
      ((-1 : ZMod r) • x.1.1) v
    rw [hzOperator]
    simp

/-- Distinct central cosets have distinct joint commutator-sign
characters. -/
private theorem twoCoreJointSign_injective
    {r d : ℕ} [Fact r.Prime] (hrTwo : r ≠ 2)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P) :
    Function.Injective
      (fun u : P ⧸ Subgroup.center P ↦
        fun g : P ↦
          twoCoreElementSign (r := r)
            ⁅g, centralQuotientLift u⁆) := by
  intro u v huv
  let a : P := centralQuotientLift u
  let b : P := centralQuotientLift v
  have hcenter : a / b ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hayMem :
        ⁅y, a⁆ ∈ commutator P :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top y) (Subgroup.mem_top a)
    have hbyMem :
        ⁅y, b⁆ ∈ commutator P :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top y) (Subgroup.mem_top b)
    have hab :
        ⁅y, a⁆ = ⁅y, b⁆ := by
      apply twoCoreCommutatorSign_injective
        (r := r) hrTwo hcomm _ _ hayMem hbyMem
      exact congrFun huv y
    have hbyInvMem :
        ⁅y, b⁻¹⁆ ∈ Subgroup.center P :=
      hcomm.commutator_le_center
        (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top y) (Subgroup.mem_top b⁻¹))
    have hbyInv :
        ⁅y, b⁻¹⁆ = ⁅y, b⁆⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      calc
        ⁅y, b⁆ * ⁅y, b⁻¹⁆ =
            ⁅y, b * b⁻¹⁆ :=
          (commutatorElement_mul_right_of_mem_center
            y b b⁻¹ hbyInvMem).symm
        _ = 1 := by simp
    calc
      ⁅y, a / b⁆ =
          ⁅y, a⁆ * ⁅y, b⁻¹⁆ :=
        commutatorElement_mul_right_of_mem_center
          y a b⁻¹ hbyInvMem
      _ = ⁅y, a⁆ * ⁅y, b⁆⁻¹ := by rw [hbyInv]
      _ = 1 := by rw [hab, mul_inv_cancel]
  calc
    u =
        QuotientGroup.mk' (Subgroup.center P) a :=
      (centralQuotientLift_mk u).symm
    _ = QuotientGroup.mk' (Subgroup.center P) b :=
      QuotientGroup.eq_iff_div_mem.mpr hcenter
    _ = v := centralQuotientLift_mk v

/-- The central-coset operators are linearly independent over the base
field.  No irreducibility or splitting-field hypothesis is needed. -/
theorem linearIndependent_twoCoreCentralCosetOperator
    {r d : ℕ} [Fact r.Prime]
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (C : CenterFixedPointFreeAction r d P) :
    LinearIndependent (ZMod r)
      (twoCoreCentralCosetOperator P) := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  apply linearIndependent_of_joint_eigenvectors
    (fun g : P ↦ twoCoreConjugationOperator g)
    (fun u : P ⧸ Subgroup.center P ↦
      fun g : P ↦
        twoCoreElementSign (r := r)
          ⁅g, centralQuotientLift u⁆)
  · exact twoCoreJointSign_injective hrTwo P hcomm
  · intro u hu
    exact (centralQuotientLift u).1.ne_zero hu
  · intro g u
    exact twoCoreConjugationOperator_centralCoset
      P hcomm C g u

/-- The number of central cosets is at most the dimension of the
endomorphism algebra. -/
theorem natCard_quotientCenter_le_dimension_sq_of_centralCommutator
    {r d : ℕ} [Fact r.Prime]
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (C : CenterFixedPointFreeAction r d P) :
    Nat.card (P ⧸ Subgroup.center P) ≤ d * d := by
  letI : Fintype (P ⧸ Subgroup.center P) :=
    Fintype.ofFinite _
  have hbound :=
    (linearIndependent_twoCoreCentralCosetOperator
      hrTwo hd P hcomm C).fintype_card_le_finrank
  simpa [Nat.card_eq_fintype_card,
    Module.finrank_linearMap] using hbound

/-- The ambient dimension is even.  The nontrivial derived involution is
`-1` by fixed-point-freeness, but its determinant is one because every
homomorphism to an abelian group kills the derived subgroup. -/
theorem even_dimension_of_centralCommutator
    {r d : ℕ} [Fact r.Prime]
    (hrTwo : r ≠ 2)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (C : CenterFixedPointFreeAction r d P) :
    Even d := by
  obtain ⟨c, hcNe, _hcUnique⟩ :=
    (Nat.card_eq_two_iff' (1 : commutator P)).mp
      hcomm.card_commutator
  let z : Subgroup.center P :=
    ⟨c.1, hcomm.commutator_le_center c.2⟩
  have hzNe : z ≠ 1 := by
    intro hz
    apply hcNe
    apply Subtype.ext
    exact congrArg (fun w : Subgroup.center P ↦ w.1) hz
  have hcSq : c ^ 2 = 1 := by
    have hpow :
        c ^ Nat.card (commutator P) = 1 :=
      pow_card_eq_one'
    simpa [hcomm.card_commutator] using hpow
  have hzSq : z ^ 2 = 1 := by
    apply Subtype.ext
    simpa only [z, Subgroup.coe_pow, Subgroup.coe_one] using
      congrArg Subtype.val hcSq
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
  have hcDetUnits : detP c.1 = 1 :=
    MonoidHom.mem_ker.mp
      (Abelianization.commutator_subset_ker detP c.2)
  have hcDet := congrArg Units.val hcDetUnits
  dsimp only [detP] at hcDet
  simp only [MonoidHom.coe_comp, Function.comp_apply,
    LinearEquiv.coe_det]
      at hcDet
  have hcDet' : LinearMap.det c.1.1.1 = 1 := by
    simpa using hcDet
  have hcOperator :
      c.1.1.1 =
        -(1 : Module.End (ZMod r) (Fin d → ZMod r)) := by
    exact hzOperator
  have hnegAsSmul :
      -(1 : Module.End (ZMod r) (Fin d → ZMod r)) =
        (-1 : ZMod r) •
          (1 : Module.End (ZMod r) (Fin d → ZMod r)) := by
    ext v i
    simp
  have hpow : (-1 : ZMod r) ^ d = 1 := by
    rw [hcOperator, hnegAsSmul, LinearMap.det_smul] at hcDet'
    simpa using hcDet'
  have hnegOne : (-1 : ZMod r) ≠ 1 := by
    intro h
    have htwo : (2 : ZMod r) = 0 := by
      calc
        (2 : ZMod r) = 1 + 1 := by norm_num
        _ = 1 + -1 := congrArg (fun t : ZMod r ↦ 1 + t) h.symm
        _ = 0 := by simp
    exact (two_ne_zero_zmod_of_prime_ne_two
      (Fact.out : r.Prime) hrTwo) htwo
  exact (neg_one_pow_eq_one_iff_even hnegOne).mp hpow

/-- A small exponential inequality used after the endomorphism-dimension
bound. -/
private theorem four_mul_sq_le_three_pow
    (d : ℕ) (hd : 4 ≤ d) :
    4 * d * d ≤ 3 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ]
      calc
        4 * (n + 1) * (n + 1) ≤
            3 * (4 * n * n) := by nlinarith
        _ ≤ 3 * 3 ^ n :=
          Nat.mul_le_mul_left 3 ih
        _ = 3 ^ n * 3 := by omega

/-- Apart from `F₃²`, the quotient-size envelope follows solely from
linear independence of central-coset operators and evenness of the
dimension. -/
theorem centralCommutator_representationComparison_ordinary_or_f3Plane
    {r d : ℕ} [Fact r.Prime]
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (C : CenterFixedPointFreeAction r d P) :
    4 * (Nat.card (P ⧸ Subgroup.center P) - 1) ≤
        r ^ d - 1 ∨
      (r = 3 ∧ d = 2) := by
  let Q := Nat.card (P ⧸ Subgroup.center P)
  have hQ :
      Q ≤ d * d :=
    natCard_quotientCenter_le_dimension_sq_of_centralCommutator
      hrTwo hd P hcomm C
  have hdeven :=
    even_dimension_of_centralCommutator
      hrTwo P hcomm C
  have hrThree : 3 ≤ r := by
    have hrTwoLe := (Fact.out : r.Prime).two_le
    omega
  by_cases hdTwo : d = 2
  · subst d
    by_cases hrEq : r = 3
    · exact Or.inr ⟨hrEq, rfl⟩
    · left
      obtain ⟨k, hk⟩ :=
        (Fact.out : r.Prime).odd_of_ne_two hrTwo
      have hrFive : 5 ≤ r := by omega
      have hrSq : 25 ≤ r ^ 2 := by
        rw [pow_two]
        nlinarith
      dsimp only [Q] at hQ ⊢
      norm_num at hQ
      omega
  · left
    obtain ⟨m, hm⟩ := hdeven
    have hdFour : 4 ≤ d := by omega
    have hstrict :
        4 * (Q - 1) < r ^ d := by
      calc
        4 * (Q - 1) < 4 * d * d := by
          have hpred : Q - 1 < d * d := by
            have hdSqPos : 0 < d * d :=
              Nat.mul_pos hd hd
            omega
          simpa [mul_assoc] using
            Nat.mul_lt_mul_of_pos_left hpred
              (by norm_num : 0 < 4)
        _ ≤ 3 ^ d := four_mul_sq_le_three_pow d hdFour
        _ ≤ r ^ d := Nat.pow_le_pow_left hrThree d
    dsimp only [Q] at hstrict ⊢
    omega

end LisiSabatini
