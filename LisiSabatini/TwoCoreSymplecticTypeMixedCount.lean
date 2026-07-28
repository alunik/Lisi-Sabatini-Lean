module

public import LisiSabatini.TwoCoreSymplecticTypeMixedStructure

/-!
# Active-involution bookkeeping for a mixed two-core

The central-product count is separated from the sole extraspecial input:
the two square fibers in an extraspecial `2`-group of order `2e²` have
sizes `e² ± e`.  Only the sign-free consequences are used here: their
sum is `2e²`, and each is at most `e² + e`.

The maximal-class head square fibers are recorded independently.  Once
those finite normal-form counts are supplied, the internal central
product bookkeeping gives the uniform envelope needed by the
odd-characteristic arithmetic.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- Elements with a prescribed square, as a finite type. -/
abbrev SquareFiber
    (G : Type u) [Group G] (a : G) :=
  {x : G // x ^ 2 = a}

/-- The sign-free part of the standard extraspecial involution count. -/
structure ExtraspecialTwoSquareCountData
    (E : Type u) [Group E] [Finite E] (e : ℕ) where
  centralInvolution : Subgroup.center E
  centralInvolution_ne_one : centralInvolution ≠ 1
  centralInvolution_sq : centralInvolution ^ 2 = 1
  square_dichotomy :
    ∀ x : E, x ^ 2 = 1 ∨ x ^ 2 = centralInvolution.1
  card_fibers :
    Nat.card (SquareFiber E 1) +
        Nat.card (SquareFiber E centralInvolution.1) =
      2 * e * e
  card_one_le :
    Nat.card (SquareFiber E 1) ≤ e * e + e
  card_central_le :
    Nat.card (SquareFiber E centralInvolution.1) ≤ e * e + e

namespace BergerMaximalClassHead

variable {H : Type u} [Group H] [Finite H]

/-- Number of square-one elements in the three maximal-class normal
forms. -/
def squareOneCount (head : BergerMaximalClassHead H) : ℕ :=
  let N := head.rotationOrder
  match head with
  | .dihedral _ _ _ => N + 2
  | .semidihedral _ _ _ => N / 2 + 2
  | .generalizedQuaternion _ _ _ => 2

/-- Number of elements squaring to the unique central involution in the
three maximal-class normal forms. -/
def squareCentralCount (head : BergerMaximalClassHead H) : ℕ :=
  let N := head.rotationOrder
  match head with
  | .dihedral _ _ _ => 2
  | .semidihedral _ _ _ => N / 2 + 2
  | .generalizedQuaternion _ _ _ => N + 2

/-- The two finite square-fiber computations for a maximal-class head. -/
structure SquareCountData
    (head : BergerMaximalClassHead H)
    (z : Subgroup.center H) : Prop where
  card_one_le :
    Nat.card (SquareFiber H 1) ≤ head.squareOneCount
  card_central_le :
    Nat.card (SquareFiber H z.1) ≤ head.squareCentralCount

/-- A sign-independent envelope.  Unlike the exact branchwise formula,
this does not require choosing a normalized plus/minus presentation of
the extraspecial factor. -/
def countingEnvelope
    (head : BergerMaximalClassHead H) (e : ℕ) : ℕ :=
  let N := head.rotationOrder
  match head with
  | .dihedral _ _ _ =>
      (N / 2 + 2) * (e * e) + (N / 2) * e
  | .semidihedral _ _ _ =>
      (N / 2 + 2) * (e * e)
  | .generalizedQuaternion _ _ _ =>
      (N / 2 + 2) * (e * e) + (N / 2) * e

end BergerMaximalClassHead

namespace BergerMixedCentralProductData

variable {P : Type u} [Group P] [Finite P]

/-- The extraspecial central involution, viewed in the head through the
amalgamated intersection. -/
def headCentralInvolution
    (data : BergerMixedCentralProductData P)
    {e : ℕ}
    (extra : ExtraspecialTwoSquareCountData
      data.extraspecialPart e) :
    Subgroup.center data.headPart := by
  let z := extra.centralInvolution
  have hzMap :
      z.1.1 ∈
        (Subgroup.center data.extraspecialPart).map
          data.extraspecialPart.subtype := by
    exact ⟨z.1, z.2, rfl⟩
  rw [data.overlap] at hzMap
  let zHead : data.headPart := ⟨z.1.1, hzMap.2⟩
  refine ⟨zHead, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  have hzWhole :
      z.1.1 ∈ Subgroup.center P :=
    data.extraspecialCenter_le_center z
  exact Subgroup.mem_center_iff.mp hzWhole h.1

@[simp]
theorem coe_headCentralInvolution
    (data : BergerMixedCentralProductData P)
    {e : ℕ}
    (extra : ExtraspecialTwoSquareCountData
      data.extraspecialPart e) :
    (data.headCentralInvolution extra).1.1 =
      extra.centralInvolution.1.1 :=
  rfl

theorem headCentralInvolution_ne_one
    (data : BergerMixedCentralProductData P)
    {e : ℕ}
    (extra : ExtraspecialTwoSquareCountData
      data.extraspecialPart e) :
    data.headCentralInvolution extra ≠ 1 := by
  intro hz
  apply extra.centralInvolution_ne_one
  apply Subtype.ext
  apply Subtype.ext
  have hzP :=
    congrArg (fun w : Subgroup.center data.headPart ↦ w.1.1) hz
  exact hzP

theorem headCentralInvolution_sq
    (data : BergerMixedCentralProductData P)
    {e : ℕ}
    (extra : ExtraspecialTwoSquareCountData
      data.extraspecialPart e) :
    data.headCentralInvolution extra ^ 2 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun w :
    Subgroup.center data.extraspecialPart ↦ w.1.1)
      extra.centralInvolution_sq

section Count

variable
  {r d : ℕ} [Fact r.Prime]
  (P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
  [Fintype P]
  (data : BergerMixedCentralProductData P)
  (e : ℕ)
  (extra : ExtraspecialTwoSquareCountData
    data.extraspecialPart e)
  (headCount : data.head.SquareCountData
    (data.headCentralInvolution extra))

private def twistedExtra
    (x : P) (b : Bool) : data.extraspecialPart :=
  if b then
    (data.factor x).1 * extra.centralInvolution.1
  else
    (data.factor x).1

private def twistedHead
    (x : P) (b : Bool) : data.headPart :=
  if b then
    (data.factor x).2 *
      (data.headCentralInvolution extra).1⁻¹
  else
    (data.factor x).2

private theorem twisted_mul
    (x : P) (b : Bool) :
    (twistedExtra P data e extra x b).1 *
        (twistedHead P data e extra x b).1 = x := by
  cases b with
  | false =>
      simp [twistedExtra, twistedHead, data.factor_mul]
  | true =>
      have hcomm :
          extra.centralInvolution.1.1 *
              (data.factor x).2.1 =
            (data.factor x).2.1 *
              extra.centralInvolution.1.1 :=
        data.commute extra.centralInvolution.1 (data.factor x).2
      simp only [twistedExtra, twistedHead, if_true,
        Subgroup.coe_mul, Subgroup.coe_inv,
        coe_headCentralInvolution]
      calc
        ((data.factor x).1.1 *
            extra.centralInvolution.1.1) *
              ((data.factor x).2.1 *
                extra.centralInvolution.1.1⁻¹) =
            (data.factor x).1.1 *
              (extra.centralInvolution.1.1 *
                (data.factor x).2.1) *
                  extra.centralInvolution.1.1⁻¹ := by group
        _ = (data.factor x).1.1 *
              ((data.factor x).2.1 *
                extra.centralInvolution.1.1) *
                  extra.centralInvolution.1.1⁻¹ := by rw [hcomm]
        _ = (data.factor x).1.1 * (data.factor x).2.1 := by group
        _ = x := data.factor_mul x

private theorem twistedExtra_sq
    (x : P) (b : Bool) :
    (twistedExtra P data e extra x b) ^ 2 =
      (data.factor x).1 ^ 2 := by
  cases b with
  | false => simp [twistedExtra]
  | true =>
      have hcomm :
          Commute (data.factor x).1 extra.centralInvolution.1 :=
        Subgroup.mem_center_iff.mp extra.centralInvolution.2
          (data.factor x).1
      have hzSq :
          extra.centralInvolution.1 ^ 2 = 1 :=
        congrArg Subtype.val extra.centralInvolution_sq
      simp only [twistedExtra, if_true]
      rw [hcomm.mul_pow, hzSq, mul_one]

private theorem twistedHead_sq
    (x : P) (b : Bool) :
    (twistedHead P data e extra x b) ^ 2 =
      (data.factor x).2 ^ 2 := by
  cases b with
  | false => simp [twistedHead]
  | true =>
      have hzComm :
          Commute (data.factor x).2
            (data.headCentralInvolution extra).1 :=
        Subgroup.mem_center_iff.mp
          (data.headCentralInvolution extra).2
          (data.factor x).2
      have hcomm :
          Commute (data.factor x).2
            (data.headCentralInvolution extra).1⁻¹ :=
        hzComm.inv_right
      simp only [twistedHead, if_true]
      rw [hcomm.mul_pow]
      have hzSq :
          (data.headCentralInvolution extra).1 ^ 2 = 1 := by
        exact congrArg Subtype.val
          (data.headCentralInvolution_sq extra)
      rw [inv_pow, hzSq, inv_one, mul_one]

private theorem factor_square_dichotomy
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    ((data.factor x).1 ^ 2 = 1 ∧
        (data.factor x).2 ^ 2 = 1) ∨
      ((data.factor x).1 ^ 2 =
          extra.centralInvolution.1 ∧
        (data.factor x).2 ^ 2 =
          (data.headCentralInvolution extra).1) := by
  have hxSq : x ^ 2 = 1 := by
    have hxOrder :=
      (mem_activePrimeOrderElements 2 P x).mp hx |>.1
    rw [← hxOrder]
    exact pow_orderOf_eq_one x
  have hcomm :
      Commute (data.factor x).1.1 (data.factor x).2.1 :=
    data.commute (data.factor x).1 (data.factor x).2
  have hproduct :
      (data.factor x).1.1 ^ 2 *
          (data.factor x).2.1 ^ 2 = 1 := by
    rw [← hcomm.mul_pow, data.factor_mul, hxSq]
  rcases extra.square_dichotomy (data.factor x).1 with
      hone | hcentral
  · left
    refine ⟨hone, ?_⟩
    apply Subtype.ext
    have honeP :
        (data.factor x).1.1 ^ 2 = 1 :=
      congrArg Subtype.val hone
    rw [honeP, one_mul] at hproduct
    exact hproduct
  · right
    refine ⟨hcentral, ?_⟩
    apply Subtype.ext
    have hcentralP :
        (data.factor x).1.1 ^ 2 =
          extra.centralInvolution.1.1 :=
      congrArg Subtype.val hcentral
    have hzSqP :
        extra.centralInvolution.1.1 ^ 2 = 1 :=
      congrArg (fun w :
        Subgroup.center data.extraspecialPart ↦ w.1.1)
          extra.centralInvolution_sq
    rw [hcentralP] at hproduct
    calc
      (data.factor x).2.1 ^ 2 =
          extra.centralInvolution.1.1 ^ 2 *
            (data.factor x).2.1 ^ 2 := by rw [hzSqP, one_mul]
      _ = extra.centralInvolution.1.1 *
            (extra.centralInvolution.1.1 *
              (data.factor x).2.1 ^ 2) := by
        rw [pow_two]
        group
      _ = extra.centralInvolution.1.1 := by rw [hproduct, mul_one]

private abbrev ActiveType :=
  {x : P // x ∈ activePrimeOrderElements 2 P}

private abbrev MatchingSquarePairs :=
  (SquareFiber data.extraspecialPart 1 ×
      SquareFiber data.headPart 1) ⊕
    (SquareFiber data.extraspecialPart
        extra.centralInvolution.1 ×
      SquareFiber data.headPart
        (data.headCentralInvolution extra).1)

private def encodeTwisted
    (xb : ActiveType P × Bool) :
    MatchingSquarePairs P data e extra := by
  let x := xb.1.1
  let b := xb.2
  if hone : (data.factor x).1 ^ 2 = 1 then
    have honePair :
        (data.factor x).1 ^ 2 = 1 ∧
          (data.factor x).2 ^ 2 = 1 := by
      rcases factor_square_dichotomy P data e extra x xb.1.2 with
          h | h
      · exact h
      · exact False.elim <|
          extra.centralInvolution_ne_one <| by
            apply Subtype.ext
            exact h.1.symm.trans hone
    exact Sum.inl
      (⟨twistedExtra P data e extra x b,
          (twistedExtra_sq P data e extra x b).trans honePair.1⟩,
       ⟨twistedHead P data e extra x b,
          (twistedHead_sq P data e extra x b).trans honePair.2⟩)
  else
    have hcentral :
        (data.factor x).1 ^ 2 =
            extra.centralInvolution.1 ∧
          (data.factor x).2 ^ 2 =
            (data.headCentralInvolution extra).1 := by
      rcases factor_square_dichotomy P data e extra x xb.1.2 with
          h | h
      · exact False.elim (hone h.1)
      · exact h
    exact Sum.inr
      (⟨twistedExtra P data e extra x b,
          (twistedExtra_sq P data e extra x b).trans hcentral.1⟩,
       ⟨twistedHead P data e extra x b,
          (twistedHead_sq P data e extra x b).trans hcentral.2⟩)

private def encodedProduct :
    MatchingSquarePairs P data e extra → P
  | Sum.inl pair => pair.1.1.1 * pair.2.1.1
  | Sum.inr pair => pair.1.1.1 * pair.2.1.1

private def encodedExtra :
    MatchingSquarePairs P data e extra → data.extraspecialPart
  | Sum.inl pair => pair.1.1
  | Sum.inr pair => pair.1.1

private theorem encodedProduct_encodeTwisted
    (xb : ActiveType P × Bool) :
    encodedProduct P data e extra
        (encodeTwisted P data e extra xb) = xb.1.1 := by
  simp only [encodeTwisted]
  split <;>
    exact twisted_mul P data e extra xb.1.1 xb.2

private theorem encodedExtra_encodeTwisted
    (xb : ActiveType P × Bool) :
    encodedExtra P data e extra
        (encodeTwisted P data e extra xb) =
      twistedExtra P data e extra xb.1.1 xb.2 := by
  simp only [encodeTwisted]
  split <;> rfl

private theorem encodeTwisted_injective :
    Function.Injective (encodeTwisted P data e extra) := by
  rintro ⟨x, b⟩ ⟨y, c⟩ hencode
  have hxy :
      x.1 = y.1 := by
    have hproduct :=
      congrArg (encodedProduct P data e extra) hencode
    simpa only [encodedProduct_encodeTwisted] using hproduct
  have hxySubtype : x = y := by
    exact Subtype.ext hxy
  subst y
  apply Prod.ext
  · rfl
  · have htwist :=
      congrArg (encodedExtra P data e extra) hencode
    simp only [encodedExtra_encodeTwisted] at htwist
    cases b <;> cases c <;>
      simp only [Bool.false_eq_true, Bool.true_eq_false] at htwist ⊢
    · apply extra.centralInvolution_ne_one
      apply Subtype.ext
      have htwist' :
          (data.factor x.1).1 =
            (data.factor x.1).1 *
              extra.centralInvolution.1 := by
        simpa [twistedExtra] using htwist
      have hone :
          (1 : data.extraspecialPart) =
            extra.centralInvolution.1 := by
        apply mul_left_cancel (a := (data.factor x.1).1)
        simpa using htwist'
      exact hone.symm
    · apply extra.centralInvolution_ne_one
      apply Subtype.ext
      have htwist' :
          (data.factor x.1).1 *
              extra.centralInvolution.1 =
            (data.factor x.1).1 := by
        simpa [twistedExtra] using htwist
      have hone :
          extra.centralInvolution.1 =
            (1 : data.extraspecialPart) := by
        apply mul_left_cancel (a := (data.factor x.1).1)
        simpa using htwist'
      exact hone

/-- Two chosen decompositions of every active involution inject into the
two matching square-fiber rectangles. -/
theorem two_mul_active_card_le_matchingSquarePairs :
    2 * (activePrimeOrderElements 2 P).card ≤
      Nat.card (SquareFiber data.extraspecialPart 1) *
          Nat.card (SquareFiber data.headPart 1) +
        Nat.card (SquareFiber data.extraspecialPart
            extra.centralInvolution.1) *
          Nat.card (SquareFiber data.headPart
            (data.headCentralInvolution extra).1) := by
  have hinj :=
    Nat.card_le_card_of_injective
      (encodeTwisted P data e extra)
      (encodeTwisted_injective P data e extra)
  have hactive :
      Nat.card (ActiveType P) =
        (activePrimeOrderElements 2 P).card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe _
  have hbool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_bool
  rw [Nat.card_prod, hactive, hbool, Nat.card_sum,
    Nat.card_prod, Nat.card_prod] at hinj
  simpa only [Nat.mul_comm] using hinj

include extra headCount

/-- The finite central-product bookkeeping, with no representation theory
and no hidden normalization of the extraspecial sign. -/
theorem active_card_le_countingEnvelope :
    (activePrimeOrderElements 2 P).card ≤
      data.head.countingEnvelope e := by
  have hpairs :=
    two_mul_active_card_le_matchingSquarePairs
      P data e extra
  have hpairsBound :
      2 * (activePrimeOrderElements 2 P).card ≤
        Nat.card (SquareFiber data.extraspecialPart 1) *
            data.head.squareOneCount +
          Nat.card (SquareFiber data.extraspecialPart
              extra.centralInvolution.1) *
            data.head.squareCentralCount := by
    exact hpairs.trans <|
      Nat.add_le_add
        (Nat.mul_le_mul_left _ headCount.card_one_le)
        (Nat.mul_le_mul_left _ headCount.card_central_le)
  have hbound :
      2 * (activePrimeOrderElements 2 P).card ≤
        2 * data.head.countingEnvelope e := by
    generalize data.head = head at hpairsBound ⊢
    cases head with
    | dihedral k hk equiv =>
        have hkdiv : 4 * k / 2 = 2 * k := by omega
        simp only [BergerMaximalClassHead.squareOneCount,
          BergerMaximalClassHead.squareCentralCount,
          BergerMaximalClassHead.countingEnvelope,
          BergerMaximalClassHead.rotationOrder, hkdiv] at hpairsBound ⊢
        nlinarith [extra.card_fibers, extra.card_one_le]
    | semidihedral k hk presentation =>
        have hkdiv : 8 * k / 2 = 4 * k := by omega
        simp only [BergerMaximalClassHead.squareOneCount,
          BergerMaximalClassHead.squareCentralCount,
          BergerMaximalClassHead.countingEnvelope,
          BergerMaximalClassHead.rotationOrder, hkdiv] at hpairsBound ⊢
        nlinarith [extra.card_fibers]
    | generalizedQuaternion n hn equiv =>
        have hndiv : 2 * n / 2 = n := by omega
        simp only [BergerMaximalClassHead.squareOneCount,
          BergerMaximalClassHead.squareCentralCount,
          BergerMaximalClassHead.countingEnvelope,
          BergerMaximalClassHead.rotationOrder, hndiv] at hpairsBound ⊢
        nlinarith [extra.card_fibers, extra.card_central_le]
  omega

end Count

end BergerMixedCentralProductData

end LisiSabatini
