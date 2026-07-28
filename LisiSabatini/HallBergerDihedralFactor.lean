module

public import LisiSabatini.HallBergerInvolutionExtraction

/-!
# The dihedral factor extracted in the BKN proof

Two noncommuting involutions in a finite group whose derived subgroup is
central of order two generate a copy of the dihedral group of order
eight.  This file proves that statement directly, beginning with the
order-four rotation normal form.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

universe u

theorem mem_zpowers_generator_in_zpowers
    {D : Type u} [Group D] (a : D) :
    ∀ q : Subgroup.zpowers a,
      q ∈ Subgroup.zpowers
        (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) := by
  intro q
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp q.2
  exact Subgroup.mem_zpowers_iff.mpr
    ⟨k, Subtype.ext hk⟩

/-- The canonical order-four rotation subgroup, coordinatized by
`ZMod 4`. -/
noncomputable def rotationEquivFour
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4) :
    Multiplicative (ZMod 4) ≃*
      Subgroup.zpowers a :=
  zmodMulEquivOfGenerator
    (G := Subgroup.zpowers a)
    (g := ⟨a, Subgroup.mem_zpowers a⟩)
    (mem_zpowers_generator_in_zpowers a)
    (by rw [Nat.card_zpowers, haOrder])

@[simp]
private theorem coe_rotationEquivFour_one
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4) :
    ((rotationEquivFour a haOrder
        (Multiplicative.ofAdd (1 : ZMod 4)) :
      Subgroup.zpowers a) : D) =
      a := by
  simp [rotationEquivFour]

/-- The ambient value of the rotation coordinate. -/
noncomputable def rotationValue
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4)
    (i : ZMod 4) : D :=
  rotationEquivFour a haOrder (Multiplicative.ofAdd i)

@[simp]
theorem rotationValue_zero
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4) :
    rotationValue a haOrder 0 = 1 := by
  change
    ((rotationEquivFour a haOrder
      (1 : Multiplicative (ZMod 4)) :
        Subgroup.zpowers a) : D) = 1
  rw [map_one]
  rfl

@[simp]
theorem rotationValue_one
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4) :
    rotationValue a haOrder 1 = a :=
  coe_rotationEquivFour_one a haOrder

private theorem rotationValue_add
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4)
    (i j : ZMod 4) :
    rotationValue a haOrder (i + j) =
      rotationValue a haOrder i *
        rotationValue a haOrder j := by
  exact congrArg Subtype.val
    (map_mul (rotationEquivFour a haOrder)
      (Multiplicative.ofAdd i)
      (Multiplicative.ofAdd j))

theorem rotationValue_injective
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4) :
    Function.Injective (rotationValue a haOrder) := by
  intro i j hij
  have hsub :
      rotationEquivFour a haOrder
          (Multiplicative.ofAdd i) =
        rotationEquivFour a haOrder
          (Multiplicative.ofAdd j) :=
    Subtype.ext hij
  exact congrArg Multiplicative.toAdd
    ((rotationEquivFour a haOrder).injective hsub)

theorem rotationValue_mem_zpowers
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4)
    (i : ZMod 4) :
    rotationValue a haOrder i ∈ Subgroup.zpowers a :=
  (rotationEquivFour a haOrder
    (Multiplicative.ofAdd i)).2

private theorem rotationValue_intCast
    {D : Type u} [Group D] (a : D)
    (haOrder : orderOf a = 4)
    (k : ℤ) :
    rotationValue a haOrder (k : ZMod 4) =
      a ^ k := by
  simp [rotationValue, rotationEquivFour]

/-- An involution inverting the distinguished generator also inverts
every modular rotation coordinate. -/
private theorem involution_flips_rotationValue
    {D : Type u} [Group D]
    {a x : D}
    (haOrder : orderOf a = 4)
    (hxSq : x ^ 2 = 1)
    (hconj : x * a * x⁻¹ = a⁻¹)
    (i : ZMod 4) :
    rotationValue a haOrder i * x =
      x * rotationValue a haOrder (-i) := by
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective i
  simp only [← Int.cast_neg, rotationValue_intCast]
  have hxInv : x⁻¹ = x := by
    have hxx : x * x = 1 := by simpa only [pow_two] using hxSq
    exact (mul_eq_one_iff_eq_inv.mp hxx).symm
  have hconjK :
      x * a ^ k * x⁻¹ = (a⁻¹) ^ k := by
    calc
      x * a ^ k * x⁻¹ = (x * a * x⁻¹) ^ k :=
        (conj_zpow).symm
      _ = (a⁻¹) ^ k := by rw [hconj]
  apply (mul_left_cancel_iff (a := x)).mp
  calc
    x * (a ^ k * x) = x * a ^ k * x⁻¹ := by
      rw [hxInv, mul_assoc]
    _ = (a⁻¹) ^ k := hconjK
    _ = a ^ (-k) := inv_zpow' a k
    _ = x * (x * a ^ (-k)) := by
      rw [← mul_assoc, ← pow_two, hxSq, one_mul]

/-- The dihedral presentation determined by an order-four rotation and
an involution that inverts it. -/
noncomputable def dihedralFourHom
    {D : Type u} [Group D]
    {a x : D}
    (haOrder : orderOf a = 4)
    (hxSq : x ^ 2 = 1)
    (hconj : x * a * x⁻¹ = a⁻¹) :
    DihedralGroup 4 →* D where
  toFun
    | .r i => rotationValue a haOrder i
    | .sr i => x * rotationValue a haOrder i
  map_one' := rotationValue_zero a haOrder
  map_mul' := by
    rintro (i | i) (j | j)
    · exact rotationValue_add a haOrder i j
    · change
        x * rotationValue a haOrder (j - i) =
          rotationValue a haOrder i *
            (x * rotationValue a haOrder j)
      calc
        x * rotationValue a haOrder (j - i) =
            x * (rotationValue a haOrder (-i) *
              rotationValue a haOrder j) := by
          rw [show j - i = -i + j by abel,
            rotationValue_add]
        _ = (rotationValue a haOrder i * x) *
              rotationValue a haOrder j := by
          rw [involution_flips_rotationValue
            haOrder hxSq hconj i]
          exact (mul_assoc _ _ _).symm
        _ = rotationValue a haOrder i *
              (x * rotationValue a haOrder j) :=
          mul_assoc _ _ _
    · change
        x * rotationValue a haOrder (i + j) =
          (x * rotationValue a haOrder i) *
            rotationValue a haOrder j
      rw [rotationValue_add, mul_assoc]
    · change
        rotationValue a haOrder (j - i) =
          (x * rotationValue a haOrder i) *
            (x * rotationValue a haOrder j)
      symm
      calc
        (x * rotationValue a haOrder i) *
              (x * rotationValue a haOrder j) =
            x * ((rotationValue a haOrder i * x) *
              rotationValue a haOrder j) := by
          group
        _ = x * ((x * rotationValue a haOrder (-i)) *
              rotationValue a haOrder j) := by
          rw [involution_flips_rotationValue
            haOrder hxSq hconj i]
        _ = (x * x) *
              (rotationValue a haOrder (-i) *
                rotationValue a haOrder j) := by
          group
        _ = rotationValue a haOrder (-i) *
              rotationValue a haOrder j := by
          rw [← pow_two, hxSq, one_mul]
        _ = rotationValue a haOrder (-i + j) :=
          (rotationValue_add a haOrder (-i) j).symm
        _ = rotationValue a haOrder (j - i) := by
          congr 1
          abel

/-- The product of two noncommuting involutions has order four in the
central-derived-order-two setting. -/
theorem orderOf_mul_eq_four_of_involutions
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    {x y : D}
    (hxSq : x ^ 2 = 1) (hySq : y ^ 2 = 1)
    (hxy : ⁅x, y⁆ ≠ 1) :
    orderOf (x * y) = 4 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxInv : x⁻¹ = x := by
    have hxx : x * x = 1 := by simpa only [pow_two] using hxSq
    exact (mul_eq_one_iff_eq_inv.mp hxx).symm
  have hyInv : y⁻¹ = y := by
    have hyy : y * y = 1 := by simpa only [pow_two] using hySq
    exact (mul_eq_one_iff_eq_inv.mp hyy).symm
  have hsq : (x * y) ^ 2 = ⁅x, y⁆ := by
    simp only [pow_two, commutatorElement_def, hxInv, hyInv, mul_assoc]
  have hsqNe : (x * y) ^ 2 ≠ 1 := by
    rw [hsq]
    exact hxy
  have hfour : (x * y) ^ 4 = 1 := by
    calc
      (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by
        rw [← pow_mul]
      _ = ⁅x, y⁆ ^ 2 := by rw [hsq]
      _ = 1 := commutatorElement_sq_eq_one hD x y
  have horder :=
    orderOf_eq_prime_pow (x := x * y) (p := 2) (n := 1)
      hsqNe hfour
  norm_num at horder ⊢
  exact horder

/-- A noncommutative group of order eight has center of order two. -/
theorem card_center_eq_two_of_card_eight_of_noncommutative
    {K : Type u} [Group K] [Finite K]
    (hcardK : Nat.card K = 8)
    (hnoncomm : ¬ IsMulCommutative K) :
    Nat.card (Subgroup.center K) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK2 : IsPGroup 2 K := by
    rw [IsPGroup.iff_card]
    exact ⟨3, by norm_num [hcardK]⟩
  letI : Nontrivial K := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    apply hnoncomm
    exact ⟨⟨fun x y ↦ hsub.elim (x * y) (y * x)⟩⟩
  have hcenterGt :
      1 < Nat.card (Subgroup.center K) := by
    letI : Nontrivial (Subgroup.center K) :=
      hK2.center_nontrivial
    exact Finite.one_lt_card
  have hdiv :
      Nat.card (Subgroup.center K) ∣ 2 ^ 3 := by
    have h :=
      Subgroup.card_dvd_of_le
        (show Subgroup.center K ≤ (⊤ : Subgroup K) from le_top)
    rw [Subgroup.card_top, hcardK] at h
    norm_num at h ⊢
    exact h
  obtain ⟨n, hnLe, hcenterCard⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
  interval_cases n
  · have hcenterOne :
        Nat.card (Subgroup.center K) = 1 :=
      hcenterCard.trans (by norm_num)
    omega
  · exact hcenterCard.trans (by norm_num)
  · have hcenterFour :
        Nat.card (Subgroup.center K) = 4 :=
      hcenterCard.trans (by norm_num)
    exfalso
    apply hnoncomm
    let Z : Subgroup K := Subgroup.center K
    have hcardZ : Nat.card Z = 4 := by
      simpa only [Z] using hcenterFour
    have hindex : Z.index = 2 := by
      have hmul := Z.card_mul_index
      rw [hcardZ, hcardK] at hmul
      omega
    have hquotCard : Nat.card (K ⧸ Z) = 2 := by
      rw [← Z.index_eq_card]
      exact hindex
    letI : IsCyclic (K ⧸ Z) :=
      isCyclic_of_prime_card hquotCard
    refine ⟨⟨fun a b ↦
      commutative_of_cyclic_center_quotient
        (QuotientGroup.mk' Z) ?_ a b⟩⟩
    rw [QuotientGroup.ker_mk']
  · have hcenterEight :
        Nat.card (Subgroup.center K) = 8 :=
      hcenterCard.trans (by norm_num)
    exfalso
    apply hnoncomm
    have hcenterTop :
        Subgroup.center K = ⊤ :=
      (Subgroup.center K).eq_top_of_card_eq
        (hcenterEight.trans hcardK.symm)
    refine ⟨⟨fun a b ↦ ?_⟩⟩
    have hb : b ∈ Subgroup.center K := by
      rw [hcenterTop]
      exact Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hb a

/-- Two noncommuting involutions generate the dihedral group of order
eight.  The equivalence is constructed from the eight normal forms
`r^i` and `x r^i`, rather than from a classification of groups of order
eight. -/
noncomputable def twoGeneratorSubgroup_mulEquiv_dihedralFour
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    {x y : D}
    (hxSq : x ^ 2 = 1) (hySq : y ^ 2 = 1)
    (hxy : ⁅x, y⁆ ≠ 1) :
    twoGeneratorSubgroup x y ≃* DihedralGroup 4 := by
  let a : D := x * y
  let H : Subgroup D := twoGeneratorSubgroup x y
  have haOrder : orderOf a = 4 :=
    orderOf_mul_eq_four_of_involutions hD hxSq hySq hxy
  have hxInv : x⁻¹ = x := by
    have hxx : x * x = 1 := by simpa only [pow_two] using hxSq
    exact (mul_eq_one_iff_eq_inv.mp hxx).symm
  have hyInv : y⁻¹ = y := by
    have hyy : y * y = 1 := by simpa only [pow_two] using hySq
    exact (mul_eq_one_iff_eq_inv.mp hyy).symm
  have hconj : x * a * x⁻¹ = a⁻¹ := by
    calc
      x * a * x⁻¹ = (x * x) * y * x := by
        dsimp only [a]
        rw [hxInv]
        group
      _ = y * x := by
        rw [← pow_two, hxSq, one_mul]
      _ = a⁻¹ := by
        dsimp only [a]
        rw [mul_inv_rev, hxInv, hyInv]
  let fD : DihedralGroup 4 →* D :=
    dihedralFourHom haOrder hxSq hconj
  have hxNotRotation : x ∉ Subgroup.zpowers a := by
    intro hxRotation
    have hxa : x * a = a * x := by
      exact congrArg Subtype.val
        (mul_comm
          (⟨x, hxRotation⟩ : Subgroup.zpowers a)
          (⟨a, Subgroup.mem_zpowers a⟩ :
            Subgroup.zpowers a))
    have hyEq : y = x * a := by
      calc
        y = (x * x) * y := by
          rw [← pow_two, hxSq, one_mul]
        _ = x * a := by
          dsimp only [a]
          group
    have hxyComm : x * y = y * x := by
      rw [hyEq]
      calc
        x * (x * a) = a := by
          rw [← mul_assoc, ← pow_two, hxSq, one_mul]
        _ = (x * a) * x := by
          rw [hxa, mul_assoc, ← pow_two, hxSq, mul_one]
    exact hxy
      (commutatorElement_eq_one_iff_mul_comm.mpr hxyComm)
  have hcross (i j : ZMod 4) :
      rotationValue a haOrder i ≠
        x * rotationValue a haOrder j := by
    intro hij
    apply hxNotRotation
    have heq :
        x =
          rotationValue a haOrder i *
            (rotationValue a haOrder j)⁻¹ := by
      calc
        x = x *
            (rotationValue a haOrder j *
              (rotationValue a haOrder j)⁻¹) := by simp
        _ = (x * rotationValue a haOrder j) *
              (rotationValue a haOrder j)⁻¹ := by
          rw [mul_assoc]
        _ = rotationValue a haOrder i *
              (rotationValue a haOrder j)⁻¹ := by
          rw [← hij]
    rw [heq]
    exact (Subgroup.zpowers a).mul_mem
      (rotationValue_mem_zpowers a haOrder i)
      ((Subgroup.zpowers a).inv_mem
        (rotationValue_mem_zpowers a haOrder j))
  have hfDInjective : Function.Injective fD := by
    intro u v huv
    cases u with
    | r i =>
        cases v with
        | r j =>
            change
              rotationValue a haOrder i =
                rotationValue a haOrder j at huv
            exact congrArg DihedralGroup.r
              (rotationValue_injective a haOrder huv)
        | sr j =>
            change
              rotationValue a haOrder i =
                x * rotationValue a haOrder j at huv
            exact False.elim (hcross i j huv)
    | sr i =>
        cases v with
        | r j =>
            change
              x * rotationValue a haOrder i =
                rotationValue a haOrder j at huv
            exact False.elim (hcross j i huv.symm)
        | sr j =>
            change
              x * rotationValue a haOrder i =
                x * rotationValue a haOrder j at huv
            exact congrArg DihedralGroup.sr
              (rotationValue_injective a haOrder
                ((mul_left_cancel_iff).mp huv))
  have hxH : x ∈ H := by
    exact
      (show Subgroup.zpowers x ≤ H from le_sup_left)
        (Subgroup.mem_zpowers x)
  have hyH : y ∈ H := by
    exact
      (show Subgroup.zpowers y ≤ H from le_sup_right)
        (Subgroup.mem_zpowers y)
  have haH : a ∈ H := H.mul_mem hxH hyH
  have hfDmem : ∀ w : DihedralGroup 4, fD w ∈ H := by
    intro w
    cases w with
    | r i =>
        exact (Subgroup.zpowers_le_of_mem haH)
          (rotationValue_mem_zpowers a haOrder i)
    | sr i =>
        exact H.mul_mem hxH
          ((Subgroup.zpowers_le_of_mem haH)
            (rotationValue_mem_zpowers a haOrder i))
  let fH : DihedralGroup 4 →* H :=
    fD.codRestrict H hfDmem
  have hxRange : x ∈ fD.range := by
    refine ⟨DihedralGroup.sr 0, ?_⟩
    change x * rotationValue a haOrder 0 = x
    rw [rotationValue_zero, mul_one]
  have hyRange : y ∈ fD.range := by
    refine ⟨DihedralGroup.sr 1, ?_⟩
    change x * rotationValue a haOrder 1 = y
    rw [rotationValue_one]
    calc
      x * a = (x * x) * y := by
        dsimp only [a]
        group
      _ = y := by
        rw [← pow_two, hxSq, one_mul]
  have hHleRange : H ≤ fD.range :=
    sup_le
      (Subgroup.zpowers_le_of_mem hxRange)
      (Subgroup.zpowers_le_of_mem hyRange)
  have hfHSurjective : Function.Surjective fH := by
    intro h
    obtain ⟨w, hw⟩ := hHleRange h.2
    exact ⟨w, Subtype.ext hw⟩
  have hfHInjective : Function.Injective fH := by
    intro u v huv
    apply hfDInjective
    exact congrArg Subtype.val huv
  exact
    (MulEquiv.ofBijective fH
      ⟨hfHInjective, hfHSurjective⟩).symm

/-- Proposition-valued form of
`twoGeneratorSubgroup_mulEquiv_dihedralFour`. -/
theorem twoGeneratorSubgroup_isomorphic_dihedralFour
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    {x y : D}
    (hxSq : x ^ 2 = 1) (hySq : y ^ 2 = 1)
    (hxy : ⁅x, y⁆ ≠ 1) :
    Nonempty
      (twoGeneratorSubgroup x y ≃* DihedralGroup 4) :=
  ⟨twoGeneratorSubgroup_mulEquiv_dihedralFour
    hD hxSq hySq hxy⟩

/-- The extracted dihedral factor is extraspecial in the intrinsic
project definition. -/
theorem twoGeneratorSubgroup_isExtraspecial
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    {x y : D}
    (hxSq : x ^ 2 = 1) (hySq : y ^ 2 = 1)
    (hxy : ⁅x, y⁆ ≠ 1) :
    IsExtraspecial 2 (twoGeneratorSubgroup x y) := by
  let H : Subgroup D := twoGeneratorSubgroup x y
  let e : H ≃* DihedralGroup 4 :=
    twoGeneratorSubgroup_mulEquiv_dihedralFour
      hD hxSq hySq hxy
  have hcardH : Nat.card H = 8 := by
    calc
      Nat.card H = Nat.card (DihedralGroup 4) :=
        Nat.card_congr e.toEquiv
      _ = 8 := by
        rw [DihedralGroup.nat_card]
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH2 : IsPGroup 2 H := by
    rw [IsPGroup.iff_card]
    exact ⟨3, by norm_num [hcardH]⟩
  have hxH : x ∈ H := by
    exact
      (show Subgroup.zpowers x ≤ H from le_sup_left)
        (Subgroup.mem_zpowers x)
  have hyH : y ∈ H := by
    exact
      (show Subgroup.zpowers y ≤ H from le_sup_right)
        (Subgroup.mem_zpowers y)
  let xH : H := ⟨x, hxH⟩
  let yH : H := ⟨y, hyH⟩
  have hnoncomm : ¬ IsMulCommutative H := by
    intro hcomm
    apply hxy
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact congrArg Subtype.val
      (hcomm.1.1 xH yH)
  have hclass :
      commutator H ≤ Subgroup.center H := by
    intro c hc
    have hcAmbient :
        (c : D) ∈ commutator D := by
      apply
        (Subgroup.commutator_mono
          (show H ≤ (⊤ : Subgroup D) from le_top)
          (show H ≤ (⊤ : Subgroup D) from le_top))
      rw [← Subgroup.map_subtype_commutator]
      exact Subgroup.mem_map.mpr
        ⟨c, hc, rfl⟩
    have hcCenter :
        (c : D) ∈ Subgroup.center D :=
      hD.commutator_le_center hcAmbient
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp hcCenter z
  have hcenterCard :
      Nat.card (Subgroup.center H) = 2 :=
    card_center_eq_two_of_card_eight_of_noncommutative
      hcardH hnoncomm
  have hcommNe : commutator H ≠ ⊥ := by
    intro hbot
    have hmem :
        ⁅xH, yH⁆ ∈ commutator H :=
      Subgroup.commutator_mem_commutator
        (Subgroup.mem_top xH) (Subgroup.mem_top yH)
    have hone : ⁅xH, yH⁆ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hbot]
      exact hmem
    exact hxy (congrArg Subtype.val hone)
  have hcommCard :
      Nat.card (commutator H) = 2 := by
    have hgt : 1 < Nat.card (commutator H) :=
      (commutator H).one_lt_card_iff_ne_bot.mpr hcommNe
    have hle :
        Nat.card (commutator H) ≤
          Nat.card (Subgroup.center H) :=
      Subgroup.card_le_of_le hclass
    rw [hcenterCard] at hle
    omega
  exact
    { prime := Nat.prime_two
      pGroup := hH2
      commutator_eq_center := by
        apply Subgroup.eq_of_le_of_card_ge hclass
        rw [hcenterCard, hcommCard]
      card_center := hcenterCard }

/-- The complete single-step extraction used in the BKN maximal
central-product argument.

From a noncentral involution, the exact omega-one hypothesis supplies a
noncommuting involution partner; the resulting subgroup is a dihedral
group of order eight, is an internal central factor, and its residual
centralizer has the same center as the ambient group. -/
theorem exists_dihedralInternalCentralFactor_of_noncentralInvolution
    {D : Type u} [Group D] [Finite D]
    (hD : HasCentralCommutatorOfOrderTwo D)
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup 2 D)))
    {x : D} (hxSq : x ^ 2 = 1)
    (hxNotCenter : x ∉ Subgroup.center D) :
    ∃ y : D,
      y ^ 2 = 1 ∧
      ⁅x, y⁆ ≠ 1 ∧
      Nonempty
        (twoGeneratorSubgroup x y ≃* DihedralGroup 4) ∧
      IsExtraspecial 2 (twoGeneratorSubgroup x y) ∧
      IsInternalCentralFactor (twoGeneratorSubgroup x y) ∧
      characteristicCenterImage
          (Subgroup.centralizer
            (twoGeneratorSubgroup x y : Set D)) =
        Subgroup.center D := by
  obtain ⟨y, hySq, hxy⟩ :=
    exists_noncommuting_involution_of_not_mem_center
      hOmegaCenter hxSq hxNotCenter
  let hFactor :
      IsInternalCentralFactor
        (twoGeneratorSubgroup x y) :=
    twoGeneratorSubgroup_isInternalCentralFactor
      hD x y hxy
  exact
    ⟨y, hySq, hxy,
      twoGeneratorSubgroup_isomorphic_dihedralFour
        hD hxSq hySq hxy,
      twoGeneratorSubgroup_isExtraspecial
        hD hxSq hySq hxy,
      hFactor,
      centralizer_centerImage_eq_center_of_isInternalCentralFactor
        hFactor⟩

end LisiSabatini
