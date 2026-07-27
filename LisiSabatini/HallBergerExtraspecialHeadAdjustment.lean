import LisiSabatini.ExtraspecialCentralAutomorphism
import LisiSabatini.HallBergerExtraspecialExtension
import LisiSabatini.HallBergerSourcePreliminaries

/-!
# Adjusting the Hall--Berger head past an extraspecial factor

Suppose an ambient element normalizes an extraspecial two-subgroup and
acts trivially on its quotient by the center.  Its induced automorphism
is inner, so multiplication on the right by a suitable element of the
extraspecial subgroup makes it centralize that subgroup.

The right adjustment `h * c⁻¹` is the useful orientation in the
Hall--Berger application: it has the same conjugation action as `h` on
every element which commutes with the extraspecial factor.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

/-- An element of `N_G(E)` acts trivially on `E / Z(E)`.

This is phrased through the canonical normalizer action on `E`, avoiding
any choice of an ambient representative. -/
def NormalizerConjugationTrivialModuloCenter
    (E : Subgroup G) (h : Subgroup.normalizer (E : Set G)) : Prop :=
  ∀ x : E,
    E.normalizerMonoidHom h x * x⁻¹ ∈ Subgroup.center E

/-- Conjugation fixes every element of order at most two in a finite
cyclic normal subgroup. -/
theorem conjugate_eq_self_of_mem_cyclic_normal_of_sq_eq_one
    [Finite G] (N : Subgroup G) [N.Normal]
    (hNcyclic : IsCyclic N)
    (g x : G) (hxN : x ∈ N) (hxSq : x ^ 2 = 1) :
    g * x * g⁻¹ = x := by
  let xN : N := ⟨x, hxN⟩
  let gxN : N :=
    ⟨g * x * g⁻¹,
      (inferInstance : N.Normal).conj_mem x hxN g⟩
  have hxNSq : xN ^ 2 = 1 := by
    apply Subtype.ext
    exact hxSq
  have hgxNSq : gxN ^ 2 = 1 := by
    apply Subtype.ext
    change (g * x * g⁻¹) ^ 2 = 1
    calc
      (g * x * g⁻¹) ^ 2 =
          g * x ^ 2 * g⁻¹ := by
        simp only [pow_two]
        group
      _ = 1 := by rw [hxSq]; simp
  by_cases hxOne : xN = 1
  · have hxVal : x = 1 :=
      congrArg Subtype.val hxOne
    simp [hxVal]
  have hgxOne : gxN ≠ 1 := by
    intro hgx
    apply hxOne
    apply Subtype.ext
    have hgxVal :
        g * x * g⁻¹ = 1 :=
      congrArg Subtype.val hgx
    have hxVal : x = 1 := by
      have := congrArg (fun y : G ↦ g⁻¹ * y * g) hgxVal
      simpa [mul_assoc] using this
    exact hxVal
  exact congrArg Subtype.val
    (eq_of_sq_eq_one_of_ne_one_of_isCyclic
      hNcyclic hgxNSq hxNSq hgxOne hxOne)

namespace IsExtraspecial

variable {G : Type u} [Group G] [Finite G]
  {E : Subgroup G}

/-- **Extraspecial head adjustment.**

If `h ∈ N_G(E)` induces the identity on `E / Z(E)`, then there is
`c ∈ E` such that the right-adjusted element `h * c⁻¹` centralizes
`E`. -/
theorem exists_right_adjustment_mem_centralizer
    (hE : IsExtraspecial 2 E)
    (h : Subgroup.normalizer (E : Set G))
    (htriv :
      NormalizerConjugationTrivialModuloCenter E h) :
    ∃ c : E,
      (h : G) * (c : G)⁻¹ ∈
        Subgroup.centralizer (E : Set G) := by
  let α : MulAut E :=
    E.normalizerMonoidHom h
  obtain ⟨c, hc⟩ :=
    hE.exists_eq_conj_of_apply_mul_inv_mem_center
      α htriv
  let cn : Subgroup.normalizer (E : Set G) :=
    ⟨(c : G), E.le_normalizer c.2⟩
  have hmapc :
      E.normalizerMonoidHom cn = MulAut.conj c := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rfl
  have hk :
      h * cn⁻¹ ∈ E.normalizerMonoidHom.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_mul, map_inv, hmapc]
    change α * (MulAut.conj c)⁻¹ = 1
    rw [hc]
    exact mul_inv_cancel _
  rw [Subgroup.normalizerMonoidHom_ker] at hk
  exact ⟨c, hk⟩

/-- Ambient-element formulation of
`exists_right_adjustment_mem_centralizer`. -/
theorem exists_right_adjustment_mem_centralizer_of_mem_normalizer
    (hE : IsExtraspecial 2 E)
    (h : G) (hN : h ∈ Subgroup.normalizer (E : Set G))
    (htriv :
      NormalizerConjugationTrivialModuloCenter E ⟨h, hN⟩) :
    ∃ c : E,
      h * (c : G)⁻¹ ∈
        Subgroup.centralizer (E : Set G) :=
  hE.exists_right_adjustment_mem_centralizer
    ⟨h, hN⟩ htriv

/-- Right adjustment preserves being outside a subgroup containing the
extraspecial factor. -/
theorem exists_right_adjustment_mem_centralizer_and_not_mem
    (hE : IsExtraspecial 2 E)
    (C : Subgroup G) (hEC : E ≤ C)
    (h : G) (hN : h ∈ Subgroup.normalizer (E : Set G))
    (htriv :
      NormalizerConjugationTrivialModuloCenter E ⟨h, hN⟩)
    (hout : h ∉ C) :
    ∃ c : E,
      h * (c : G)⁻¹ ∈
          Subgroup.centralizer (E : Set G) ∧
        h * (c : G)⁻¹ ∉ C := by
  obtain ⟨c, hcCentral⟩ :=
    hE.exists_right_adjustment_mem_centralizer_of_mem_normalizer
      h hN htriv
  refine ⟨c, hcCentral, ?_⟩
  intro hcC
  apply hout
  have hcMem : (c : G) ∈ C :=
    hEC c.2
  have hprod :
      (h * (c : G)⁻¹) * (c : G) ∈ C :=
    C.mul_mem hcC hcMem
  simpa [mul_assoc] using hprod

omit [Finite G] in
/-- Conjugation by a right adjustment agrees with the original
conjugation on an element commuting with the correcting element. -/
theorem conj_right_adjustment_apply_of_commute
    (h a : G) (c : E)
    (hcomm : Commute (c : G) a) :
    MulAut.conj (h * (c : G)⁻¹) a =
      MulAut.conj h a := by
  simp only [MulAut.conj_apply, mul_inv_rev, inv_inv]
  have hcInv :
      (c : G)⁻¹ * a = a * (c : G)⁻¹ :=
    hcomm.inv_left.eq
  calc
    h * (c : G)⁻¹ * a * ((c : G) * h⁻¹) =
        h * ((c : G)⁻¹ * a) * (c : G) * h⁻¹ := by
      group
    _ = h * (a * (c : G)⁻¹) * (c : G) * h⁻¹ := by
      rw [hcInv]
    _ = h * a * h⁻¹ := by
      group

/-- Hall--Berger-ready adjustment package.

Besides centralizing `E` and remaining outside `C`, the adjusted element
has the same action as `h` on every `a` centralized by `E`. -/
theorem exists_right_adjustment_with_same_conjugation
    (hE : IsExtraspecial 2 E)
    (C : Subgroup G) (hEC : E ≤ C)
    (h : G) (hN : h ∈ Subgroup.normalizer (E : Set G))
    (htriv :
      NormalizerConjugationTrivialModuloCenter E ⟨h, hN⟩)
    (hout : h ∉ C)
    (a : G)
    (hEa : ∀ c : E, Commute (c : G) a) :
    ∃ c : E,
      h * (c : G)⁻¹ ∈
          Subgroup.centralizer (E : Set G) ∧
        h * (c : G)⁻¹ ∉ C ∧
        MulAut.conj (h * (c : G)⁻¹) a =
          MulAut.conj h a := by
  obtain ⟨c, hcCentral, hcOut⟩ :=
    hE.exists_right_adjustment_mem_centralizer_and_not_mem
      C hEC h hN htriv hout
  exact
    ⟨c, hcCentral, hcOut,
      conj_right_adjustment_apply_of_commute h a c (hEa c)⟩

/-- Nested-subgroup version for an extraspecial factor supplied inside
the Hall--Berger centralizer `C`.

The correcting element belongs to the ambient image of the factor, and
the adjustment remains outside `C`. -/
theorem exists_right_adjustment_of_nested_extraspecial_factor
    (C : Subgroup G) (E₀ : Subgroup C)
    (hE₀ : IsExtraspecial 2 E₀)
    (h : G)
    (hN :
      h ∈ Subgroup.normalizer
        ((E₀.map C.subtype : Subgroup G) : Set G))
    (htriv :
      NormalizerConjugationTrivialModuloCenter
        (E₀.map C.subtype)
        ⟨h, hN⟩)
    (hout : h ∉ C) :
    ∃ c : E₀.map C.subtype,
      h * (c : G)⁻¹ ∈
          Subgroup.centralizer
            ((E₀.map C.subtype : Subgroup G) : Set G) ∧
        h * (c : G)⁻¹ ∉ C := by
  let F : Subgroup G :=
    E₀.map C.subtype
  let eF : E₀ ≃* F :=
    Subgroup.equivMapOfInjective
      E₀ C.subtype Subtype.coe_injective
  have hF : IsExtraspecial 2 F :=
    hE₀.of_mulEquiv eF
  have hFC : F ≤ C :=
    Subgroup.map_subtype_le E₀
  simpa only [F] using
    hF.exists_right_adjustment_mem_centralizer_and_not_mem
      C hFC h hN htriv hout

/-- The nested Hall--Berger adjustment also preserves the action on a
rotation centralized by the internal extraspecial factor. -/
theorem exists_right_adjustment_of_nested_extraspecial_factor_with_same_conjugation
    (C : Subgroup G) (E₀ : Subgroup C)
    (hE₀ : IsExtraspecial 2 E₀)
    (h : G)
    (hN :
      h ∈ Subgroup.normalizer
        ((E₀.map C.subtype : Subgroup G) : Set G))
    (htriv :
      NormalizerConjugationTrivialModuloCenter
        (E₀.map C.subtype)
        ⟨h, hN⟩)
    (hout : h ∉ C)
    (a : G)
    (hE₀a : ∀ c : E₀, Commute ((c : C) : G) a) :
    ∃ c : E₀.map C.subtype,
      h * (c : G)⁻¹ ∈
          Subgroup.centralizer
            ((E₀.map C.subtype : Subgroup G) : Set G) ∧
        h * (c : G)⁻¹ ∉ C ∧
        MulAut.conj (h * (c : G)⁻¹) a =
          MulAut.conj h a := by
  let F : Subgroup G :=
    E₀.map C.subtype
  let eF : E₀ ≃* F :=
    Subgroup.equivMapOfInjective
      E₀ C.subtype Subtype.coe_injective
  have hF : IsExtraspecial 2 F :=
    hE₀.of_mulEquiv eF
  have hFC : F ≤ C :=
    Subgroup.map_subtype_le E₀
  have hFa : ∀ c : F, Commute (c : G) a := by
    intro c
    obtain ⟨x, hxE₀, hxc⟩ :=
      Subgroup.mem_map.mp c.2
    have hx := hE₀a ⟨x, hxE₀⟩
    change Commute (c : G) a
    rw [← hxc]
    exact hx
  simpa only [F] using
    hF.exists_right_adjustment_with_same_conjugation
      C hFC h hN htriv hout a hFa

/-- In particular, the adjustment preserves conjugation on every
element of the ambient image of `Z(C)`.  This is the form directly
applicable to the distinguished Hall--Berger rotation. -/
theorem exists_right_adjustment_of_nested_extraspecial_factor_on_centerImage
    (C : Subgroup G) (E₀ : Subgroup C)
    (hE₀ : IsExtraspecial 2 E₀)
    (h : G)
    (hN :
      h ∈ Subgroup.normalizer
        ((E₀.map C.subtype : Subgroup G) : Set G))
    (htriv :
      NormalizerConjugationTrivialModuloCenter
        (E₀.map C.subtype)
        ⟨h, hN⟩)
    (hout : h ∉ C)
    (a : G)
    (ha : a ∈ characteristicCenterImage C) :
    ∃ c : E₀.map C.subtype,
      h * (c : G)⁻¹ ∈
          Subgroup.centralizer
            ((E₀.map C.subtype : Subgroup G) : Set G) ∧
        h * (c : G)⁻¹ ∉ C ∧
        MulAut.conj (h * (c : G)⁻¹) a =
          MulAut.conj h a := by
  have haCentralizer :
      a ∈ Subgroup.centralizer (C : Set G) := by
    rw [characteristicCenterImage_eq_inf_centralizer] at ha
    exact ha.2
  apply
    hE₀.exists_right_adjustment_of_nested_extraspecial_factor_with_same_conjugation
      C E₀ h hN htriv hout a
  intro c
  exact
    Subgroup.mem_centralizer_iff.mp
      haCentralizer (c : C) (c : C).2

/-! ## Automatic normalization in the Hall--Berger setting -/

/-- Under the cyclic-Frattini Hall--Berger hypothesis, every ambient
element normalizes an extraspecial subgroup of the Frattini centralizer
and acts trivially on its quotient by the center.

The commutator error lies in `Φ(G)`.  Its square is one because
conjugation fixes the order-at-most-two square of the extraspecial
element inside cyclic `Φ(G)`.  Thus the error is either one or the
unique involution in `Φ(G)`, which is already the central involution of
the extraspecial subgroup. -/
theorem exists_mem_normalizer_and_trivialModuloCenter_of_le_frattiniCentralizer
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hE : IsExtraspecial 2 E)
    (hEC : E ≤ frattiniCentralizer G)
    (h : G) :
    ∃ hN : h ∈ Subgroup.normalizer (E : Set G),
      NormalizerConjugationTrivialModuloCenter E ⟨h, hN⟩ := by
  have hPhiCyclic :
      IsCyclic (frattini G) :=
    frattini_isCyclic_of_omegaOne_frattiniCentralizer_center_isCyclic
      Nat.prime_two hG2 hBKN
  have hcenterImageLePhi :
      characteristicCenterImage E ≤ frattini G := by
    intro z hz
    unfold characteristicCenterImage at hz
    rw [← hE.commutator_eq_center,
      Subgroup.map_subtype_commutator] at hz
    exact
      (commutator_le_frattini_of_isPGroup
        Nat.prime_two hG2)
        (Subgroup.commutator_mono le_top le_top hz)
  have herror (x : E) :
      ⁅h, (x : G)⁆ ∈ frattini G ∧
        ⁅h, (x : G)⁆ ∈ E := by
    let d : G := ⁅h, (x : G)⁆
    have hdPhi : d ∈ frattini G := by
      apply
        (commutator_le_frattini_of_isPGroup
          Nat.prime_two hG2)
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top h)
        (Subgroup.mem_top (x : G))
    have hxSqCenter :
        x ^ 2 ∈ Subgroup.center E :=
      hE.square_mem_center x
    have hxFourth : ((x : G) ^ 2) ^ 2 = 1 := by
      let xSqCenter : Subgroup.center E :=
        ⟨x ^ 2, hxSqCenter⟩
      exact congrArg
        (fun z : Subgroup.center E ↦ ((z : E) : G))
        (hE.center_sq_eq_one xSqCenter)
    have hxSqPhi : (x : G) ^ 2 ∈ frattini G := by
      apply hcenterImageLePhi
      exact Subgroup.mem_map.mpr
        ⟨x ^ 2, hxSqCenter, rfl⟩
    have hfixSq :
        h * (x : G) ^ 2 * h⁻¹ = (x : G) ^ 2 :=
      conjugate_eq_self_of_mem_cyclic_normal_of_sq_eq_one
        (frattini G) hPhiCyclic h ((x : G) ^ 2)
          hxSqPhi hxFourth
    have hdCommuteX :
        Commute d (x : G) := by
      have hxC :
          (x : G) ∈ frattiniCentralizer G :=
        hEC x.2
      change
        (x : G) ∈
          Subgroup.centralizer
            (frattini G : Set G) at hxC
      exact hxC d hdPhi
    have hconjEq :
        h * (x : G) * h⁻¹ = d * (x : G) := by
      simp only [d, commutatorElement_def]
      group
    have hconjSq :
        (h * (x : G) * h⁻¹) ^ 2 =
          (x : G) ^ 2 := by
      calc
        (h * (x : G) * h⁻¹) ^ 2 =
            h * (x : G) ^ 2 * h⁻¹ := by
          simp only [pow_two]
          group
        _ = (x : G) ^ 2 := hfixSq
    have hdSq : d ^ 2 = 1 := by
      rw [hconjEq, hdCommuteX.mul_pow] at hconjSq
      apply mul_right_cancel
        (b := (x : G) ^ 2)
      simpa using hconjSq
    refine ⟨hdPhi, ?_⟩
    by_cases hdOne : d = 1
    · change d ∈ E
      rw [hdOne]
      exact E.one_mem
    obtain ⟨z, hzNe, _hzUnique⟩ :=
      (Nat.card_eq_two_iff'
        (1 : Subgroup.center E)).mp
        hE.card_center
    have hzPhi : ((z : E) : G) ∈ frattini G := by
      apply hcenterImageLePhi
      exact Subgroup.mem_map.mpr
        ⟨(z : E), z.2, rfl⟩
    have hzSq : ((z : E) : G) ^ 2 = 1 := by
      exact congrArg
        (fun w : Subgroup.center E ↦ ((w : E) : G))
        (hE.center_sq_eq_one z)
    let dPhi : frattini G :=
      ⟨d, hdPhi⟩
    let zPhi : frattini G :=
      ⟨((z : E) : G), hzPhi⟩
    have hdPhiSq : dPhi ^ 2 = 1 := by
      apply Subtype.ext
      exact hdSq
    have hzPhiSq : zPhi ^ 2 = 1 := by
      apply Subtype.ext
      exact hzSq
    have hdPhiNe : dPhi ≠ 1 := by
      intro hd
      exact hdOne (congrArg Subtype.val hd)
    have hzPhiNe : zPhi ≠ 1 := by
      intro hz
      apply hzNe
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun w : frattini G ↦ (w : G)) hz
    have hdz :
        d = ((z : E) : G) :=
      congrArg Subtype.val
        (eq_of_sq_eq_one_of_ne_one_of_isCyclic
          hPhiCyclic hdPhiSq hzPhiSq
            hdPhiNe hzPhiNe)
    change d ∈ E
    rw [hdz]
    exact (z : E).2
  have hN :
      h ∈ Subgroup.normalizer (E : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hxE
    let xE : E := ⟨x, hxE⟩
    have hdE := (herror xE).2
    have hconj :
        h * x * h⁻¹ =
          ⁅h, x⁆ * x := by
      simp only [commutatorElement_def]
      group
    rw [hconj]
    exact E.mul_mem hdE hxE
  refine ⟨hN, ?_⟩
  intro x
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hdPhi := (herror x).1
  have hyC :
      (y : G) ∈ frattiniCentralizer G :=
    hEC y.2
  change
    (y : G) *
        (h * (x : G) * h⁻¹ * (x : G)⁻¹) =
      (h * (x : G) * h⁻¹ * (x : G)⁻¹) *
        (y : G)
  change
    (y : G) * ⁅h, (x : G)⁆ =
      ⁅h, (x : G)⁆ * (y : G)
  change
    (y : G) ∈
      Subgroup.centralizer
        (frattini G : Set G) at hyC
  exact (hyC ⁅h, (x : G)⁆ hdPhi).symm

/-- Automatic bridge for a nested Hall--Berger extraspecial factor. -/
theorem exists_mem_normalizer_and_trivialModuloCenter_of_nested_extraspecial
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (E₀ : Subgroup (frattiniCentralizer G))
    (hE₀ : IsExtraspecial 2 E₀)
    (h : G) :
    ∃ hN :
        h ∈ Subgroup.normalizer
          ((E₀.map (frattiniCentralizer G).subtype :
            Subgroup G) : Set G),
      NormalizerConjugationTrivialModuloCenter
        (E₀.map (frattiniCentralizer G).subtype)
        ⟨h, hN⟩ := by
  let F : Subgroup G :=
    E₀.map (frattiniCentralizer G).subtype
  let eF : E₀ ≃* F :=
    Subgroup.equivMapOfInjective E₀
      (frattiniCentralizer G).subtype
      Subtype.coe_injective
  have hF : IsExtraspecial 2 F :=
    hE₀.of_mulEquiv eF
  have hFC : F ≤ frattiniCentralizer G :=
    Subgroup.map_subtype_le E₀
  simpa only [F] using
    hF.exists_mem_normalizer_and_trivialModuloCenter_of_le_frattiniCentralizer
      hG2 hBKN hFC h

/-- Fully automatic source-paper adjustment for a nested extraspecial
factor of `C_G(Φ(G))`.

For an outside element `h` and a central rotation `a`, the corrected
element `h * c⁻¹` centralizes the ambient image of the extraspecial
factor, remains outside the Frattini centralizer, and induces the same
conjugation on `a`. -/
theorem exists_hallBerger_right_adjustment_of_nested_extraspecial
    (hG2 : IsPGroup 2 G)
    (hBKN :
      HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (E₀ : Subgroup (frattiniCentralizer G))
    (hE₀ : IsExtraspecial 2 E₀)
    (h : G) (hout : h ∉ frattiniCentralizer G)
    (a : G)
    (ha :
      a ∈ characteristicCenterImage
        (frattiniCentralizer G)) :
    ∃ c :
        E₀.map (frattiniCentralizer G).subtype,
      h * (c : G)⁻¹ ∈
          Subgroup.centralizer
            ((E₀.map
              (frattiniCentralizer G).subtype :
                Subgroup G) : Set G) ∧
        h * (c : G)⁻¹ ∉ frattiniCentralizer G ∧
        MulAut.conj (h * (c : G)⁻¹) a =
          MulAut.conj h a := by
  obtain ⟨hN, htriv⟩ :=
    hE₀.exists_mem_normalizer_and_trivialModuloCenter_of_nested_extraspecial
      hG2 hBKN E₀ h
  exact
    hE₀.exists_right_adjustment_of_nested_extraspecial_factor_on_centerImage
      (frattiniCentralizer G) E₀ h hN htriv
        hout a ha

end IsExtraspecial

end LisiSabatini
