module

public import LisiSabatini.TwoCoreSymplecticTypeRepresentationComparison
public import LisiSabatini.HallBergerDihedralFactor
public import LisiSabatini.F3Plane

/-!
# The sharp central-commutator edge in `GL₂(F₃)`

The ordinary central-coset estimate leaves one exceptional module:
`F₃²`.  This file proves the required sharp bound of four active
involutions without classifying subgroups of `GL₂(F₃)`.

The proof first shows that Hall's cyclic center has order two.  Otherwise
a central element with nontrivial square makes every nonzero vector a
cyclic vector, embedding the whole group into the eight nonzero vectors
of `F₃²`; the resulting quotient by the center is cyclic, contradicting
the nontrivial derived subgroup.  The existing representation comparison
then gives group order at most eight.  Finally, Hall's omega-one argument
extends an active involution to a generating dihedral pair, and the
already formalized `D₈` count gives the result.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- If a central operator on `F₃²` has nontrivial square, every nonzero
vector is cyclic for that operator. -/
private theorem linearIndependent_vector_centralImage
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 3) F3Plane))
    (C : CenterFixedPointFreeAction 3 2 P)
    (z : Subgroup.center P)
    (hzSqNe : z ^ 2 ≠ 1)
    (v : F3Plane) (hv : v ≠ 0) :
    LinearIndependent (ZMod 3)
      ![v, z.1.1.1 v] := by
  rw [linearIndependent_fin2]
  constructor
  · simpa using z.1.1.toLinearEquiv.injective.ne hv
  · intro a ha
    have hzNe : z ≠ 1 := by
      intro hz
      apply hzSqNe
      rw [hz]
      simp
    fin_cases a
    · apply hv
      simpa using ha.symm
    · exact hv (C.fixedPointFree z hzNe v (by simpa using ha))
    · have hzv : z.1.1.1 v = -v := by
        change (2 : ZMod 3) • z.1.1.1 v = v at ha
        have htwo : (2 : ZMod 3) = -1 := by decide
        rw [htwo, neg_smul, one_smul] at ha
        have hneg : -z.1.1.1 v = v := by
          exact ha
        calc
          z.1.1.1 v = -(-z.1.1.1 v) := by simp
          _ = -v := congrArg Neg.neg hneg
      have hzSqFix :
          (z ^ 2).1.1.1 v = v := by
        change z.1.1.1 (z.1.1.1 v) = v
        rw [hzv, map_neg, hzv, neg_neg]
      exact hv
        (C.fixedPointFree (z ^ 2) hzSqNe v hzSqFix)

/-- A subgroup of `GL₂(F₃)` centralizing an element with nontrivial
square acts freely on the eight nonzero vectors. -/
private theorem natCard_le_eight_of_center_sq_ne_one
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 3) F3Plane))
    (C : CenterFixedPointFreeAction 3 2 P)
    (z : Subgroup.center P)
    (hzSqNe : z ^ 2 ≠ 1) :
    Nat.card P ≤ 8 := by
  classical
  let v : F3Plane := fun _ ↦ 1
  have hv : v ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin 2)
    norm_num [v] at h0
  let b : Fin 2 → F3Plane :=
    ![v, z.1.1.1 v]
  have hb :
      LinearIndependent (ZMod 3) b := by
    simpa only [b] using
      linearIndependent_vector_centralImage P C z hzSqNe v hv
  have hbSpan :
      Submodule.span (ZMod 3) (Set.range b) = ⊤ :=
    hb.span_eq_top_of_card_eq_finrank (by
      simp [F3Plane])
  let eval :
      P → {w : F3Plane // w ≠ 0} := fun g ↦
    ⟨g.1.1.1 v, by
      simpa using g.1.toLinearEquiv.injective.ne hv⟩
  have heval : Function.Injective eval := by
    intro g h hgh
    have hgv : g.1.1.1 v = h.1.1.1 v :=
      congrArg Subtype.val hgh
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext_on hbSpan
    rintro w ⟨i, rfl⟩
    fin_cases i
    · exact hgv
    · have hgz :
          g.1.1.1 (z.1.1.1 v) =
            z.1.1.1 (g.1.1.1 v) := by
        have hc :
            g * z.1 = z.1 * g :=
          Subgroup.mem_center_iff.mp z.2 g
        exact congrArg (fun k : P ↦ k.1.1.1 v) hc
      have hhz :
          h.1.1.1 (z.1.1.1 v) =
            z.1.1.1 (h.1.1.1 v) := by
        have hc :
            h * z.1 = z.1 * h :=
          Subgroup.mem_center_iff.mp z.2 h
        exact congrArg (fun k : P ↦ k.1.1.1 v) hc
      change
        g.1.1.1 (z.1.1.1 v) =
          h.1.1.1 (z.1.1.1 v)
      rw [hgz, hhz, hgv]
  have htarget :
      Nat.card {w : F3Plane // w ≠ 0} = 8 := by
    rw [Nat.card_eq_fintype_card]
    decide
  rw [← htarget]
  exact Nat.card_le_card_of_injective eval heval

/-- A group whose derived subgroup has order two is noncommutative. -/
private theorem not_isMulCommutative
    {P : Type*} [Group P] [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P) :
    ¬ IsMulCommutative P := by
  intro hPcomm
  have hcenterTop :
      Subgroup.center P = ⊤ := by
    apply top_unique
    intro x _hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact hPcomm.1.1 y x
  have hcommBot :
      commutator P = ⊥ :=
    (commutator_eq_bot_iff_center_eq_top (G := P)).mpr
      hcenterTop
  have hcardOne :
      Nat.card (commutator P) = 1 := by
    rw [hcommBot]
    simp
  have hcardTwo := hcomm.card_commutator
  omega

/-- In the exceptional representation, Hall's cyclic center has order
exactly two.

If its order were larger, the cyclic center would contain an element
whose square is nontrivial.  Evaluation at a nonzero vector would then
embed the whole group into the eight nonzero vectors of `F₃²`.  The
resulting central quotient has order at most two, forcing the group to be
commutative, contrary to the derived subgroup having order two. -/
private theorem natCard_center_eq_two
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 3) F3Plane))
    [Finite P]
    (hP : IsPGroup 2 P)
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hhall : HasCyclicCharacteristicAbelianSubgroups P)
    (C : CenterFixedPointFreeAction 3 2 P) :
    Nat.card (Subgroup.center P) = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Z := Subgroup.center P
  let S := centerSquareKernel P
  have hScard : Nat.card S = 2 :=
    natCard_centerSquareKernel_eq_two
      hcomm hhall.center_isCyclic
  have htwoLeZ : 2 ≤ Nat.card Z := by
    calc
      2 = Nat.card S := hScard.symm
      _ ≤ Nat.card (⊤ : Subgroup Z) :=
        Subgroup.card_le_of_le
          (show S ≤ (⊤ : Subgroup Z) from le_top)
      _ = Nat.card Z := Subgroup.card_top
  by_contra hZne
  have hZgt : 2 < Nat.card Z :=
    lt_of_le_of_ne htwoLeZ (Ne.symm hZne)
  have hSneTop : S ≠ ⊤ := by
    intro hS
    have hcardEq : Nat.card S = Nat.card Z := by
      rw [hS, Subgroup.card_top]
    omega
  obtain ⟨z, hzNotS⟩ :=
    SetLike.exists_not_mem_of_ne_top S hSneTop
  have hzSqNe : z ^ 2 ≠ 1 := by
    intro hz
    exact hzNotS (MonoidHom.mem_ker.mpr hz)
  have hPcard :
      Nat.card P ≤ 8 :=
    natCard_le_eight_of_center_sq_ne_one
      P C z hzSqNe
  let Q := P ⧸ Z
  have hcardEq :
      Nat.card P = Nat.card Q * Nat.card Z := by
    simpa only [Q, Z] using
      Subgroup.card_eq_card_quotient_mul_card_subgroup Z
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  have hQle : Nat.card Q ≤ 2 := by
    nlinarith
  have hQp : IsPGroup 2 Q :=
    hP.to_quotient Z
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
  have hnle : n ≤ 1 := by
    by_contra hnle
    have htwoLeN : 2 ≤ n := by omega
    have hpow :
        2 ^ 2 ≤ 2 ^ n :=
      Nat.pow_le_pow_right (by norm_num : 0 < 2) htwoLeN
    rw [← hn] at hpow
    norm_num at hpow
    omega
  have hQdvd : Nat.card Q ∣ 2 := by
    rw [hn]
    interval_cases n <;> norm_num
  letI : IsCyclic Q :=
    isCyclic_of_card_dvd_prime hQdvd
  apply not_isMulCommutative hcomm
  refine ⟨⟨fun a b ↦
    commutative_of_cyclic_center_quotient
      (QuotientGroup.mk' Z) ?_ a b⟩⟩
  rw [QuotientGroup.ker_mk']

/-- The exceptional central-commutator group in `GL₂(F₃)` has order at
most eight. -/
theorem natCard_le_eight_of_centralCommutator_f3Plane
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 3) F3Plane))
    [Finite P]
    (hP : IsPGroup 2 P)
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hhall : HasCyclicCharacteristicAbelianSubgroups P)
    (C : CenterFixedPointFreeAction 3 2 P) :
    Nat.card P ≤ 8 := by
  have hZ :
      Nat.card (Subgroup.center P) = 2 :=
    natCard_center_eq_two P hP hcomm hhall C
  have hQ :
      Nat.card (P ⧸ Subgroup.center P) ≤ 4 := by
    have h :=
      natCard_quotientCenter_le_dimension_sq_of_centralCommutator
        (by norm_num : (3 : ℕ) ≠ 2)
        (by norm_num : 0 < 2)
        P hcomm C
    norm_num at h ⊢
    exact h
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup,
    hZ]
  omega

/-- Sharp exceptional-edge count.

For a Hall two-subgroup of `GL₂(F₃)` with central derived subgroup of
order two and fixed-point-free center, at most four involutions are
active.  Once the preceding argument gives order at most eight, any
active involution has a noncommuting involution partner by Hall's
omega-one condition.  The pair generates `D₈`, hence the whole group,
and the existing dihedral count applies. -/
theorem card_activePrimeOrderElements_two_le_four_of_centralCommutator_f3Plane
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod 3) F3Plane))
    [Fintype P]
    (hP : IsPGroup 2 P)
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hhall : HasCyclicCharacteristicAbelianSubgroups P)
    (C : CenterFixedPointFreeAction 3 2 P) :
    (activePrimeOrderElements 2 P).card ≤ 4 := by
  classical
  by_cases hactive :
      activePrimeOrderElements 2 P = ∅
  · rw [hactive]
    simp
  · obtain ⟨x, hx⟩ :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    have hxData :=
      (mem_activePrimeOrderElements 2 P x).mp hx
    have hxSq : x ^ 2 = 1 := by
      calc
        x ^ 2 = x ^ orderOf x :=
          congrArg (fun n : ℕ ↦ x ^ n) hxData.1.symm
        _ = 1 := pow_orderOf_eq_one x
    have hxNotCenter :
        x ∉ Subgroup.center P :=
      C.active_not_mem_center x hxData.2
    have hOmegaCenter :
        IsCyclic
          (Subgroup.center (omegaOneSubgroup 2 P)) :=
      hhall.characteristic_center_isCyclic
        (omegaOneSubgroup 2 P)
    obtain ⟨y, hySq, hxy⟩ :=
      exists_noncommuting_involution_of_not_mem_center
        hOmegaCenter hxSq hxNotCenter
    let H : Subgroup P := twoGeneratorSubgroup x y
    let eH : H ≃* DihedralGroup 4 :=
      twoGeneratorSubgroup_mulEquiv_dihedralFour
        hcomm hxSq hySq hxy
    have hHcard : Nat.card H = 8 := by
      calc
        Nat.card H = Nat.card (DihedralGroup 4) :=
          Nat.card_congr eH.toEquiv
        _ = 8 := by
          rw [DihedralGroup.nat_card]
    have hPcardLe : Nat.card P ≤ 8 :=
      natCard_le_eight_of_centralCommutator_f3Plane
        P hP hcomm hhall C
    have hHcardLe : Nat.card H ≤ Nat.card P :=
      by
        simpa using
          (Subgroup.card_le_of_le
            (show H ≤ (⊤ : Subgroup P) from le_top))
    have hPcard : Nat.card P = 8 := by omega
    have hHtop : H = ⊤ :=
      H.eq_top_of_card_eq (hHcard.trans hPcard.symm)
    let eTop : (⊤ : Subgroup P) ≃* DihedralGroup 4 :=
      (MulEquiv.subgroupCongr hHtop).symm.trans eH
    let eP : P ≃* DihedralGroup 4 :=
      Subgroup.topEquiv.symm.trans eTop
    exact
      card_activePrimeOrderElements_two_le_of_dihedral
        (by norm_num : 0 < 4) P eP C

/-- The complete central-commutator representation comparison.

The dimension argument proves the ordinary inequality unless the module
is `F₃²`; the preceding theorem supplies the sharp active count in that
remaining case. -/
theorem centralCommutator_representationComparison
    {r d : ℕ} [Fact r.Prime]
    (hrTwo : r ≠ 2) (hd : 0 < d)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsPGroup 2 P)
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hhall : HasCyclicCharacteristicAbelianSubgroups P)
    (C : CenterFixedPointFreeAction r d P) :
    4 * (Nat.card (P ⧸ Subgroup.center P) - 1) ≤
        r ^ d - 1 ∨
      (r = 3 ∧ d = 2 ∧
        (activePrimeOrderElements 2 P).card ≤ 4) := by
  rcases
      centralCommutator_representationComparison_ordinary_or_f3Plane
        hrTwo hd P hcomm C with
    hordinary | ⟨hr, hd'⟩
  · exact Or.inl hordinary
  · subst r
    subst d
    exact Or.inr
      ⟨rfl, rfl,
        card_activePrimeOrderElements_two_le_four_of_centralCommutator_f3Plane
          P hP hcomm hhall C⟩

end LisiSabatini
