module

public import LisiSabatini.TwoCoreSymplecticTypeHeadRotation
public import LisiSabatini.TwoCoreExtraspecialSchurDegree
public import LisiSabatini.TwoCoreSymplecticTypeExtraspecialCount
public import Mathlib.GroupTheory.GroupAction.CardCommute

/-!
# The head-field degree in a mixed symplectic-type two-core

Let `P = E ∘ H`, with `E` extraspecial and `H` a noncyclic
maximal-class two-group.  Restrict a faithful homogeneous
cross-characteristic representation to `E`.  If

`V |_ E ≃ U^b`

and the Schur field of `U` has order `r^a`, the extraspecial
Stone--von Neumann theorem gives `dim U = a e`.  The head acts on the
multiplicity space

`M = Hom_E(U,V)`,

which has order `r^(a*b)`.  The rotation half-turn is the amalgamated
central involution of `E`; it acts as `-1` on `M`.  Since the rotation
group is cyclic of two-power order, its action on `M \\ {0}` is free.
Consequently its order divides `r^(a*b)-1`.  Finally `b ≠ 1`, since for
`b = 1` the noncommuting head would embed in the commutative Schur
field of `U`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra

set_option backward.isDefEq.respectTransparency false

universe uK uG uV

/-! ## A central involution on a faithful homogeneous module -/

/-- On a faithful homogeneous representation in characteristic other
than two, a nontrivial central involution acts as `-1`. -/
theorem centralInvolution_eq_neg_one_of_homogeneousDimensionData
    {r d : ℕ} [Fact r.Prime]
    {G : Type uG} [Group G]
    (rho : Representation (ZMod r) G
      (Fin d → ZMod r))
    (H : HomogeneousDimensionData r d rho)
    (hfaith : Function.Injective rho)
    (z : Subgroup.center G)
    (hzNe : z ≠ 1) (hzSq : z ^ 2 = 1) :
    rho z.1 = -(1 :
      Module.End (ZMod r) (Fin d → ZMod r)) := by
  classical
  let S := H.constituent
  letI : IsSimpleModule (ZMod r)[G] S :=
    H.constituent_simple
  letI : Module.Finite (ZMod r) S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars (ZMod r))
      S.subtype_injective
  letI : Finite rho.asModule :=
    rho.asModuleEquiv.toEquiv.finite_iff.mpr inferInstance
  letI : Finite S :=
    Finite.of_injective S.subtype S.subtype_injective
  letI : Module.Finite (ZMod r)
      (Module.End (ZMod r)[G] S) :=
    moduleFinite_schurEnd
      (k := ZMod r) (A := (ZMod r)[G]) (S := S)
  letI : Finite (Module.End (ZMod r)[G] S) :=
    Module.finite_of_finite (ZMod r)
  let D := SchurField (ZMod r)[G] S
  letI : Field D := by
    dsimp only [D]
    infer_instance
  let f : Module.End (ZMod r)[G] S :=
    centralConstituentAction rho S z
  have hfNe : f ≠ 1 := by
    intro hf
    have hinj :
        Function.Injective
          (centralConstituentActionHom rho S) :=
      centralConstituentActionHom_injective_of_decomposition
        rho hfaith H.decomposition.some
    apply hzNe
    apply hinj
    simpa [f] using hf
  have hfSq : f ^ 2 = 1 := by
    have hmap :=
      map_pow (centralConstituentActionHom rho S) z 2
    rw [hzSq, map_one] at hmap
    simpa [f] using hmap.symm
  let fd : D := ⟨f⟩
  have hfdNe : fd ≠ 1 := by
    intro h
    apply hfNe
    simpa using congrArg SchurField.val h
  have hfdSq : fd ^ 2 = 1 := by
    apply
      (SchurField.ringEquiv
        (A := (ZMod r)[G]) (S := S)).injective
    simpa [fd] using hfSq
  have hfdNeg : fd = -1 :=
    (sq_eq_one_iff.mp hfdSq).resolve_left hfdNe
  have hfNeg : f = (-1 : D).val := by
    exact congrArg SchurField.val hfdNeg
  apply LinearMap.ext
  intro v
  let u : rho.asModule := rho.asModuleEquiv.symm v
  apply rho.asModuleEquiv.symm.injective
  apply H.decomposition.some.injective
  ext i
  have hcoord :
      f (H.decomposition.some u i) =
        -(H.decomposition.some u i) := by
    rw [hfNeg]
    rfl
  change
    MonoidAlgebra.of (ZMod r) G z.1 •
        H.decomposition.some u i =
      -(H.decomposition.some u i) at hcoord
  apply congrArg Subtype.val
  change
    H.decomposition.some
        (rho.asModuleEquiv.symm (rho z.1 v)) i =
      H.decomposition.some
        (rho.asModuleEquiv.symm
          ((-(1 : Module.End (ZMod r)
            (Fin d → ZMod r))) v)) i
  rw [rho.asModuleEquiv_symm_map_rho]
  change
    H.decomposition.some
        (MonoidAlgebra.of (ZMod r) G z.1 • u) i =
      H.decomposition.some
        (rho.asModuleEquiv.symm (-v)) i
  rw [LinearEquiv.map_smul]
  simpa [u] using hcoord

/-! ## A finite free-action count -/

/-- A finite group acting freely on a finite type has order dividing the
cardinality of that type. -/
theorem natCard_dvd_natCard_of_stabilizers_bot
    {G X : Type*} [Group G] [Finite G] [Finite X]
    [MulAction G X]
    (hstab : ∀ x : X, MulAction.stabilizer G x = ⊥) :
    Nat.card G ∣ Nat.card X := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype X := Fintype.ofFinite X
  let Ω := Quotient (MulAction.orbitRel G X)
  letI : Fintype Ω := Fintype.ofFinite Ω
  have hclass :=
    MulAction.card_eq_sum_card_group_div_card_stabilizer G X
  refine ⟨Fintype.card Ω, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  calc
    Fintype.card X =
        ∑ ω : Ω, Fintype.card G /
          Fintype.card (MulAction.stabilizer G ω.out) :=
      hclass
    _ = ∑ _ω : Ω, Fintype.card G := by
      apply Finset.sum_congr rfl
      intro ω _
      have hc :
          Fintype.card (MulAction.stabilizer G ω.out) = 1 := by
        rw [← Nat.card_eq_fintype_card, Subgroup.card_eq_one]
        exact hstab ω.out
      rw [hc, Nat.div_one]
    _ = Fintype.card G * Fintype.card Ω := by
      simp [mul_comm]

/-- If the relevant gcd divides an exponent, that power belongs to the
cyclic subgroup generated by the other power. -/
private theorem pow_mem_zpowers_pow_of_gcd_dvd
    {G : Type*} [Group G] {g : G} {m n : ℕ}
    (h : Nat.gcd n (orderOf g) ∣ m) :
    g ^ m ∈ Subgroup.zpowers (g ^ n) := by
  obtain ⟨k, rfl⟩ := h
  apply Subgroup.mem_zpowers_iff.mpr
  refine
    ⟨(Nat.gcdA n (orderOf g)) * (k : ℤ), ?_⟩
  rw [← zpow_natCast g n]
  rw [← zpow_natCast g
    (Nat.gcd n (orderOf g) * k)]
  rw [← zpow_mul, zpow_eq_zpow_iff_modEq]
  have hmod := Int.gcd_a_modEq n (orderOf g)
  have hmodk := hmod.mul_right (k : ℤ)
  simpa [Int.natCast_mul, mul_assoc] using hmodk

/-- Cyclic subgroups in a finite cyclic `p`-group are comparable. -/
private theorem zpowers_le_or_le_of_isCyclic_isPGroup
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G) [IsCyclic G]
    (a b : G) :
    Subgroup.zpowers a ≤ Subgroup.zpowers b ∨
      Subgroup.zpowers b ≤ Subgroup.zpowers a := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ :=
    IsCyclic.exists_monoid_generator (α := G)
  obtain ⟨m, hm⟩ := hg a
  obtain ⟨n, hn⟩ := hg b
  rw [← hm, ← hn]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hGp) g
  obtain ⟨i, _hi, hmi⟩ :=
    (Nat.dvd_prime_pow hp).mp
      (hk ▸ Nat.gcd_dvd_right m (orderOf g))
  obtain ⟨j, _hj, hnj⟩ :=
    (Nat.dvd_prime_pow hp).mp
      (hk ▸ Nat.gcd_dvd_right n (orderOf g))
  rcases le_total i j with hij | hji
  · right
    apply Subgroup.zpowers_le_of_mem
    apply pow_mem_zpowers_pow_of_gcd_dvd
    have hd :
        Nat.gcd m (orderOf g) ∣
          Nat.gcd n (orderOf g) := by
      rw [hk, hmi, hnj]
      exact pow_dvd_pow p hij
    exact hd.trans (Nat.gcd_dvd_left n (orderOf g))
  · left
    apply Subgroup.zpowers_le_of_mem
    apply pow_mem_zpowers_pow_of_gcd_dvd
    have hd :
        Nat.gcd n (orderOf g) ∣
          Nat.gcd m (orderOf g) := by
      rw [hk, hmi, hnj]
      exact pow_dvd_pow p hji
    exact hd.trans (Nat.gcd_dvd_left m (orderOf g))

/-- In a cyclic two-group, if its unique involution acts as negation and
negation has no nonzero fixed point, every nonzero stabilizer is trivial. -/
theorem stabilizer_eq_bot_of_cyclic_twoGroup_of_involution_neg
    {C M : Type*} [Group C] [Finite C] [IsCyclic C]
    (hC : IsPGroup 2 C)
    [AddCommGroup M] [MulAction C M]
    (z : C) (hzOrder : orderOf z = 2)
    (hneg : ∀ m : M, z • m = -m)
    (hnegFixed : ∀ m : M, -m = m → m = 0)
    (m : M) (hm : m ≠ 0) :
    MulAction.stabilizer C m = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  by_contra hgNe
  have hzNe : z ≠ 1 := by
    intro hz
    rw [hz, orderOf_one] at hzOrder
    omega
  have hzMem : z ∈ Subgroup.zpowers g := by
    rcases
        zpowers_le_or_le_of_isCyclic_isPGroup
          Nat.prime_two hC z g with hzg | hgz
    · exact hzg (Subgroup.mem_zpowers z)
    · have hgMem : g ∈ Subgroup.zpowers z :=
        hgz (Subgroup.mem_zpowers g)
      let gz : Subgroup.zpowers z := ⟨g, hgMem⟩
      let zz : Subgroup.zpowers z :=
        ⟨z, Subgroup.mem_zpowers z⟩
      have hcard : Nat.card (Subgroup.zpowers z) = 2 := by
        rw [Nat.card_zpowers, hzOrder]
      have hgSubNe : gz ≠ 1 := by
        intro h
        apply hgNe
        exact congrArg Subtype.val h
      have hzSubNe : zz ≠ 1 := by
        intro h
        apply hzNe
        exact congrArg Subtype.val h
      have hunique :=
        (Nat.card_eq_two_iff'
          (1 : Subgroup.zpowers z)).mp hcard
      have hgzEq : gz = zz :=
        (hunique.choose_spec.2 gz hgSubNe).trans
          (hunique.choose_spec.2 zz hzSubNe).symm
      have hgEq : g = z :=
        congrArg Subtype.val hgzEq
      rw [hgEq]
      exact Subgroup.mem_zpowers z
  have hzStab :
      z ∈ MulAction.stabilizer C m :=
    (Subgroup.zpowers_le_of_mem hg) hzMem
  have hzFix :
      z • m = m :=
    MulAction.mem_stabilizer_iff.mp hzStab
  apply hm
  exact hnegFixed m ((hneg m).symm.trans hzFix)

/-! ## The extraspecial multiplicity space -/

namespace BergerMixedCentralProductData

variable {r d : ℕ} [Fact r.Prime]
  (P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
  [Fintype P]

abbrev ambientRepresentation :
    Representation (ZMod r) P (Fin d → ZMod r) :=
  linearSubgroupRepresentation P

/-- The ambient representation restricted to the extraspecial factor. -/
abbrev extraspecialRepresentation
    (data : BergerMixedCentralProductData P) :
    Representation (ZMod r) data.extraspecialPart
      (Fin d → ZMod r) :=
  (ambientRepresentation P).comp data.extraspecialPart.subtype

/-- A head element commutes with `E`, hence acts by an endomorphism of
the restricted `ZMod r[E]`-module. -/
def headRestrictedEnd
    (data : BergerMixedCentralProductData P)
    (h : data.headPart) :
    Module.End (ZMod r)[data.extraspecialPart]
      (extraspecialRepresentation P data).asModule where
  toFun u :=
    (extraspecialRepresentation P data).asModuleEquiv.symm
      ((ambientRepresentation P) h.1
        ((extraspecialRepresentation P data).asModuleEquiv u))
  map_add' u v := by simp
  map_smul' c u := by
    apply
      (extraspecialRepresentation P data).asModuleEquiv.injective
    rw [(extraspecialRepresentation P data).asModuleEquiv_map_smul]
    change
      (ambientRepresentation P) h.1
          ((extraspecialRepresentation P data).asAlgebraHom c
            ((extraspecialRepresentation P data).asModuleEquiv u)) =
        (extraspecialRepresentation P data).asAlgebraHom c
          ((ambientRepresentation P) h.1
            ((extraspecialRepresentation P data).asModuleEquiv u))
    induction c using MonoidAlgebra.induction_on with
    | hM x =>
        simp only [Representation.asAlgebraHom_of]
        change
          (ambientRepresentation P) h.1
              ((ambientRepresentation P) x.1
                ((extraspecialRepresentation P data).asModuleEquiv u)) =
            (ambientRepresentation P) x.1
              ((ambientRepresentation P) h.1
                ((extraspecialRepresentation P data).asModuleEquiv u))
        simp only [← Module.End.mul_apply, ← map_mul]
        exact congrArg
          (fun T : Module.End (ZMod r) (Fin d → ZMod r) ↦
            T ((extraspecialRepresentation P data).asModuleEquiv u))
          (congrArg (ambientRepresentation P)
            (data.commute x h).symm)
    | hadd c₁ c₂ hc₁ hc₂ =>
        simp only [map_add, LinearMap.add_apply]
        exact congrArg₂ (· + ·) hc₁ hc₂
    | hsmul a c hc =>
        simp only [map_smul, LinearMap.smul_apply]
        exact congrArg (fun z ↦ a • z) hc

private theorem headRestrictedEnd_mul
    (data : BergerMixedCentralProductData P)
    (g h : data.headPart) :
    data.headRestrictedEnd P (g * h) =
      data.headRestrictedEnd P g *
        data.headRestrictedEnd P h := by
  apply LinearMap.ext
  intro u
  apply
    (extraspecialRepresentation P data).asModuleEquiv.injective
  change
    (ambientRepresentation P) (g.1 * h.1)
        ((extraspecialRepresentation P data).asModuleEquiv u) =
      (ambientRepresentation P) g.1
        ((ambientRepresentation P) h.1
          ((extraspecialRepresentation P data).asModuleEquiv u))
  rw [map_mul]
  rfl

private theorem headRestrictedEnd_injective
    (data : BergerMixedCentralProductData P) :
    Function.Injective (data.headRestrictedEnd P) := by
  intro g h hgh
  apply Subtype.ext
  apply (linearSubgroupRepresentation_faithful P)
  apply LinearMap.ext
  intro v
  let u :=
    (extraspecialRepresentation P data).asModuleEquiv.symm v
  have huv :=
    LinearMap.congr_fun hgh u
  have huv' :=
    congrArg
      (extraspecialRepresentation P data).asModuleEquiv huv
  simpa [u, headRestrictedEnd] using huv'

@[simp]
private theorem headRestrictedEnd_one
    (data : BergerMixedCentralProductData P) :
    data.headRestrictedEnd P 1 = 1 := by
  apply LinearMap.ext
  intro u
  apply
    (extraspecialRepresentation P data).asModuleEquiv.injective
  simp [headRestrictedEnd]

/-- The head action on `Hom_E(U,V)` by postcomposition. -/
@[reducible] def multiplicityMulAction
    (data : BergerMixedCentralProductData P)
    (U : Type*) [AddCommGroup U]
    [Module (ZMod r)[data.extraspecialPart] U] :
    DistribMulAction data.headPart
      (U →ₗ[(ZMod r)[data.extraspecialPart]]
        (extraspecialRepresentation P data).asModule) where
  smul h f := (data.headRestrictedEnd P h).comp f
  one_smul f := by
    change
      (data.headRestrictedEnd P 1).comp f = f
    rw [data.headRestrictedEnd_one P]
    ext u
    rfl
  mul_smul g h f := by
    change
      (data.headRestrictedEnd P (g * h)).comp f =
        (data.headRestrictedEnd P g).comp
          ((data.headRestrictedEnd P h).comp f)
    rw [data.headRestrictedEnd_mul P]
    ext u
    rfl
  smul_zero h := by
    change
      (data.headRestrictedEnd P h).comp 0 = 0
    ext u
    simp
  smul_add h f g := by
    change
      (data.headRestrictedEnd P h).comp (f + g) =
        (data.headRestrictedEnd P h).comp f +
          (data.headRestrictedEnd P h).comp g
    ext u
    simp

/-- Coordinates identify the multiplicity space with one copy of the
constituent endomorphism ring for each homogeneous summand. -/
private def multiplicityHomEquiv
    (data : BergerMixedCentralProductData P)
    (H : HomogeneousDimensionData r d
      (extraspecialRepresentation P data)) :
    (H.constituent →ₗ[(ZMod r)[data.extraspecialPart]]
        (extraspecialRepresentation P data).asModule) ≃
      (Fin H.multiplicity →
        Module.End (ZMod r)[data.extraspecialPart]
          H.constituent) where
  toFun f i :=
    (LinearMap.proj i).comp
      (H.decomposition.some.toLinearMap.comp f)
  invFun F :=
    H.decomposition.some.symm.toLinearMap.comp
      (LinearMap.pi F)
  left_inv f := by
    apply LinearMap.ext
    intro u
    apply H.decomposition.some.injective
    ext i
    simp
  right_inv F := by
    funext i
    apply LinearMap.ext
    intro u
    simp

/-- The multiplicity space has one Schur-field coordinate for every
homogeneous summand. -/
theorem natCard_multiplicitySpace
    (data : BergerMixedCentralProductData P)
    (H : HomogeneousDimensionData r d
      (extraspecialRepresentation P data))
    (a : ℕ)
    (hEndCard :
      Nat.card
        (Module.End (ZMod r)[data.extraspecialPart]
          H.constituent) = r ^ a) :
    Nat.card
        (H.constituent →ₗ[(ZMod r)[data.extraspecialPart]]
          (extraspecialRepresentation P data).asModule) =
      r ^ (a * H.multiplicity) := by
  rw [Nat.card_congr (data.multiplicityHomEquiv P H),
    Nat.card_fun, Nat.card_fin, hEndCard, pow_mul]

set_option maxHeartbeats 500000 in
-- The multiplicity-one contradiction constructs an explicit conjugating
-- equivalence and then transports Schur-field commutativity through it.
/-- Multiplicity one would realize the noncommuting head inside the
commutative finite Schur field of the simple constituent. -/
theorem multiplicity_ne_one
    (data : BergerMixedCentralProductData P)
    (H : HomogeneousDimensionData r d
      (extraspecialRepresentation P data)) :
    H.multiplicity ≠ 1 := by
  classical
  intro hb
  let S := H.constituent
  letI : IsSimpleModule
      (ZMod r)[data.extraspecialPart] S :=
    H.constituent_simple
  letI : Module.Finite (ZMod r) S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars (ZMod r))
      S.subtype_injective
  letI : Finite
      (extraspecialRepresentation P data).asModule :=
    (extraspecialRepresentation P data).asModuleEquiv.toEquiv.finite_iff.mpr
      inferInstance
  letI : Finite S :=
    Finite.of_injective S.subtype S.subtype_injective
  letI : Finite
      (Module.End (ZMod r)[data.extraspecialPart] S) :=
    Finite.of_injective
      (fun f :
        Module.End (ZMod r)[data.extraspecialPart] S ↦
          (f : S → S))
      LinearMap.coe_injective
  let D := SchurField
    (ZMod r)[data.extraspecialPart] S
  letI : Field D := by
    dsimp only [D]
    infer_instance
  let i0 : Fin H.multiplicity :=
    ⟨0, Nat.pos_of_ne_zero
      H.multiplicity_neZero.out⟩
  let eMap :
      (extraspecialRepresentation P data).asModule →ₗ[
        (ZMod r)[data.extraspecialPart]] S :=
    (LinearMap.proj i0).comp
      H.decomposition.some.toLinearMap
  have heMapInj : Function.Injective eMap := by
    intro v w hvw
    apply H.decomposition.some.injective
    funext i
    have hi : i = i0 := by
      apply Fin.ext
      omega
    rw [hi]
    simpa [eMap] using hvw
  have heMapSurj : Function.Surjective eMap := by
    intro s
    refine
      ⟨H.decomposition.some.symm (fun _ ↦ s), ?_⟩
    change
      (H.decomposition.some
        (H.decomposition.some.symm (fun _ ↦ s))) i0 = s
    rw [LinearEquiv.apply_symm_apply]
  let e :
      (extraspecialRepresentation P data).asModule ≃ₗ[
        (ZMod r)[data.extraspecialPart]] S :=
    LinearEquiv.ofBijective eMap
      ⟨heMapInj, heMapSurj⟩
  have hEndComm
      (f g :
        Module.End (ZMod r)[data.extraspecialPart]
          (extraspecialRepresentation P data).asModule) :
      f * g = g * f := by
    apply e.conjRingEquiv.injective
    let fd : D := ⟨e.conjRingEquiv f⟩
    let gd : D := ⟨e.conjRingEquiv g⟩
    have hcomm : fd * gd = gd * fd := mul_comm fd gd
    have hcommEnd :
        e.conjRingEquiv f * e.conjRingEquiv g =
          e.conjRingEquiv g * e.conjRingEquiv f := by
      exact congrArg SchurField.val hcomm
    calc
      e.conjRingEquiv (f * g) =
          e.conjRingEquiv f * e.conjRingEquiv g :=
        e.conjRingEquiv.map_mul f g
      _ = e.conjRingEquiv g * e.conjRingEquiv f :=
        hcommEnd
      _ = e.conjRingEquiv (g * f) :=
        (e.conjRingEquiv.map_mul g f).symm
  apply data.head.rotation_companion_ne_companion_rotation
  apply data.headRestrictedEnd_injective P
  rw [data.headRestrictedEnd_mul P,
    data.headRestrictedEnd_mul P]
  exact hEndComm _ _

/-- The common extraspecial/head involution acts as `-1` on the
restricted module. -/
theorem headRestrictedEnd_halfTurn_eq_neg_one
    (data : BergerMixedCentralProductData P)
    (H : HomogeneousDimensionData r d
      (extraspecialRepresentation P data))
    {e : ℕ}
    (extra : ExtraspecialTwoSquareCountData
      data.extraspecialPart e) :
    data.headRestrictedEnd P data.head.halfTurn =
      -(1 :
        Module.End (ZMod r)[data.extraspecialPart]
          (extraspecialRepresentation P data).asModule) := by
  let zHead := data.headCentralInvolution extra
  have hzHeadSq : zHead.1 ^ 2 = 1 := by
    exact congrArg Subtype.val
      (data.headCentralInvolution_sq extra)
  have hzHeadNe : zHead.1 ≠ 1 := by
    intro hz
    apply data.headCentralInvolution_ne_one extra
    exact Subtype.ext hz
  have hzHeadEq :
      zHead.1 = data.head.halfTurn :=
    data.head.eq_halfTurn_of_mem_center_of_sq_eq_one_of_ne_one
      zHead.1 zHead.2 hzHeadSq hzHeadNe
  have hzExtraOperator :
      (extraspecialRepresentation P data)
          extra.centralInvolution.1 =
        -(1 :
          Module.End (ZMod r) (Fin d → ZMod r)) :=
    centralInvolution_eq_neg_one_of_homogeneousDimensionData
      (extraspecialRepresentation P data) H
      ((linearSubgroupRepresentation_faithful P).comp
        data.extraspecialPart.subtype_injective)
      extra.centralInvolution
      extra.centralInvolution_ne_one
      extra.centralInvolution_sq
  apply LinearMap.ext
  intro u
  apply
    (extraspecialRepresentation P data).asModuleEquiv.injective
  change
    (ambientRepresentation P) data.head.halfTurn.1
        ((extraspecialRepresentation P data).asModuleEquiv u) =
      (extraspecialRepresentation P data).asModuleEquiv (-u)
  rw [← hzHeadEq]
  change
    (extraspecialRepresentation P data)
        extra.centralInvolution.1
        ((extraspecialRepresentation P data).asModuleEquiv u) =
      (extraspecialRepresentation P data).asModuleEquiv (-u)
  rw [hzExtraOperator]
  simp

end BergerMixedCentralProductData

end LisiSabatini
