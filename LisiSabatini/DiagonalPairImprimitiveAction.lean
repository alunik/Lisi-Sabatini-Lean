module

public import LisiSabatini.AffineTwoBaseTranslates
public import LisiSabatini.ImprimitiveBundleMarkerCore

/-!
# Diagonal pairs of imprimitive linear actions

The affine two-base problem is ordinary regularity on the diagonal action on
two copies of the module.  For an imprimitive action on `I → W`, this file
identifies that doubled representation with `I → (W × W)` and transports the
imprimitive action data through the identification.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

/-- Pair two functions coordinatewise. -/
def piProdLinearEquiv :
    ((I → W) × (I → W)) ≃ₗ[R] (I → W × W) where
  toFun z i := (z.1 i, z.2 i)
  invFun x := (fun i ↦ (x i).1, fun i ↦ (x i).2)
  left_inv z := by
    rcases z with ⟨x, y⟩
    rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem piProdLinearEquiv_apply
    (z : (I → W) × (I → W)) (i : I) :
    piProdLinearEquiv (R := R) z i = (z.1 i, z.2 i) :=
  rfl

@[simp]
theorem piProdLinearEquiv_symm_apply_fst
    (x : I → W × W) :
    ((piProdLinearEquiv (R := R)).symm x).1 =
      fun i ↦ (x i).1 :=
  rfl

@[simp]
theorem piProdLinearEquiv_symm_apply_snd
    (x : I → W × W) :
    ((piProdLinearEquiv (R := R)).symm x).2 =
      fun i ↦ (x i).2 :=
  rfl

/-- The diagonal action on two global vectors, rewritten as an action on
blockwise pairs. -/
def pairedGeneralLinearHom :
    LinearMap.GeneralLinearGroup R (I → W) →*
      LinearMap.GeneralLinearGroup R (I → W × W) :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (piProdLinearEquiv (R := R))).toMonoidHom.comp
    (diagonalGeneralLinearHom R (I → W))

@[simp]
theorem pairedGeneralLinearHom_smul
    (g : LinearMap.GeneralLinearGroup R (I → W))
    (x : I → W × W) (i : I) :
    (pairedGeneralLinearHom (R := R) g • x) i =
      ((g • fun j ↦ (x j).1) i,
        (g • fun j ↦ (x j).2) i) := by
  rfl

/-- The paired representation is faithful. -/
theorem pairedGeneralLinearHom_injective :
    Function.Injective
      (pairedGeneralLinearHom (I := I) (R := R) (W := W)) :=
  (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (piProdLinearEquiv (R := R))).injective.comp
    (diagonalGeneralLinearHom_injective R (I → W))

/-- The image of a linear group in the blockwise-paired representation. -/
def pairedSubgroup
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W))) :
    Subgroup (LinearMap.GeneralLinearGroup R (I → W × W)) :=
  K.map pairedGeneralLinearHom

/-- The canonical equivalence with the paired image. -/
def pairedSubgroupEquiv
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W))) :
    K ≃* pairedSubgroup K :=
  K.equivMapOfInjective pairedGeneralLinearHom
    pairedGeneralLinearHom_injective

@[simp]
theorem pairedSubgroupEquiv_coe
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (g : K) :
    ((pairedSubgroupEquiv K g : pairedSubgroup K) :
      LinearMap.GeneralLinearGroup R (I → W × W)) =
        pairedGeneralLinearHom g :=
  Subgroup.coe_equivMapOfInjective_apply
    K pairedGeneralLinearHom pairedGeneralLinearHom_injective g

/-- An internal subgroup transported to the paired representation. -/
def pairedInternalSubgroup
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) : Subgroup (pairedSubgroup K) :=
  H.map (pairedSubgroupEquiv K).toMonoidHom

/-- The canonical equivalence between an internal subgroup and its paired
image. -/
def pairedInternalSubgroupEquiv
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) :
    H ≃* pairedInternalSubgroup K H :=
  H.equivMapOfInjective (pairedSubgroupEquiv K).toMonoidHom
    (pairedSubgroupEquiv K).injective

@[simp]
theorem pairedInternalSubgroupEquiv_coe
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) (g : H) :
    ((pairedInternalSubgroupEquiv K H g : pairedInternalSubgroup K H) :
      pairedSubgroup K) =
        pairedSubgroupEquiv K g :=
  Subgroup.coe_equivMapOfInjective_apply
    H (pairedSubgroupEquiv K).toMonoidHom
      (pairedSubgroupEquiv K).injective g

theorem pairedInternalSubgroup_normal
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) (hH : H.Normal) :
    (pairedInternalSubgroup K H).Normal :=
  hH.map (pairedSubgroupEquiv K).toMonoidHom
    (pairedSubgroupEquiv K).surjective

theorem pairedInternalSubgroup_isPGroup
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    {p : ℕ} (H : Subgroup K) (hH : IsPGroup p H) :
    IsPGroup p (pairedInternalSubgroup K H) :=
  hH.map (pairedSubgroupEquiv K).toMonoidHom

/-- Mapping a paired internal subgroup into the ambient general linear group
is the same as pairing its original ambient image. -/
theorem pairedInternalSubgroup_map_subtype
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) :
    (pairedInternalSubgroup K H).map (pairedSubgroup K).subtype =
      (H.map K.subtype).map pairedGeneralLinearHom := by
  rw [pairedInternalSubgroup, Subgroup.map_map, Subgroup.map_map]
  congr 1

/-- The diagonal image of a common local block group. -/
def diagonalLocalSubgroup
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) :
    Subgroup (LinearMap.GeneralLinearGroup R (W × W)) :=
  L.map (diagonalGeneralLinearHom R W)

/-- The canonical equivalence with a diagonal local image. -/
def diagonalLocalSubgroupEquiv
    (L : Subgroup (LinearMap.GeneralLinearGroup R W)) :
    L ≃* diagonalLocalSubgroup L :=
  L.equivMapOfInjective (diagonalGeneralLinearHom R W)
    (diagonalGeneralLinearHom_injective R W)

@[simp]
theorem diagonalLocalSubgroupEquiv_coe
    (L : Subgroup (LinearMap.GeneralLinearGroup R W))
    (g : L) :
    ((diagonalLocalSubgroupEquiv L g : diagonalLocalSubgroup L) :
      LinearMap.GeneralLinearGroup R (W × W)) =
        diagonalGeneralLinearHom R W g :=
  Subgroup.coe_equivMapOfInjective_apply
    L (diagonalGeneralLinearHom R W)
      (diagonalGeneralLinearHom_injective R W) g

/-- An internal subgroup transported to the diagonal local
representation. -/
def diagonalInternalSubgroup
    (L : Subgroup (LinearMap.GeneralLinearGroup R W))
    (A : Subgroup L) : Subgroup (diagonalLocalSubgroup L) :=
  A.map (diagonalLocalSubgroupEquiv L).toMonoidHom

/-- The canonical equivalence with an internal diagonal image. -/
def diagonalInternalSubgroupEquiv
    (L : Subgroup (LinearMap.GeneralLinearGroup R W))
    (A : Subgroup L) :
    A ≃* diagonalInternalSubgroup L A :=
  A.equivMapOfInjective (diagonalLocalSubgroupEquiv L).toMonoidHom
    (diagonalLocalSubgroupEquiv L).injective

theorem diagonalInternalSubgroup_normal
    (L : Subgroup (LinearMap.GeneralLinearGroup R W))
    (A : Subgroup L) (hA : A.Normal) :
    (diagonalInternalSubgroup L A).Normal :=
  hA.map (diagonalLocalSubgroupEquiv L).toMonoidHom
    (diagonalLocalSubgroupEquiv L).surjective

theorem diagonalInternalSubgroup_isPGroup
    (L : Subgroup (LinearMap.GeneralLinearGroup R W))
    {p : ℕ} (A : Subgroup L) (hA : IsPGroup p A) :
    IsPGroup p (diagonalInternalSubgroup L A) :=
  hA.map (diagonalLocalSubgroupEquiv L).toMonoidHom

/-- Mapping an internal diagonal subgroup into the ambient paired local
general linear group agrees with first exposing the original local action
and then taking its diagonal image. -/
theorem diagonalInternalSubgroup_map_subtype
    (L : Subgroup (LinearMap.GeneralLinearGroup R W))
    (A : Subgroup L) :
    (diagonalInternalSubgroup L A).map (diagonalLocalSubgroup L).subtype =
      (A.map L.subtype).map (diagonalGeneralLinearHom R W) := by
  rw [diagonalInternalSubgroup, Subgroup.map_map, Subgroup.map_map]
  congr 1

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- The imprimitive data on blockwise pairs induced by a diagonal pair of
global vectors. -/
def diagonalPair
    (D : ImprimitiveLinearActionData K L) :
    ImprimitiveLinearActionData
      (pairedSubgroup K) (diagonalLocalSubgroup L) where
  blockPerm :=
    D.blockPerm.comp (pairedSubgroupEquiv K).symm.toMonoidHom
  blockLinear g i :=
    diagonalLocalSubgroupEquiv L
      (D.blockLinear ((pairedSubgroupEquiv K).symm g) i)
  action_apply g x i := by
    let g₀ : K := (pairedSubgroupEquiv K).symm g
    have hg : pairedSubgroupEquiv K g₀ = g :=
      (pairedSubgroupEquiv K).apply_symm_apply g
    have hgCoe :
        pairedGeneralLinearHom g₀.1 = g.1 := by
      simpa only [pairedSubgroupEquiv_coe] using
        congrArg Subtype.val hg
    rw [← hgCoe]
    apply Prod.ext
    · change
        (g₀.1 • (fun j ↦ (x j).1)) i =
          (D.blockLinear g₀ i).1 •
            (x ((D.blockPerm g₀).symm i)).1
      exact D.action_apply g₀ (fun j ↦ (x j).1) i
    · change
        (g₀.1 • (fun j ↦ (x j).2)) i =
          (D.blockLinear g₀ i).1 •
            (x ((D.blockPerm g₀).symm i)).2
      exact D.action_apply g₀ (fun j ↦ (x j).2) i

@[simp]
theorem diagonalPair_blockPerm
    (D : ImprimitiveLinearActionData K L)
    (g : pairedSubgroup K) :
    D.diagonalPair.blockPerm g =
      D.blockPerm ((pairedSubgroupEquiv K).symm g) :=
  rfl

/-- Pairing the representation does not change its permutation top. -/
theorem diagonalPair_blockPerm_range
    (D : ImprimitiveLinearActionData K L) :
    D.diagonalPair.blockPerm.range = D.blockPerm.range := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨(pairedSubgroupEquiv K).symm g, rfl⟩
  · rintro ⟨g, rfl⟩
    refine ⟨pairedSubgroupEquiv K g, ?_⟩
    simp

/-- Canonical identification of the concrete ambient copy of an internal
component with the concrete ambient copy of its paired image. -/
def pairedRestrictedAmbientEquiv
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) :
    restrictedAmbient H ≃*
      restrictedAmbient (pairedInternalSubgroup K H) :=
  (H.equivMapOfInjective K.subtype K.subtype_injective).symm |>.trans
    ((pairedInternalSubgroupEquiv K H).trans
      ((pairedInternalSubgroup K H).equivMapOfInjective
        (pairedSubgroup K).subtype
        (pairedSubgroup K).subtype_injective))

@[simp]
theorem pairedRestrictedAmbientEquiv_coe
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) (g : restrictedAmbient H) :
    ((pairedRestrictedAmbientEquiv K H g :
        restrictedAmbient (pairedInternalSubgroup K H)) :
      LinearMap.GeneralLinearGroup R (I → W × W)) =
        pairedGeneralLinearHom (g :
          LinearMap.GeneralLinearGroup R (I → W)) := by
  let eH : H ≃* restrictedAmbient H :=
    H.equivMapOfInjective K.subtype K.subtype_injective
  let eI : H ≃* pairedInternalSubgroup K H :=
    pairedInternalSubgroupEquiv K H
  let eA : pairedInternalSubgroup K H ≃*
      restrictedAmbient (pairedInternalSubgroup K H) :=
    (pairedInternalSubgroup K H).equivMapOfInjective
      (pairedSubgroup K).subtype
      (pairedSubgroup K).subtype_injective
  let h : H := eH.symm g
  have hh : ((h : K) :
      LinearMap.GeneralLinearGroup R (I → W)) = g := by
    exact congrArg Subtype.val (eH.apply_symm_apply g)
  calc
    ((pairedRestrictedAmbientEquiv K H g :
        restrictedAmbient (pairedInternalSubgroup K H)) :
      LinearMap.GeneralLinearGroup R (I → W × W)) =
        ((eA (eI h) : restrictedAmbient (pairedInternalSubgroup K H)) :
          LinearMap.GeneralLinearGroup R (I → W × W)) := rfl
    _ = ((eI h : pairedInternalSubgroup K H) :
        LinearMap.GeneralLinearGroup R (I → W × W)) := by
      exact Subgroup.coe_equivMapOfInjective_apply
        (pairedInternalSubgroup K H) (pairedSubgroup K).subtype
          (pairedSubgroup K).subtype_injective (eI h)
    _ = ((pairedSubgroupEquiv K h : pairedSubgroup K) :
        LinearMap.GeneralLinearGroup R (I → W × W)) := by
      exact congrArg Subtype.val
        (pairedInternalSubgroupEquiv_coe K H h)
    _ = pairedGeneralLinearHom (h : K) :=
      pairedSubgroupEquiv_coe K h
    _ = pairedGeneralLinearHom g := congrArg pairedGeneralLinearHom hh

@[simp]
theorem pairedSubgroupEquiv_symm_restrictedAmbient
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) (g : restrictedAmbient H) :
    (pairedSubgroupEquiv K).symm
        (restrictedAmbientToCommon (pairedInternalSubgroup K H)
          (pairedRestrictedAmbientEquiv K H g)) =
      restrictedAmbientToCommon H g := by
  apply (pairedSubgroupEquiv K).injective
  rw [(pairedSubgroupEquiv K).apply_symm_apply]
  apply Subtype.ext
  exact pairedRestrictedAmbientEquiv_coe K H g

@[simp]
theorem diagonalPair_restrictComponent_blockPerm_paired
    (D : ImprimitiveLinearActionData K L)
    (H : Subgroup K) (g : restrictedAmbient H) :
    (D.diagonalPair.restrictComponent (pairedInternalSubgroup K H)).blockPerm
        (pairedRestrictedAmbientEquiv K H g) =
      (D.restrictComponent H).blockPerm g := by
  exact congrArg D.blockPerm
    (pairedSubgroupEquiv_symm_restrictedAmbient K H g)

/-- Restricting to a component and pairing the representation leaves that
component's permutation range unchanged. -/
theorem diagonalPair_restrictComponent_blockPerm_range
    (D : ImprimitiveLinearActionData K L)
    (H : Subgroup K) :
    (D.diagonalPair.restrictComponent
        (pairedInternalSubgroup K H)).blockPerm.range =
      (D.restrictComponent H).blockPerm.range := by
  ext σ
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := (pairedRestrictedAmbientEquiv K H).surjective g
    exact ⟨h, (diagonalPair_restrictComponent_blockPerm_paired D H h).symm⟩
  · rintro ⟨g, rfl⟩
    refine ⟨pairedRestrictedAmbientEquiv K H g, ?_⟩
    exact diagonalPair_restrictComponent_blockPerm_paired D H g

/-- The base kernels of a restricted component before and after pairing are
canonically equivalent. -/
def pairedComponentBaseKernelEquiv
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) :
    D.componentBaseKernel H ≃*
      D.diagonalPair.componentBaseKernel (pairedInternalSubgroup K H) where
  toFun g :=
    ⟨pairedRestrictedAmbientEquiv K H g.1, by
      change
        (D.diagonalPair.restrictComponent
          (pairedInternalSubgroup K H)).blockPerm
            (pairedRestrictedAmbientEquiv K H g.1) = 1
      rw [diagonalPair_restrictComponent_blockPerm_paired]
      exact g.2⟩
  invFun g :=
    ⟨(pairedRestrictedAmbientEquiv K H).symm g.1, by
      have hg :
          (D.diagonalPair.restrictComponent
            (pairedInternalSubgroup K H)).blockPerm g.1 = 1 :=
        g.2
      change (D.restrictComponent H).blockPerm
        ((pairedRestrictedAmbientEquiv K H).symm g.1) = 1
      rw [← diagonalPair_restrictComponent_blockPerm_paired D H
        ((pairedRestrictedAmbientEquiv K H).symm g.1)]
      simpa only [(pairedRestrictedAmbientEquiv K H).apply_symm_apply]
        using hg⟩
  left_inv g := by
    apply Subtype.ext
    exact (pairedRestrictedAmbientEquiv K H).symm_apply_apply g.1
  right_inv g := by
    apply Subtype.ext
    exact (pairedRestrictedAmbientEquiv K H).apply_symm_apply g.1
  map_mul' g h := by
    apply Subtype.ext
    exact (pairedRestrictedAmbientEquiv K H).map_mul g.1 h.1

@[simp]
theorem pairedComponentBaseKernelEquiv_coe
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (g : D.componentBaseKernel H) :
    ((((pairedComponentBaseKernelEquiv D H g).1 :
        restrictedAmbient (pairedInternalSubgroup K H)) :
      LinearMap.GeneralLinearGroup R (I → W × W))) =
        pairedGeneralLinearHom
          ((g.1 : restrictedAmbient H) :
            LinearMap.GeneralLinearGroup R (I → W)) :=
  pairedRestrictedAmbientEquiv_coe K H g.1

/-- The local block homomorphism on a paired base kernel is the diagonal
image of the original local block homomorphism. -/
@[simp]
theorem diagonalPair_componentBaseBlockLinearGL_paired
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K)
    (i : I) (g : D.componentBaseKernel H) :
    D.diagonalPair.componentBaseBlockLinearGL
        (pairedInternalSubgroup K H) i
        (pairedComponentBaseKernelEquiv D H g) =
      diagonalGeneralLinearHom R W
        (D.componentBaseBlockLinearGL H i g) := by
  change diagonalGeneralLinearHom R W
      (D.blockLinear
        ((pairedSubgroupEquiv K).symm
          (restrictedAmbientToCommon (pairedInternalSubgroup K H)
            (pairedRestrictedAmbientEquiv K H g.1))) i).1 =
    diagonalGeneralLinearHom R W
      (D.blockLinear (restrictedAmbientToCommon H g.1) i).1
  rw [pairedSubgroupEquiv_symm_restrictedAmbient]

/-- The component base image in a paired local block is exactly the diagonal
image of the original component base action. -/
theorem diagonalPair_componentBaseImageInCommonLocalGL
    (D : ImprimitiveLinearActionData K L) (H : Subgroup K) (i : I) :
    D.diagonalPair.componentBaseImageInCommonLocalGL
        (pairedInternalSubgroup K H) i =
      (D.componentBaseImageInCommonLocalGL H i).map
        (diagonalGeneralLinearHom R W) := by
  rw [componentBaseImageInCommonLocalGL_eq_componentBaseBlockImage,
    componentBaseImageInCommonLocalGL_eq_componentBaseBlockImage]
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    obtain ⟨h, rfl⟩ := (pairedComponentBaseKernelEquiv D H).surjective g
    apply Subgroup.mem_map.mpr
    refine ⟨D.componentBaseBlockLinearGL H i h, ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨h, rfl⟩
    · exact (diagonalPair_componentBaseBlockLinearGL_paired D H i h).symm
  · rintro ⟨x, ⟨g, rfl⟩, rfl⟩
    exact MonoidHom.mem_range.mpr
      ⟨pairedComponentBaseKernelEquiv D H g,
        diagonalPair_componentBaseBlockLinearGL_paired D H i g⟩

end ImprimitiveLinearActionData

/-! ## Stabilizer and translation transport -/

/-- A paired-image stabilizer is trivial exactly when the original action
has trivial common stabilizer on the two global vectors. -/
theorem stabilizer_map_pairedGeneralLinearHom_eq_bot_iff
    (A : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (v w : I → W) :
    MulAction.stabilizer
          (A.map (pairedGeneralLinearHom (R := R)))
          (piProdLinearEquiv (R := R) (v, w)) =
        ⊥ ↔
      MulAction.stabilizer A v ⊓
          MulAction.stabilizer A w =
        ⊥ := by
  let P := pairedGeneralLinearHom (I := I) (R := R) (W := W)
  constructor
  · intro hpaired
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    let pg : A.map P := ⟨P g.1, ⟨g.1, g.2, rfl⟩⟩
    have hpg :
        pg ∈ MulAction.stabilizer
          (A.map P) (piProdLinearEquiv (R := R) (v, w)) := by
      apply MulAction.mem_stabilizer_iff.mpr
      funext i
      change ((g.1 • v) i, (g.1 • w) i) = (v i, w i)
      apply Prod.ext
      · exact congrFun (MulAction.mem_stabilizer_iff.mp hg.1) i
      · exact congrFun (MulAction.mem_stabilizer_iff.mp hg.2) i
    rw [hpaired] at hpg
    have hpgOne : pg = 1 := Subgroup.mem_bot.mp hpg
    apply Subtype.ext
    apply pairedGeneralLinearHom_injective
    simpa only [P, pg, map_one] using congrArg Subtype.val hpgOne
  · intro hsource
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro pg hpg
    obtain ⟨g, hgA, hg⟩ := pg.2
    let ga : A := ⟨g, hgA⟩
    have hfix :
        P g • piProdLinearEquiv (R := R) (v, w) =
          piProdLinearEquiv (R := R) (v, w) := by
      rw [hg]
      exact MulAction.mem_stabilizer_iff.mp hpg
    have hv : ga • v = v := by
      funext i
      have hi := congrFun hfix i
      exact congrArg Prod.fst hi
    have hw : ga • w = w := by
      funext i
      have hi := congrFun hfix i
      exact congrArg Prod.snd hi
    have hga :
        ga ∈ MulAction.stabilizer A v ⊓
          MulAction.stabilizer A w :=
      ⟨MulAction.mem_stabilizer_iff.mpr hv,
        MulAction.mem_stabilizer_iff.mpr hw⟩
    have hgaOne : ga = 1 :=
      (Subgroup.eq_bot_iff_forall _).mp hsource ga hga
    apply Subtype.ext
    calc
      pg.1 = P g := hg.symm
      _ = P (1 : LinearMap.GeneralLinearGroup R (I → W)) := by
        congr 1
        exact congrArg Subtype.val hgaOne
      _ = 1 := P.map_one

/-- Specialized stabilizer transport for an internal component and its
paired concrete ambient image. -/
theorem stabilizer_pairedInternalSubgroup_eq_bot_iff
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : Subgroup K) (v w : I → W) :
    MulAction.stabilizer
          (ImprimitiveLinearActionData.restrictedAmbient
            (pairedInternalSubgroup K H))
          (piProdLinearEquiv (R := R) (v, w)) =
        ⊥ ↔
      MulAction.stabilizer
            (ImprimitiveLinearActionData.restrictedAmbient H) v ⊓
          MulAction.stabilizer
            (ImprimitiveLinearActionData.restrictedAmbient H) w =
        ⊥ := by
  change
    MulAction.stabilizer
        ((pairedInternalSubgroup K H).map (pairedSubgroup K).subtype)
        (piProdLinearEquiv (R := R) (v, w)) = ⊥ ↔
      MulAction.stabilizer (H.map K.subtype) v ⊓
        MulAction.stabilizer (H.map K.subtype) w = ⊥
  rw [pairedInternalSubgroup_map_subtype]
  exact stabilizer_map_pairedGeneralLinearHom_eq_bot_iff
    (H.map K.subtype) v w

/-- Addition of paired translations is coordinatewise under the pairing
equivalence. -/
theorem piProdLinearEquiv_pair_add
    (v w a b : I → W) :
    piProdLinearEquiv (R := R) (v + a, w + b) =
      piProdLinearEquiv (R := R) (v, w) +
        piProdLinearEquiv (R := R) (a, b) :=
  (piProdLinearEquiv (I := I) (R := R) (W := W)).map_add (v, w) (a, b)

/-- Action-level adapter: common regular translates for the paired concrete
component images give affine two-base translates for the original internal
components. -/
theorem exists_commonAffineTwoBaseTranslates_of_paired_commonRegularTranslates
    {J : Type*}
    (K : Subgroup (LinearMap.GeneralLinearGroup R (I → W)))
    (H : J → Subgroup K)
    (hregular :
      ∀ t : J → I → W × W,
        ∃ z : I → W × W, ∀ j,
          MulAction.stabilizer
              (ImprimitiveLinearActionData.restrictedAmbient
                (pairedInternalSubgroup K (H j)))
              (z + t j) =
            ⊥)
    (a b : J → I → W) :
    ∃ v w : I → W, ∀ j,
      MulAction.stabilizer
            (ImprimitiveLinearActionData.restrictedAmbient (H j))
            (v + a j) ⊓
          MulAction.stabilizer
            (ImprimitiveLinearActionData.restrictedAmbient (H j))
            (w + b j) =
        ⊥ := by
  obtain ⟨z, hz⟩ :=
    hregular (fun j ↦ piProdLinearEquiv (R := R) (a j, b j))
  let vw := (piProdLinearEquiv (I := I) (R := R) (W := W)).symm z
  refine ⟨vw.1, vw.2, fun j ↦ ?_⟩
  apply
    (stabilizer_pairedInternalSubgroup_eq_bot_iff
      K (H j) (vw.1 + a j) (vw.2 + b j)).mp
  have hpoint :
      piProdLinearEquiv (R := R) (vw.1 + a j, vw.2 + b j) =
        z + piProdLinearEquiv (R := R) (a j, b j) := by
    rw [piProdLinearEquiv_pair_add]
    change
      piProdLinearEquiv (R := R)
          ((piProdLinearEquiv (I := I) (R := R) (W := W)).symm z) +
        piProdLinearEquiv (R := R) (a j, b j) =
          z + piProdLinearEquiv (R := R) (a j, b j)
    rw [(piProdLinearEquiv (I := I) (R := R) (W := W)).apply_symm_apply]
  rw [hpoint]
  exact hz j

end LisiSabatini
