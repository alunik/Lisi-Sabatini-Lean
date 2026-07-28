module

public import LisiSabatini.PrimitiveSolvableTopCore
public import LisiSabatini.RegularAbelianTop
public import Mathlib.GroupTheory.PGroup

/-!
# Normal prime subgroups of primitive permutation groups

Let a finite group `G` act faithfully and primitively on a nonempty type
`Ω`, and let `H ⫳ G` be a nontrivial `p`-subgroup.  The center of `H` is
nontrivial because `H` is a finite `p`-group.  It is characteristic in `H`,
so its image in `G` is normal.  Primitivity and faithfulness make that image
transitive; since it is abelian, it is regular and self-centralizing.

Every element of `H` centralizes its center.  Self-centralization therefore
forces `H` to equal its center image.  Consequently `H` itself is abelian,
regular on `Ω`, and self-centralizing.  The final theorem packages its image
in `Equiv.Perm Ω` as a `IsRegularAbelianPermutationSubgroup`, hence in
particular as the semiregular top required by the single-marker imprimitive
reduction.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG uΩ

variable {G : Type uG} {Ω : Type uΩ}
variable [Group G] [MulAction G Ω]

namespace PrimitiveNormalPSubgroup

/-- The center of `H`, embedded back into the ambient group. -/
def centerImage (H : Subgroup G) : Subgroup G :=
  (Subgroup.center H).map H.subtype

/-- The ambient center image lies in the original subgroup. -/
theorem centerImage_le (H : Subgroup G) : centerImage H ≤ H := by
  exact Subgroup.map_subtype_le _

/-- The ambient image of a center is abelian. -/
theorem centerImage_isMulCommutative (H : Subgroup G) :
    IsMulCommutative (centerImage H) := by
  letI : IsMulCommutative (Subgroup.center H) :=
    Subgroup.center.isMulCommutative H
  exact Subgroup.map_isMulCommutative (Subgroup.center H) H.subtype

/-- The center image of a normal subgroup is normal in the ambient group. -/
theorem centerImage_normal (H : Subgroup G) (hHn : H.Normal) :
    (centerImage H).Normal := by
  letI : H.Normal := hHn
  exact ConjAct.normal_of_characteristic_of_normal

/-- A nontrivial finite `p`-group has nontrivial center image in the ambient
group. -/
theorem centerImage_ne_bot
    [Finite G] {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    centerImage H ≠ ⊥ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hH
  haveI : Nontrivial (Subgroup.center H) := hHp.center_nontrivial
  intro hcenter
  have hcenterBot : Subgroup.center H = ⊥ := by
    rw [← Subgroup.map_subtype_inj]
    simpa [centerImage] using hcenter
  exact (Subgroup.nontrivial_iff_ne_bot (Subgroup.center H)).mp
    inferInstance hcenterBot

/-- A subgroup centralizes the ambient image of its own center. -/
theorem le_centralizer_centerImage (H : Subgroup G) :
    H ≤ Subgroup.centralizer (centerImage H : Set G) := by
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  obtain ⟨z, hzCenter, rfl⟩ := Subgroup.mem_map.mp hz
  exact congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hzCenter ⟨h, hh⟩).symm

/-- A nontrivial normal `p`-subgroup of a finite faithful primitive
permutation group equals the ambient image of its center. -/
theorem eq_centerImage
    [Finite G] [Nonempty Ω] [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    H = centerImage H := by
  letI : H.Normal := hHn
  let Z : Subgroup G := centerImage H
  have hZn : Z.Normal := centerImage_normal H hHn
  letI : Z.Normal := hZn
  have hZne : Z ≠ ⊥ := centerImage_ne_bot hp H hHp hH
  have hZtrans : MulAction.IsPretransitive Z Ω :=
    PrimitiveSolvableTop.isPretransitive_of_normal_of_ne_bot hZne
  letI : MulAction.IsPretransitive Z Ω := hZtrans
  have hZcomm : IsMulCommutative Z := by
    exact centerImage_isMulCommutative H
  letI : IsMulCommutative Z := hZcomm
  have hZcentralizer : Subgroup.centralizer (Z : Set G) = Z :=
    PrimitiveSolvableTop.centralizer_eq_of_isMulCommutative_of_isPretransitive
      (Ω := Ω) Z
  apply le_antisymm
  · change H ≤ Z
    rw [← hZcentralizer]
    exact le_centralizer_centerImage H
  · exact centerImage_le H

/-- Such a normal `p`-subgroup is abelian. -/
theorem isMulCommutative
    [Finite G] [Nonempty Ω] [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    IsMulCommutative H := by
  rw [eq_centerImage (Ω := Ω) hp H hHn hHp hH]
  exact centerImage_isMulCommutative H

/-- Such a normal `p`-subgroup is transitive and semiregular, hence regular,
on the primitive permutation domain. -/
theorem isRegularSubgroupAction
    [Finite G] [Nonempty Ω] [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    IsRegularSubgroupAction H Ω := by
  letI : H.Normal := hHn
  have hcomm : IsMulCommutative H :=
    isMulCommutative (Ω := Ω) hp H hHn hHp hH
  letI : IsMulCommutative H := hcomm
  have htrans : MulAction.IsPretransitive H Ω :=
    PrimitiveSolvableTop.isPretransitive_of_normal_of_ne_bot hH
  letI : MulAction.IsPretransitive H Ω := htrans
  exact ⟨htrans,
    PrimitiveSolvableTop.isCancelSMul_of_isMulCommutative_of_isPretransitive H⟩

/-- In particular, every point stabilizer in `H` is trivial. -/
theorem stabilizer_eq_bot
    [Finite G] [Nonempty Ω] [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥)
    (ω : Ω) :
    MulAction.stabilizer H ω = ⊥ := by
  have hregular :=
    isRegularSubgroupAction (Ω := Ω) hp H hHn hHp hH
  letI : IsCancelSMul H Ω := hregular.2
  exact IsCancelSMul.stabilizer_eq_bot ω

/-- The faithful permutation image of `H`. -/
def permutationImage (H : Subgroup G) : Subgroup (Equiv.Perm Ω) :=
  H.map (MulAction.toPermHom G Ω)

/-- The permutation image of a nontrivial normal `p`-subgroup is a regular
abelian permutation subgroup.  Its `semiregular` field is the exact form
consumed by `SemiregularTop`. -/
theorem permutationImage_isRegularAbelian
    [Finite G] [Nonempty Ω] [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    IsRegularAbelianPermutationSubgroup (permutationImage (Ω := Ω) H) := by
  have hregular : IsRegularSubgroupAction H Ω :=
    isRegularSubgroupAction (Ω := Ω) hp H hHn hHp hH
  have hcomm : IsMulCommutative H :=
    isMulCommutative (Ω := Ω) hp H hHn hHp hH
  letI : IsMulCommutative H := hcomm
  let A : Subgroup (Equiv.Perm Ω) := permutationImage H
  have hAcomm : IsMulCommutative A := by
    dsimp [A, permutationImage]
    exact Subgroup.map_isMulCommutative H (MulAction.toPermHom G Ω)
  apply isRegularAbelianPermutationSubgroup_of_transitive_of_pairwiseCommute
  · intro x y
    obtain ⟨h, hh⟩ := hregular.1.exists_smul_eq x y
    let a : A :=
      ⟨MulAction.toPermHom G Ω h,
        Subgroup.mem_map.mpr ⟨h, h.property, rfl⟩⟩
    exact ⟨a, hh⟩
  · letI : IsMulCommutative A := hAcomm
    intro a b
    exact mul_comm a b

/-- The permutation image is semiregular at every point. -/
theorem permutationImage_isSemiregular
    [Finite G] [Nonempty Ω] [FaithfulSMul G Ω]
    [MulAction.IsPreprimitive G Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup G) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    IsSemiregularPermutationSubgroup (permutationImage (Ω := Ω) H) :=
  (permutationImage_isRegularAbelian hp H hHn hHp hH).semiregular

/-! ## Subgroups already realized as permutation groups -/

/-- For a subgroup `T ≤ Equiv.Perm Ω`, its action homomorphism is its
subtype inclusion. -/
theorem toPermHom_eq_subtype (T : Subgroup (Equiv.Perm Ω)) :
    MulAction.toPermHom T Ω = T.subtype := by
  ext t ω
  rfl

/-- Consequently the abstract faithful permutation image agrees with the
usual mapped subgroup inside `Equiv.Perm Ω`. -/
theorem permutationImage_eq_map_subtype
    (T : Subgroup (Equiv.Perm Ω)) (H : Subgroup T) :
    permutationImage (G := T) (Ω := Ω) H = H.map T.subtype := by
  rw [permutationImage, toPermHom_eq_subtype]

/-- Concrete permutation-top form: a nontrivial normal `p`-subgroup of a
finite primitive permutation subgroup is regular abelian. -/
theorem map_subtype_isRegularAbelian
    (T : Subgroup (Equiv.Perm Ω)) [Finite T] [Nonempty Ω]
    [MulAction.IsPreprimitive T Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup T) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    IsRegularAbelianPermutationSubgroup (H.map T.subtype) := by
  rw [← permutationImage_eq_map_subtype T H]
  exact permutationImage_isRegularAbelian
    (G := T) (Ω := Ω) hp H hHn hHp hH

/-- Concrete permutation-top form used by `SingleTopComponent`: the mapped
normal `p`-subgroup is semiregular at every block. -/
theorem map_subtype_isSemiregular
    (T : Subgroup (Equiv.Perm Ω)) [Finite T] [Nonempty Ω]
    [MulAction.IsPreprimitive T Ω]
    {p : ℕ} (hp : p.Prime)
    (H : Subgroup T) (hHn : H.Normal)
    (hHp : IsPGroup p H) (hH : H ≠ ⊥) :
    IsSemiregularPermutationSubgroup (H.map T.subtype) :=
  (map_subtype_isRegularAbelian T hp H hHn hHp hH).semiregular

end PrimitiveNormalPSubgroup

end LisiSabatini
