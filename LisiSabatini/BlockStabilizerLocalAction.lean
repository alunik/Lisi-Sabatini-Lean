module

public import LisiSabatini.ChiefActionStructuralDescent
public import LisiSabatini.PCore
public import LisiSabatini.ImprimitiveBundleAction
public import LisiSabatini.ImprimitiveBundleMarkerCore
public import Mathlib.GroupTheory.Solvable

/-!
# The local action of an imprimitive block stabilizer

The common-base action used by the recursive synchronization machinery is
the image of the kernel of the permutation action.  That image need not be
irreducible.  The natural irreducible local envelope is instead obtained by
taking the setwise stabilizer of one block and restricting its action to
that block.

This file constructs that local action intrinsically for a
`LinearImprimitivitySystem`, proves the elementary finite, solvable, and
odd-order inheritance statements, and places the base part of every normal
prime component inside it as a normal prime subgroup.  The construction is
also transported to the common `Fin e → ZMod r` coordinates of an internal
prime-field presentation.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uV uW

section AbstractLocalAction

variable {I : Type uI} {R : Type uR} {V : Type uV}
variable [Ring R] [AddCommGroup V] [Module R V]
variable [Fintype I] [DecidableEq I]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

namespace LinearImprimitivitySystem

/-! ## The block stabilizer and its faithful image -/

/-- The subgroup of the ambient linear group which fixes the chosen block
index, equivalently the setwise stabilizer of the corresponding submodule.
-/
def blockStabilizer
    (S : LinearImprimitivitySystem (I := I) K) (i : I) : Subgroup K :=
  (MulAction.stabilizer (Equiv.Perm I) i).comap S.blockPerm

@[simp]
theorem mem_blockStabilizer_iff
    (S : LinearImprimitivitySystem (I := I) K) (i : I) (g : K) :
    g ∈ S.blockStabilizer i ↔ S.blockPerm g i = i := by
  change S.blockPerm g ∈ MulAction.stabilizer (Equiv.Perm I) i ↔ _
  exact MulAction.mem_stabilizer_iff

/-- Restrict a block-stabilizing element to the chosen block submodule. -/
def blockStabilizerLocalHom
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    S.blockStabilizer i →*
      LinearMap.GeneralLinearGroup R (S.block i) where
  toFun g := LinearMap.GeneralLinearGroup.ofLinearEquiv
    (g.1.1.toLinearEquiv.ofSubmodules
      (S.block i) (S.block i) (by
        have hfix : S.blockPerm g.1 i = i :=
          (S.mem_blockStabilizer_iff i g.1).mp g.2
        simpa only [hfix] using S.map_block g.1 i))
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp

@[simp]
theorem blockStabilizerLocalHom_apply_coe
    (S : LinearImprimitivitySystem (I := I) K) (i : I)
    (g : S.blockStabilizer i) (x : S.block i) :
    ((S.blockStabilizerLocalHom i g :
        LinearMap.GeneralLinearGroup R (S.block i)) • x : S.block i) =
      ⟨g.1.1 • (x : V), by
        have hx := Submodule.mem_map_of_mem
          (f := (g.1.1.toLinearEquiv : V →ₗ[R] V)) x.2
        rw [S.map_block,
          (S.mem_blockStabilizer_iff i g.1).mp g.2] at hx
        exact hx⟩ := by
  apply Subtype.ext
  rfl

/-- The faithful concrete local linear group on the chosen block.  The
restriction homomorphism itself can have a kernel, but its range is a
subgroup of a general linear group and therefore acts faithfully. -/
def blockStabilizerLocalImage
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    Subgroup (LinearMap.GeneralLinearGroup R (S.block i)) :=
  (S.blockStabilizerLocalHom i).range

/-- The restriction map, corestricted onto the faithful local image. -/
abbrev blockStabilizerLocalRangeHom
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    S.blockStabilizer i →* S.blockStabilizerLocalImage i :=
  (S.blockStabilizerLocalHom i).rangeRestrict

/-- The local range map is onto by construction. -/
theorem blockStabilizerLocalRangeHom_surjective
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    Function.Surjective (S.blockStabilizerLocalRangeHom i) :=
  (S.blockStabilizerLocalHom i).rangeRestrict_surjective

/-! ## Normal prime components in the local image -/

/-- The part of `H` lying in the global permutation kernel, regarded as a
subgroup of the chosen block stabilizer.  This is exactly
`H ∩ ker(blockPerm)` with its ambient type changed to the block stabilizer.
-/
def componentBaseInBlockStabilizer
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (i : I) : Subgroup (S.blockStabilizer i) :=
  (H ⊓ S.blockPerm.ker).comap (S.blockStabilizer i).subtype

theorem componentBaseInBlockStabilizer_normal
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hH : H.Normal) (i : I) :
    (S.componentBaseInBlockStabilizer H i).Normal := by
  let : H.Normal := hH
  let : S.blockPerm.ker.Normal := S.blockPerm.normal_ker
  have hinter : (H ⊓ S.blockPerm.ker).Normal := inferInstance
  exact Subgroup.Normal.comap hinter (S.blockStabilizer i).subtype

theorem componentBaseInBlockStabilizer_isPGroup
    {p : ℕ}
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hH : IsPGroup p H) (i : I) :
    IsPGroup p (S.componentBaseInBlockStabilizer H i) := by
  intro g
  let h : H := ⟨g.1.1, g.2.1⟩
  obtain ⟨n, hn⟩ := hH h
  refine ⟨n, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  simpa [h] using congrArg Subtype.val hn

/-- The local image of `H ∩ ker(blockPerm)`, retained as an internal
subgroup of the faithful block-stabilizer image. -/
def componentBaseImageInBlockStabilizerLocal
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (i : I) :
    Subgroup (S.blockStabilizerLocalImage i) :=
  (S.componentBaseInBlockStabilizer H i).map
    (S.blockStabilizerLocalRangeHom i)

/-- Intrinsic base images of normal components are normal in the full local
block-stabilizer image. -/
theorem componentBaseImageInBlockStabilizerLocal_normal
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hH : H.Normal) (i : I) :
    (S.componentBaseImageInBlockStabilizerLocal H i).Normal := by
  exact Subgroup.Normal.map
    (S.componentBaseInBlockStabilizer_normal H hH i)
    (S.blockStabilizerLocalRangeHom i)
    (S.blockStabilizerLocalRangeHom_surjective i)

/-- Intrinsic base images retain their prime-group label in the full local
block-stabilizer image. -/
theorem componentBaseImageInBlockStabilizerLocal_isPGroup
    {p : ℕ}
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hH : IsPGroup p H) (i : I) :
    IsPGroup p (S.componentBaseImageInBlockStabilizerLocal H i) :=
  (S.componentBaseInBlockStabilizer_isPGroup H hH i).map
    (S.blockStabilizerLocalRangeHom i)

/-- Hence every intrinsic normal `p`-component lies in the `p`-core of the
faithful local block-stabilizer image. -/
theorem componentBaseImageInBlockStabilizerLocal_le_pCore
    {p : ℕ}
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hHn : H.Normal) (hHp : IsPGroup p H) (i : I) :
    S.componentBaseImageInBlockStabilizerLocal H i ≤
      pCore p (S.blockStabilizerLocalImage i) :=
  le_pCore
    (S.componentBaseImageInBlockStabilizerLocal_isPGroup H hHp i)
    (S.componentBaseImageInBlockStabilizerLocal_normal H hHn i)

/-! ## Finite, solvable, and odd-order inheritance -/

theorem blockStabilizerLocalImage_finite
    [Finite K]
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    Finite (S.blockStabilizerLocalImage i) := by
  let : Finite (S.blockStabilizer i) := inferInstance
  exact Finite.of_surjective (S.blockStabilizerLocalRangeHom i)
    (S.blockStabilizerLocalRangeHom_surjective i)

theorem blockStabilizerLocalImage_isSolvable
    [Group.IsSolvable K]
    (S : LinearImprimitivitySystem (I := I) K) (i : I) :
    Group.IsSolvable (S.blockStabilizerLocalImage i) := by
  let : Group.IsSolvable (S.blockStabilizer i) := inferInstance
  exact Group.isSolvable_of_surjective (S.blockStabilizerLocalRangeHom_surjective i)

theorem blockStabilizerLocalImage_odd
    [Finite K]
    (S : LinearImprimitivitySystem (I := I) K) (i : I)
    (hodd : Odd (Nat.card K)) :
    Odd (Nat.card (S.blockStabilizerLocalImage i)) := by
  let : Finite (S.blockStabilizer i) := inferInstance
  let : Finite (S.blockStabilizerLocalImage i) :=
    S.blockStabilizerLocalImage_finite i
  exact hodd.of_dvd_nat <|
    (Subgroup.card_range_dvd (S.blockStabilizerLocalHom i)).trans
      (S.blockStabilizer i).card_subgroup_dvd_card

/-! ## Inducing a local invariant submodule to the ambient module -/

/-- A chosen transporter from block `i` to block `j`.  The identity is used
at the distinguished block itself. -/
def blockTransporter
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i j : I) : K := by
  classical
  exact if h : j = i then 1 else
    Classical.choose (S.isIndexPretransitive_of_irreducible hirr i j)

@[simp]
theorem blockTransporter_self
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I) :
    S.blockTransporter hirr i i = 1 := by
  simp [blockTransporter]

theorem blockTransporter_maps
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i j : I) :
    S.blockPerm (S.blockTransporter hirr i j) i = j := by
  classical
  by_cases h : j = i
  · subst j
    simp
  · simpa [blockTransporter, h] using
      Classical.choose_spec
        (S.isIndexPretransitive_of_irreducible hirr i j)

/-- A submodule of the block subtype, viewed as an ambient submodule. -/
def localSubmoduleAmbient
    (S : LinearImprimitivitySystem (I := I) K) (i : I)
    (U : Submodule R (S.block i)) : Submodule R V :=
  U.map (S.block i).subtype

theorem localSubmoduleAmbient_le_block
    (S : LinearImprimitivitySystem (I := I) K) (i : I)
    (U : Submodule R (S.block i)) :
    S.localSubmoduleAmbient i U ≤ S.block i := by
  rintro _ ⟨x, hx, rfl⟩
  exact x.2

/-- Transport one local submodule from the distinguished block to every
block in the transitive system. -/
def transportedLocalSubmodule
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i)) (j : I) : Submodule R V :=
  (S.localSubmoduleAmbient i U).map
    ((S.blockTransporter hirr i j).1.toLinearEquiv : V →ₗ[R] V)

@[simp]
theorem transportedLocalSubmodule_self
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i)) :
    S.transportedLocalSubmodule hirr i U i =
      S.localSubmoduleAmbient i U := by
  rw [transportedLocalSubmodule, S.blockTransporter_self]
  exact Submodule.map_id _

theorem transportedLocalSubmodule_le_block
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i)) (j : I) :
    S.transportedLocalSubmodule hirr i U j ≤ S.block j := by
  calc
    S.transportedLocalSubmodule hirr i U j ≤
        (S.block i).map
          ((S.blockTransporter hirr i j).1.toLinearEquiv : V →ₗ[R] V) :=
      Submodule.map_mono (S.localSubmoduleAmbient_le_block i U)
    _ = S.block j := by
      rw [S.map_block, S.blockTransporter_maps hirr i j]

/-- A local invariant submodule, embedded in the ambient chosen block, is
preserved by every element of the block stabilizer. -/
theorem localSubmoduleAmbient_invariant
    (S : LinearImprimitivitySystem (I := I) K) (i : I)
    (U : Submodule R (S.block i))
    (hU : ∀ g : S.blockStabilizerLocalImage i, ∀ x ∈ U,
      (g.1 : LinearMap.GeneralLinearGroup R (S.block i)) • x ∈ U)
    (a : S.blockStabilizer i) :
    (S.localSubmoduleAmbient i U).map
        (a.1.1.toLinearEquiv : V →ₗ[R] V) ≤
      S.localSubmoduleAmbient i U := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  let g : S.blockStabilizerLocalImage i :=
    ⟨S.blockStabilizerLocalHom i a, ⟨a, rfl⟩⟩
  have hgx : (g.1 : LinearMap.GeneralLinearGroup R (S.block i)) • x ∈ U :=
    hU g x hx
  refine ⟨(g.1 : LinearMap.GeneralLinearGroup R (S.block i)) • x,
    hgx, ?_⟩
  exact congrArg Subtype.val (S.blockStabilizerLocalHom_apply_coe i a x)

/-- The sum of all transported copies of one local submodule. -/
def inducedLocalSubmodule
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i)) : Submodule R V :=
  ⨆ j, S.transportedLocalSubmodule hirr i U j

/-- Ambient transport by any element sends the copy over block `j` into
the chosen copy over the image block.  The comparison element between the
two chosen transporters belongs to the distinguished block stabilizer, so
the local invariance hypothesis applies to it. -/
theorem map_transportedLocalSubmodule_le
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i))
    (hU : ∀ g : S.blockStabilizerLocalImage i, ∀ x ∈ U,
      (g.1 : LinearMap.GeneralLinearGroup R (S.block i)) • x ∈ U)
    (h : K) (j : I) :
    (S.transportedLocalSubmodule hirr i U j).map
        (h.1.toLinearEquiv : V →ₗ[R] V) ≤
      S.transportedLocalSubmodule hirr i U (S.blockPerm h j) := by
  let tj : K := S.blockTransporter hirr i j
  let k : I := S.blockPerm h j
  let tk : K := S.blockTransporter hirr i k
  let aK : K := tk⁻¹ * h * tj
  have haFix : S.blockPerm aK i = i := by
    dsimp only [aK]
    simp only [map_mul, map_inv, Equiv.Perm.mul_apply]
    change (S.blockPerm tk).symm (S.blockPerm h (S.blockPerm tj i)) = i
    rw [show S.blockPerm tj i = j by
      exact S.blockTransporter_maps hirr i j]
    change (S.blockPerm tk).symm k = i
    rw [← S.blockTransporter_maps hirr i k]
    exact Equiv.symm_apply_apply _ _
  let a : S.blockStabilizer i := ⟨aK,
    (S.mem_blockStabilizer_iff i aK).mpr haFix⟩
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hax : aK.1 • x ∈ S.localSubmoduleAmbient i U :=
    S.localSubmoduleAmbient_invariant i U hU a
      (Submodule.mem_map_of_mem hx)
  refine ⟨aK.1 • x, hax, ?_⟩
  change tk.1 • (aK.1 • x) = h.1 • (tj.1 • x)
  simp [aK, mul_smul]

/-- The induced sum of the transported local submodules is invariant under
the entire ambient imprimitive group. -/
theorem inducedLocalSubmodule_invariant
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i))
    (hU : ∀ g : S.blockStabilizerLocalImage i, ∀ x ∈ U,
      (g.1 : LinearMap.GeneralLinearGroup R (S.block i)) • x ∈ U) :
    ∀ h : K, ∀ v ∈ S.inducedLocalSubmodule hirr i U,
      h.1 • v ∈ S.inducedLocalSubmodule hirr i U := by
  intro h v hv
  have hmap : (S.inducedLocalSubmodule hirr i U).map
      (h.1.toLinearEquiv : V →ₗ[R] V) ≤
        S.inducedLocalSubmodule hirr i U := by
    rw [inducedLocalSubmodule, Submodule.map_iSup]
    refine iSup_le fun j ↦ ?_
    exact (S.map_transportedLocalSubmodule_le hirr i U hU h j).trans
      (le_iSup (fun k ↦ S.transportedLocalSubmodule hirr i U k)
        (S.blockPerm h j))
  exact hmap (Submodule.mem_map_of_mem hv)

/-- If the induced ambient sum is zero, then the original local submodule
is zero. -/
theorem localSubmodule_eq_bot_of_induced_eq_bot
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i))
    (hbot : S.inducedLocalSubmodule hirr i U = ⊥) :
    U = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hlocal : (x : V) ∈
        S.transportedLocalSubmodule hirr i U i := by
      rw [S.transportedLocalSubmodule_self]
      exact ⟨x, hx, rfl⟩
    have hind : (x : V) ∈ S.inducedLocalSubmodule hirr i U :=
      (le_iSup
        (fun j ↦ S.transportedLocalSubmodule hirr i U j) i) hlocal
    rw [hbot] at hind
    have hxzero : (x : V) = 0 := by simpa using hind
    exact Subtype.ext hxzero
  · exact bot_le

/-- If the transported copies span the whole ambient module, independence
of the original block system forces every transported copy to equal its
whole block; in particular the original local submodule is the whole chosen
block. -/
theorem localSubmodule_eq_top_of_induced_eq_top
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (U : Submodule R (S.block i))
    (htop : S.inducedLocalSubmodule hirr i U = ⊤) :
    U = ⊤ := by
  have hle :
      (fun j ↦ S.transportedLocalSubmodule hirr i U j) ≤ S.block :=
    fun j ↦ S.transportedLocalSubmodule_le_block hirr i U j
  have heq :
      (fun j ↦ S.transportedLocalSubmodule hirr i U j) = S.block :=
    (S.iSupIndep_block.le_iff_eq_of_iSup_eq_top htop).mp hle
  have hlocalTop : S.localSubmoduleAmbient i U = S.block i := by
    rw [← S.transportedLocalSubmodule_self hirr i U]
    exact congrFun heq i
  apply top_unique
  intro x _hx
  have hxambient : (x : V) ∈ S.localSubmoduleAmbient i U := by
    rw [hlocalTop]
    exact x.2
  obtain ⟨u, hu, hux⟩ := hxambient
  have hueq : u = x := Subtype.ext hux
  rw [← hueq]
  exact hu

/-- **The block-stabilizer local image is irreducible.**

A local invariant submodule is transported to every block.  The sum of
those copies is invariant under the ambient group, hence is zero or the
whole module.  The zero case forces the local submodule to vanish; in the
whole-module case independence of the original block decomposition forces
it to equal the entire chosen block. -/
theorem blockStabilizerLocalImage_isIrreducible
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I) :
    IsIrreducible (S.blockStabilizerLocalImage i) := by
  intro U hU
  let T := S.inducedLocalSubmodule hirr i U
  have hTinv : ∀ h : K, ∀ v ∈ T, h.1 • v ∈ T :=
    S.inducedLocalSubmodule_invariant hirr i U hU
  rcases hirr T hTinv with hbot | htop
  · exact Or.inl (S.localSubmodule_eq_bot_of_induced_eq_bot
      hirr i U hbot)
  · exact Or.inr (S.localSubmodule_eq_top_of_induced_eq_top
      hirr i U htop)

/-! ## Transport to common local coordinates -/

variable {W : Type uW} [AddCommGroup W] [Module R W]

@[simp]
theorem congrLinearEquiv_smul
    (e : V ≃ₗ[R] W)
    (g : LinearMap.GeneralLinearGroup R V) (v : V) :
    LinearMap.GeneralLinearGroup.congrLinearEquiv e g • e v =
      e (g • v) := by
  change e (g.toLinearEquiv (e.symm (e v))) =
    e (g.toLinearEquiv v)
  rw [e.symm_apply_apply]

/-- Irreducibility is preserved when a concrete linear group is conjugated
through a linear equivalence. -/
theorem isIrreducible_map_conjugation
    (A : Subgroup (LinearMap.GeneralLinearGroup R V))
    (e : V ≃ₗ[R] W) (hA : IsIrreducible A) :
    IsIrreducible
      (A.map
        (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom) := by
  intro U hU
  let U' : Submodule R V := U.comap e.toLinearMap
  have hU'inv : ∀ a : A, ∀ x ∈ U',
      (a.1 : LinearMap.GeneralLinearGroup R V) • x ∈ U' := by
    intro a x hx
    let ae : A.map
        (LinearMap.GeneralLinearGroup.congrLinearEquiv e).toMonoidHom :=
      ⟨LinearMap.GeneralLinearGroup.congrLinearEquiv e a.1,
        Subgroup.mem_map.mpr ⟨a.1, a.2, rfl⟩⟩
    have hae := hU ae (e x) hx
    change
      LinearMap.GeneralLinearGroup.congrLinearEquiv e a.1 • e x ∈ U
      at hae
    rw [congrLinearEquiv_smul] at hae
    exact hae
  rcases hA U' hU'inv with hbot | htop
  · left
    apply le_antisymm
    · intro y hy
      let x : V := e.symm y
      have hx : x ∈ U' := by
        change e x ∈ U
        simpa [x] using hy
      rw [hbot] at hx
      have hxzero : x = 0 := by simpa using hx
      have hyzero : y = 0 := by
        rw [← e.apply_symm_apply y, show e.symm y = x from rfl, hxzero]
        simp
      exact hyzero
    · exact bot_le
  · right
    apply top_unique
    intro y _hy
    let x : V := e.symm y
    have hx : x ∈ U' := by
      rw [htop]
      trivial
    change e x ∈ U at hx
    simpa [x] using hx

/-- The faithful block-stabilizer image written in any chosen coordinate
model for the block. -/
def blockStabilizerCoordinateLocalImage
    (S : LinearImprimitivitySystem (I := I) K) (i : I)
    (c : S.block i ≃ₗ[R] W) :
    Subgroup (LinearMap.GeneralLinearGroup R W) :=
  (S.blockStabilizerLocalImage i).map
    (LinearMap.GeneralLinearGroup.congrLinearEquiv c).toMonoidHom

/-- The intrinsic and coordinated local images are canonically isomorphic.
-/
def blockStabilizerLocalImageCoordinateEquiv
    (S : LinearImprimitivitySystem (I := I) K) (i : I)
    (c : S.block i ≃ₗ[R] W) :
    S.blockStabilizerLocalImage i ≃*
      S.blockStabilizerCoordinateLocalImage i c :=
  Subgroup.equivMapOfInjective (S.blockStabilizerLocalImage i)
    (LinearMap.GeneralLinearGroup.congrLinearEquiv c).toMonoidHom
    (LinearMap.GeneralLinearGroup.congrLinearEquiv c).injective

/-- The coordinated block-stabilizer image is irreducible. -/
theorem blockStabilizerCoordinateLocalImage_isIrreducible
    (S : LinearImprimitivitySystem (I := I) K)
    (hirr : IsIrreducible K) (i : I)
    (c : S.block i ≃ₗ[R] W) :
    IsIrreducible (S.blockStabilizerCoordinateLocalImage i c) :=
  isIrreducible_map_conjugation
    (S.blockStabilizerLocalImage i) c
    (S.blockStabilizerLocalImage_isIrreducible hirr i)

/-- A normal component base image transported into common local
coordinates. -/
def componentBaseImageInBlockStabilizerCoordinates
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (i : I) (c : S.block i ≃ₗ[R] W) :
    Subgroup (S.blockStabilizerCoordinateLocalImage i c) :=
  (S.componentBaseImageInBlockStabilizerLocal H i).map
    (S.blockStabilizerLocalImageCoordinateEquiv i c).toMonoidHom

theorem componentBaseImageInBlockStabilizerCoordinates_normal
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hH : H.Normal) (i : I)
    (c : S.block i ≃ₗ[R] W) :
    (S.componentBaseImageInBlockStabilizerCoordinates H i c).Normal := by
  exact Subgroup.Normal.map
    (S.componentBaseImageInBlockStabilizerLocal_normal H hH i)
    (S.blockStabilizerLocalImageCoordinateEquiv i c).toMonoidHom
    (S.blockStabilizerLocalImageCoordinateEquiv i c).surjective

theorem componentBaseImageInBlockStabilizerCoordinates_isPGroup
    {p : ℕ}
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hH : IsPGroup p H) (i : I)
    (c : S.block i ≃ₗ[R] W) :
    IsPGroup p
      (S.componentBaseImageInBlockStabilizerCoordinates H i c) :=
  (S.componentBaseImageInBlockStabilizerLocal_isPGroup H hH i).map
    (S.blockStabilizerLocalImageCoordinateEquiv i c).toMonoidHom

theorem componentBaseImageInBlockStabilizerCoordinates_le_pCore
    {p : ℕ}
    (S : LinearImprimitivitySystem (I := I) K)
    (H : Subgroup K) (hHn : H.Normal) (hHp : IsPGroup p H)
    (i : I) (c : S.block i ≃ₗ[R] W) :
    S.componentBaseImageInBlockStabilizerCoordinates H i c ≤
      pCore p (S.blockStabilizerCoordinateLocalImage i c) :=
  le_pCore
    (S.componentBaseImageInBlockStabilizerCoordinates_isPGroup H hHp i c)
    (S.componentBaseImageInBlockStabilizerCoordinates_normal H hHn i c)

/-! ## Exact comparison with the common-base action -/

/-- Transporting an `ofSubmodules` restriction through coordinates is
unchanged when its target block index is identified with its source index.
This isolates the dependent block-index transport in the comparison with
the coordinate imprimitive action. -/
theorem coordinateOfSubmodules_eq_of_eq
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W)
    (a : LinearMap.GeneralLinearGroup R V) (i j : I)
    (hmap : (S.block i).map
      (a.toLinearEquiv : V →ₗ[R] V) = S.block j)
    (hji : j = i)
    (hfix : (S.block i).map
      (a.toLinearEquiv : V →ₗ[R] V) = S.block i) :
    LinearMap.GeneralLinearGroup.ofLinearEquiv
      ((c i).symm |>.trans
        (a.toLinearEquiv.ofSubmodules
          (S.block i) (S.block j) hmap) |>.trans (c j)) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv (c i)
        (LinearMap.GeneralLinearGroup.ofLinearEquiv
          (a.toLinearEquiv.ofSubmodules
            (S.block i) (S.block i) hfix)) := by
  subst j
  rfl

/-- On an element of the global block-permutation kernel, the block factor
of the extracted coordinate imprimitive action is exactly the conjugate of
the intrinsic restriction to the chosen block. -/
theorem coordinateBlockLinear_eq_blockStabilizerLocalHom
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (i : I)
    (g : S.blockStabilizer i) (hg : S.blockPerm g.1 = 1) :
    (((S.imprimitiveLinearActionData c).blockLinear
      (S.coordinateSubgroupEquiv c g.1) i :
        (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W))) :
      LinearMap.GeneralLinearGroup R W) =
      LinearMap.GeneralLinearGroup.congrLinearEquiv (c i)
        (S.blockStabilizerLocalHom i g) := by
  change LinearMap.GeneralLinearGroup.ofLinearEquiv
      (S.targetLocalEquiv c
        ((S.coordinateSubgroupEquiv c).symm
          (S.coordinateSubgroupEquiv c g.1)) i) = _
  rw [(S.coordinateSubgroupEquiv c).symm_apply_apply]
  have htarget : S.targetLocalEquiv c g.1 i =
      S.sourceLocalEquiv c g.1 i := by
    rw [targetLocalEquiv, hg]
    rfl
  rw [htarget]
  have hgi : S.blockPerm g.1 i = i := by
    rw [hg]
    rfl
  change LinearMap.GeneralLinearGroup.ofLinearEquiv
      (S.sourceLocalEquiv c g.1 i) =
    LinearMap.GeneralLinearGroup.congrLinearEquiv (c i)
      (S.blockStabilizerLocalHom i g)
  unfold sourceLocalEquiv blockStabilizerLocalHom
  exact S.coordinateOfSubmodules_eq_of_eq c g.1.1 i
    (S.blockPerm g.1 i) (S.map_block g.1 i) hgi _

/-- An internal subgroup of the original action transported into the
canonical common-block coordinate action. -/
def coordinateInternalSubgroup
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (H : Subgroup K) :
    Subgroup (S.coordinateSubgroup c) :=
  H.map (S.coordinateSubgroupEquiv c).toMonoidHom

/-- Pull an internal subgroup of the coordinate action back to the original
action. -/
def coordinateInternalSubgroupPreimage
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W)
    (H : Subgroup (S.coordinateSubgroup c)) : Subgroup K :=
  H.comap (S.coordinateSubgroupEquiv c).toMonoidHom

/-- Coordinate transport recovers every subgroup after pulling it back
through the coordinate equivalence. -/
theorem coordinateInternalSubgroup_preimage
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W)
    (H : Subgroup (S.coordinateSubgroup c)) :
    S.coordinateInternalSubgroup c
        (S.coordinateInternalSubgroupPreimage c H) = H := by
  rw [coordinateInternalSubgroup,
    coordinateInternalSubgroupPreimage, Subgroup.map_comap_eq,
    (S.coordinateSubgroupEquiv c).toMonoidHom.range_eq_top_of_surjective
      (S.coordinateSubgroupEquiv c).surjective, top_inf_eq]

/-- The mapped intrinsic component image is exactly the existing concrete
common-local component image for the transported coordinate subgroup. -/
theorem map_componentBaseImageInBlockStabilizerCoordinates_eq_commonLocalGL
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W) (H : Subgroup K) (i : I) :
    (S.componentBaseImageInBlockStabilizerCoordinates H i (c i)).map
        (S.blockStabilizerCoordinateLocalImage i (c i)).subtype =
      (S.imprimitiveLinearActionData c).componentBaseImageInCommonLocalGL
        (S.coordinateInternalSubgroup c H) i := by
  rw [(S.imprimitiveLinearActionData c)
    |>.componentBaseImageInCommonLocalGL_eq_componentBaseBlockImage]
  ext x
  constructor
  · intro hx
    obtain ⟨xc, hxc, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨xl, hxl, hxlc⟩ := Subgroup.mem_map.mp hxc
    obtain ⟨a, ha, hal⟩ := Subgroup.mem_map.mp hxl
    let gc : S.coordinateSubgroup c := S.coordinateSubgroupEquiv c a.1
    have hgcH : gc ∈ S.coordinateInternalSubgroup c H :=
      Subgroup.mem_map.mpr ⟨a.1, ha.1, rfl⟩
    let ga : ImprimitiveLinearActionData.restrictedAmbient
        (S.coordinateInternalSubgroup c H) :=
      ⟨gc.1, Subgroup.mem_map.mpr ⟨gc, hgcH, rfl⟩⟩
    have hgker : (S.imprimitiveLinearActionData c).blockPerm
        (ImprimitiveLinearActionData.restrictedAmbientToCommon
          (S.coordinateInternalSubgroup c H) ga) = 1 := by
      change S.blockPerm
        ((S.coordinateSubgroupEquiv c).symm
          (S.coordinateSubgroupEquiv c a.1)) = 1
      rw [(S.coordinateSubgroupEquiv c).symm_apply_apply]
      exact ha.2
    let b : (S.imprimitiveLinearActionData c).componentBaseKernel
        (S.coordinateInternalSubgroup c H) := ⟨ga, hgker⟩
    apply MonoidHom.mem_range.mpr
    refine ⟨b, ?_⟩
    rw [← hxlc, ← hal]
    exact S.coordinateBlockLinear_eq_blockStabilizerLocalHom c i a ha.2
  · intro hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
    obtain ⟨gc, hgcH, hgcval⟩ := Subgroup.mem_map.mp b.1.2
    have hcommon :
        ImprimitiveLinearActionData.restrictedAmbientToCommon
          (S.coordinateInternalSubgroup c H) b.1 = gc := by
      apply Subtype.ext
      exact hgcval.symm
    obtain ⟨g, hgH, hgval⟩ := Subgroup.mem_map.mp hgcH
    have hgker : S.blockPerm g = 1 := by
      have hb := b.2
      change (S.imprimitiveLinearActionData c).blockPerm
        (ImprimitiveLinearActionData.restrictedAmbientToCommon
          (S.coordinateInternalSubgroup c H) b.1) = 1 at hb
      rw [hcommon, ← hgval] at hb
      change S.blockPerm
        ((S.coordinateSubgroupEquiv c).symm
          (S.coordinateSubgroupEquiv c g)) = 1 at hb
      simpa using hb
    let a : S.blockStabilizer i :=
      ⟨g, (S.mem_blockStabilizer_iff i g).mpr (by simp [hgker])⟩
    have ha : a ∈ S.componentBaseInBlockStabilizer H i :=
      ⟨hgH, hgker⟩
    apply Subgroup.mem_map.mpr
    let xl : S.blockStabilizerLocalImage i :=
      S.blockStabilizerLocalRangeHom i a
    let xc : S.blockStabilizerCoordinateLocalImage i (c i) :=
      S.blockStabilizerLocalImageCoordinateEquiv i (c i) xl
    refine ⟨xc, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr
        ⟨xl, Subgroup.mem_map.mpr ⟨a, ha, rfl⟩, rfl⟩
    · change LinearMap.GeneralLinearGroup.congrLinearEquiv (c i)
          (S.blockStabilizerLocalHom i a) =
        (S.imprimitiveLinearActionData c).componentBaseBlockLinearGL
          (S.coordinateInternalSubgroup c H) i b
      symm
      change (((S.imprimitiveLinearActionData c).blockLinear
        (ImprimitiveLinearActionData.restrictedAmbientToCommon
          (S.coordinateInternalSubgroup c H) b.1) i :
          (⊤ : Subgroup (LinearMap.GeneralLinearGroup R W))) :
          LinearMap.GeneralLinearGroup R W) = _
      rw [hcommon, ← hgval]
      exact S.coordinateBlockLinear_eq_blockStabilizerLocalHom c i a hgker

/-- Exact arbitrary-coordinate-component form of the preceding comparison.
This is the adapter used by the recursive NCAS layer: its existing subgroup
`H` is pulled back to the intrinsic action and mapped into the irreducible
block-stabilizer local envelope without changing its ambient linear image. -/
theorem map_componentBaseImageInBlockStabilizerCoordinates_preimage_eq_commonLocalGL
    (S : LinearImprimitivitySystem (I := I) K)
    (c : ∀ i, S.block i ≃ₗ[R] W)
    (H : Subgroup (S.coordinateSubgroup c)) (i : I) :
    (S.componentBaseImageInBlockStabilizerCoordinates
        (S.coordinateInternalSubgroupPreimage c H) i (c i)).map
        (S.blockStabilizerCoordinateLocalImage i (c i)).subtype =
      (S.imprimitiveLinearActionData c).componentBaseImageInCommonLocalGL
        H i := by
  rw [S.map_componentBaseImageInBlockStabilizerCoordinates_eq_commonLocalGL,
    S.coordinateInternalSubgroup_preimage]

end LinearImprimitivitySystem

end AbstractLocalAction

/-! ## Prime-field internal presentations -/

namespace PrimeFieldPrimitiveInternalImprimitivityPresentation

variable {r b e : ℕ}
variable [AddCommGroup V] [Module (ZMod r) V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}

/-- The faithful irreducible local envelope at one presented block, in the
common `Fin e → ZMod r` coordinates. -/
abbrev blockStabilizerLocalAction
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (i : Fin b) :
    Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin e → ZMod r)) :=
  P.system.blockStabilizerCoordinateLocalImage i (P.localCoordinates i)

/-- The image of `H ∩ ker(blockPerm)` inside the faithful coordinated local
envelope. -/
abbrev componentBaseInBlockStabilizerLocalAction
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup K) (i : Fin b) :
    Subgroup (P.blockStabilizerLocalAction i) :=
  P.system.componentBaseImageInBlockStabilizerCoordinates H i
    (P.localCoordinates i)

/-- Pull a subgroup of the canonical coordinate action back through the
presentation's global coordinate equivalence. -/
abbrev blockActionComponentPreimage
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) : Subgroup K :=
  P.system.coordinateInternalSubgroupPreimage P.localCoordinates H

/-- The component base subgroup in the irreducible local envelope, starting
from the coordinate-action subgroup used by the recursive NCAS layer. -/
abbrev componentBaseInBlockStabilizerLocalActionOfBlockAction
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) (i : Fin b) :
    Subgroup (P.blockStabilizerLocalAction i) :=
  P.componentBaseInBlockStabilizerLocalAction
    (P.blockActionComponentPreimage H) i

/-- **Exact recursive-NCAS adapter.** Mapping the intrinsic component from
the irreducible block-stabilizer envelope into the ambient local general
linear group gives exactly the existing common-local component image. -/
theorem map_componentBaseInBlockStabilizerLocalActionOfBlockAction_subtype_eq_commonLocalGL
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) (i : Fin b) :
    (P.componentBaseInBlockStabilizerLocalActionOfBlockAction H i).map
        (P.blockStabilizerLocalAction i).subtype =
      P.imprimitiveLinearActionData.componentBaseImageInCommonLocalGL H i :=
  P.system
    |>.map_componentBaseImageInBlockStabilizerCoordinates_preimage_eq_commonLocalGL
      P.localCoordinates H i

/-- Each presented block-stabilizer local action is irreducible. -/
theorem blockStabilizerLocalAction_irreducible
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (i : Fin b) :
    LinearImprimitivitySystem.IsIrreducible
      (P.blockStabilizerLocalAction i) :=
  P.system.blockStabilizerCoordinateLocalImage_isIrreducible
    P.irreducible i (P.localCoordinates i)

/-- Finiteness descends from the presented ambient action. -/
theorem blockStabilizerLocalAction_finite
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (i : Fin b) :
    Finite (P.blockStabilizerLocalAction i) := by
  let : Finite K := P.finite_action
  let : Finite (P.system.blockStabilizerLocalImage i) :=
    P.system.blockStabilizerLocalImage_finite i
  exact Finite.of_surjective
    (P.system.blockStabilizerLocalImageCoordinateEquiv i
      (P.localCoordinates i))
    (P.system.blockStabilizerLocalImageCoordinateEquiv i
      (P.localCoordinates i)).surjective

/-- Solvability descends from the presented ambient action. -/
theorem blockStabilizerLocalAction_isSolvable
    [Group.IsSolvable K]
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (i : Fin b) :
    Group.IsSolvable (P.blockStabilizerLocalAction i) := by
  let : Group.IsSolvable (P.system.blockStabilizerLocalImage i) :=
    P.system.blockStabilizerLocalImage_isSolvable i
  exact Group.isSolvable_of_surjective
    (f := (P.system.blockStabilizerLocalImageCoordinateEquiv i
      (P.localCoordinates i)).toMonoidHom)
    (P.system.blockStabilizerLocalImageCoordinateEquiv i
      (P.localCoordinates i)).surjective

/-- Odd order descends from the presented ambient action. -/
theorem blockStabilizerLocalAction_odd
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (i : Fin b)
    (hodd : Odd (Nat.card K)) :
    Odd (Nat.card (P.blockStabilizerLocalAction i)) := by
  let : Finite K := P.finite_action
  let : Finite (P.system.blockStabilizerLocalImage i) :=
    P.system.blockStabilizerLocalImage_finite i
  let : Finite (P.blockStabilizerLocalAction i) :=
    P.blockStabilizerLocalAction_finite i
  rw [Nat.card_congr
    (P.system.blockStabilizerLocalImageCoordinateEquiv i
      (P.localCoordinates i)).symm.toEquiv]
  exact P.system.blockStabilizerLocalImage_odd i hodd

/-- Normality of every component base image in the irreducible local
envelope. -/
theorem componentBaseInBlockStabilizerLocalAction_normal
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup K) (hH : H.Normal) (i : Fin b) :
    (P.componentBaseInBlockStabilizerLocalAction H i).Normal :=
  P.system.componentBaseImageInBlockStabilizerCoordinates_normal
    H hH i (P.localCoordinates i)

/-- Prime-group inheritance for every component base image. -/
theorem componentBaseInBlockStabilizerLocalAction_isPGroup
    {p : ℕ}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup K) (hH : IsPGroup p H) (i : Fin b) :
    IsPGroup p (P.componentBaseInBlockStabilizerLocalAction H i) :=
  P.system.componentBaseImageInBlockStabilizerCoordinates_isPGroup
    H hH i (P.localCoordinates i)

/-- The precise prime-core containment needed by local pCore domination. -/
theorem componentBaseInBlockStabilizerLocalAction_le_pCore
    {p : ℕ}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup K) (hHn : H.Normal)
    (hHp : IsPGroup p H) (i : Fin b) :
    P.componentBaseInBlockStabilizerLocalAction H i ≤
      pCore p (P.blockStabilizerLocalAction i) :=
  P.system.componentBaseImageInBlockStabilizerCoordinates_le_pCore
    H hHn hHp i (P.localCoordinates i)

/-- Pullback of a normal coordinate-action component remains normal in the
original presented action. -/
theorem blockActionComponentPreimage_normal
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) (hH : H.Normal) :
    (P.blockActionComponentPreimage H).Normal :=
  Subgroup.Normal.comap hH
    (P.system.coordinateSubgroupEquiv P.localCoordinates).toMonoidHom

/-- Pullback through the coordinate equivalence preserves the prime-group
label. -/
theorem blockActionComponentPreimage_isPGroup
    {p : ℕ}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) (hH : IsPGroup p H) :
    IsPGroup p (P.blockActionComponentPreimage H) :=
  hH.comap_of_injective
    (P.system.coordinateSubgroupEquiv P.localCoordinates).toMonoidHom
    (P.system.coordinateSubgroupEquiv P.localCoordinates).injective

/-- Coordinate-action components are normal in the irreducible local
envelope after taking their base image. -/
theorem componentBaseInBlockStabilizerLocalActionOfBlockAction_normal
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) (hH : H.Normal)
    (i : Fin b) :
    (P.componentBaseInBlockStabilizerLocalActionOfBlockAction H i).Normal :=
  P.componentBaseInBlockStabilizerLocalAction_normal
    (P.blockActionComponentPreimage H)
    (P.blockActionComponentPreimage_normal H hH) i

/-- Coordinate-action component base images retain their prime-group label
inside the irreducible local envelope. -/
theorem componentBaseInBlockStabilizerLocalActionOfBlockAction_isPGroup
    {p : ℕ}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) (hH : IsPGroup p H)
    (i : Fin b) :
    IsPGroup p
      (P.componentBaseInBlockStabilizerLocalActionOfBlockAction H i) :=
  P.componentBaseInBlockStabilizerLocalAction_isPGroup
    (P.blockActionComponentPreimage H)
    (P.blockActionComponentPreimage_isPGroup H hH) i

/-- Exact coordinate-action components lie in the prime core of the
irreducible local envelope. -/
theorem componentBaseInBlockStabilizerLocalActionOfBlockAction_le_pCore
    {p : ℕ}
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K) (H : Subgroup P.blockAction) (hHn : H.Normal)
    (hHp : IsPGroup p H) (i : Fin b) :
    P.componentBaseInBlockStabilizerLocalActionOfBlockAction H i ≤
      pCore p (P.blockStabilizerLocalAction i) :=
  P.componentBaseInBlockStabilizerLocalAction_le_pCore
    (P.blockActionComponentPreimage H)
    (P.blockActionComponentPreimage_normal H hHn)
    (P.blockActionComponentPreimage_isPGroup H hHp) i

end PrimeFieldPrimitiveInternalImprimitivityPresentation

end LisiSabatini
