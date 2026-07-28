module

public import LisiSabatini.TwoCoreSymplecticTypeStructure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The semidihedral symplectic-type branch

Mathlib does not currently contain a semidihedral group.  Rather than
postulating any numerical estimate, this file records the standard
normal-form presentation which is the exact output needed from the
Hall--Berger classification.

For rotation order `8*k`, write

`P = ⟨a,b | a^(8*k) = b^2 = 1, b*a*b = a^(4*k-1)⟩`.

The two normal forms are `r i = a^i` and `s i = b*a^i`.  The structure
`IsSemidihedralPresentation P k` below consists only of the normal-form
equivalence and its multiplication table.  In particular, none of the
active-involution or fixed-space bounds is included in the structure:
they are proved from the multiplication table.

The main consequences are:

* every involutory rotation is central;
* the noncentral involutions inject into the kernel of multiplication by
  `4*k` on `ZMod (8*k)`, which has `4*k` elements;
* every coset normal form has a commutator cycle through the central
  half-turn, so every active involution fixes at most a half-dimensional
  subspace.

For `k = 1` this gives the sharp four-active-involution estimate for
`QD16`.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- The twisting exponent `4*k - 1` in the standard semidihedral
presentation with rotation order `8*k`. -/
def semidihedralTwist (k : ℕ) : ZMod (8 * k) :=
  ((4 * k : ℕ) : ZMod (8 * k)) - 1

/-- A genuine semidihedral normal-form presentation.

This is deliberately structural: it contains an equivalence with the two
normal-form copies of `ZMod (8*k)` and the four multiplication laws, but
no cardinal or fixed-space conclusion. -/
structure IsSemidihedralPresentation
    (P : Type*) [Group P] (k : ℕ) where
  normalForm : (ZMod (8 * k) ⊕ ZMod (8 * k)) ≃ P
  one_eq_rotation_zero :
    (normalForm (.inl 0)) = 1
  rotation_mul_rotation :
    ∀ i j : ZMod (8 * k),
      normalForm (.inl i) * normalForm (.inl j) =
        normalForm (.inl (i + j))
  rotation_mul_coset :
    ∀ i j : ZMod (8 * k),
      normalForm (.inl i) * normalForm (.inr j) =
        normalForm (.inr (j + semidihedralTwist k * i))
  coset_mul_rotation :
    ∀ i j : ZMod (8 * k),
      normalForm (.inr i) * normalForm (.inl j) =
        normalForm (.inr (i + j))
  coset_mul_coset :
    ∀ i j : ZMod (8 * k),
      normalForm (.inr i) * normalForm (.inr j) =
        normalForm (.inl (j + semidihedralTwist k * i))

namespace IsSemidihedralPresentation

variable {P : Type*} [Group P] {k : ℕ}

/-- The rotation normal form. -/
def rotation (h : IsSemidihedralPresentation P k)
    (i : ZMod (8 * k)) : P :=
  h.normalForm (.inl i)

/-- The nontrivial-coset normal form. -/
def coset (h : IsSemidihedralPresentation P k)
    (i : ZMod (8 * k)) : P :=
  h.normalForm (.inr i)

theorem rotation_injective
    (h : IsSemidihedralPresentation P k) :
    Function.Injective h.rotation := by
  intro i j hij
  exact Sum.inl.inj (h.normalForm.injective hij)

theorem coset_injective
    (h : IsSemidihedralPresentation P k) :
    Function.Injective h.coset := by
  intro i j hij
  exact Sum.inr.inj (h.normalForm.injective hij)

theorem rotation_ne_coset
    (h : IsSemidihedralPresentation P k)
    (i j : ZMod (8 * k)) :
    h.rotation i ≠ h.coset j := by
  intro hij
  have := h.normalForm.injective hij
  exact Sum.inl_ne_inr this

theorem exists_rotation_or_coset
    (h : IsSemidihedralPresentation P k) (x : P) :
    (∃ i, x = h.rotation i) ∨
      ∃ i, x = h.coset i := by
  cases hx : h.normalForm.symm x with
  | inl i =>
      left
      refine ⟨i, ?_⟩
      simpa [rotation, hx] using
        (h.normalForm.apply_symm_apply x).symm
  | inr i =>
      right
      refine ⟨i, ?_⟩
      simpa [coset, hx] using
        (h.normalForm.apply_symm_apply x).symm

@[simp]
theorem rotation_zero
    (h : IsSemidihedralPresentation P k) :
    h.rotation 0 = 1 :=
  h.one_eq_rotation_zero

@[simp]
theorem rotation_mul_rotation_apply
    (h : IsSemidihedralPresentation P k)
    (i j : ZMod (8 * k)) :
    h.rotation i * h.rotation j = h.rotation (i + j) :=
  h.rotation_mul_rotation i j

@[simp]
theorem rotation_mul_coset_apply
    (h : IsSemidihedralPresentation P k)
    (i j : ZMod (8 * k)) :
    h.rotation i * h.coset j =
      h.coset (j + semidihedralTwist k * i) :=
  h.rotation_mul_coset i j

@[simp]
theorem coset_mul_rotation_apply
    (h : IsSemidihedralPresentation P k)
    (i j : ZMod (8 * k)) :
    h.coset i * h.rotation j = h.coset (i + j) :=
  h.coset_mul_rotation i j

@[simp]
theorem coset_mul_coset_apply
    (h : IsSemidihedralPresentation P k)
    (i j : ZMod (8 * k)) :
    h.coset i * h.coset j =
      h.rotation (j + semidihedralTwist k * i) :=
  h.coset_mul_coset i j

/-- The cast of the rotation order vanishes in its residue ring. -/
private theorem rotationOrder_eq_zero (k : ℕ) :
    ((8 * k : ℕ) : ZMod (8 * k)) = 0 := by
  simp

/-- The half-turn commutes with every normal form. -/
theorem halfTurn_mem_center
    (h : IsSemidihedralPresentation P k) :
    h.rotation ((4 * k : ℕ) : ZMod (8 * k)) ∈
      Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro x
  rcases h.exists_rotation_or_coset x with ⟨i, rfl⟩ | ⟨i, rfl⟩
  · simp only [rotation_mul_rotation_apply]
    exact congrArg h.rotation (add_comm i _)
  · simp only [coset_mul_rotation_apply, rotation_mul_coset_apply]
    apply congrArg h.coset
    have hmod := rotationOrder_eq_zero k
    have hmod' :
        (8 : ZMod (8 * k)) * (k : ZMod (8 * k)) = 0 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmod
    dsimp only [semidihedralTwist]
    norm_num [Nat.cast_mul]
    linear_combination
      ((1 - 2 * (k : ZMod (8 * k))) * hmod')

/-- For positive `k`, the half-turn is nontrivial. -/
theorem halfTurn_ne_one
    (h : IsSemidihedralPresentation P k) (hk : 0 < k) :
    h.rotation ((4 * k : ℕ) : ZMod (8 * k)) ≠ 1 := by
  intro hone
  have hforms :
      h.rotation ((4 * k : ℕ) : ZMod (8 * k)) =
        h.rotation 0 := by
    simpa using hone
  have hz :
      ((4 * k : ℕ) : ZMod (8 * k)) = 0 :=
    h.rotation_injective hforms
  have hval := congrArg ZMod.val hz
  rw [ZMod.val_natCast, ZMod.val_zero] at hval
  have hlt : 4 * k < 8 * k := by omega
  rw [Nat.mod_eq_of_lt hlt] at hval
  omega

/-- The half-turn has square one. -/
theorem halfTurn_sq
    (h : IsSemidihedralPresentation P k) :
    h.rotation ((4 * k : ℕ) : ZMod (8 * k)) ^ 2 = 1 := by
  rw [pow_two, rotation_mul_rotation_apply]
  rw [← h.rotation_zero]
  apply congrArg h.rotation
  have hmod := rotationOrder_eq_zero k
  have hmod' :
      (8 : ZMod (8 * k)) * (k : ZMod (8 * k)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmod
  norm_num [Nat.cast_mul]
  linear_combination hmod'

/-- Every rotation of order two is central. -/
theorem rotation_mem_center_of_orderOf_eq_two
    (h : IsSemidihedralPresentation P k)
    (i : ZMod (8 * k))
    (hi : orderOf (h.rotation i) = 2) :
    h.rotation i ∈ Subgroup.center P := by
  have hiSq : h.rotation i ^ 2 = 1 := by
    rw [← hi]
    exact pow_orderOf_eq_one (h.rotation i)
  have hiTwo : i + i = 0 := by
    apply h.rotation_injective
    simpa [pow_two] using hiSq
  have htwist : semidihedralTwist k * i = i := by
    dsimp only [semidihedralTwist]
    norm_num [Nat.cast_mul]
    linear_combination
      ((2 * (k : ZMod (8 * k)) - 1) * hiTwo)
  rw [Subgroup.mem_center_iff]
  intro x
  rcases h.exists_rotation_or_coset x with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · simp only [rotation_mul_rotation_apply]
    exact congrArg h.rotation (add_comm j i)
  · simp only [coset_mul_rotation_apply, rotation_mul_coset_apply,
      htwist]

/-- Every coset normal form has the central-half-turn commutator cycle
needed by the fixed-space argument. -/
theorem coset_centralInvolutionCycle
    (h : IsSemidihedralPresentation P k)
    (i : ZMod (8 * k)) :
    let y := h.rotation ((2 * k : ℕ) : ZMod (8 * k))
    let z := h.rotation ((4 * k : ℕ) : ZMod (8 * k))
    h.coset i * y = z * y * h.coset i := by
  dsimp only
  simp only [coset_mul_rotation_apply, rotation_mul_rotation_apply,
    rotation_mul_coset_apply]
  apply congrArg h.coset
  have hmod := rotationOrder_eq_zero k
  have hmod' :
      (8 : ZMod (8 * k)) * (k : ZMod (8 * k)) = 0 := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hmod
  dsimp only [semidihedralTwist]
  norm_num [Nat.cast_mul]
  linear_combination
    ((1 - 3 * (k : ZMod (8 * k))) * hmod')

/-- The additive kernel indexing precisely the involutory coset normal
forms. -/
abbrev involutoryCosetIndex (k : ℕ) :=
  (nsmulAddMonoidHom (4 * k) :
    ZMod (8 * k) →+ ZMod (8 * k)).ker

/-- A coset element whose square is one supplies an element of the
indexing kernel. -/
def involutoryCosetIndexOf
    (h : IsSemidihedralPresentation P k)
    (i : ZMod (8 * k))
    (hi : h.coset i ^ 2 = 1) :
    involutoryCosetIndex k := by
  refine ⟨i, ?_⟩
  have hsquare :
      h.rotation (i + semidihedralTwist k * i) =
        h.rotation 0 := by
    simpa [pow_two] using hi
  have hindex :
      i + semidihedralTwist k * i = 0 :=
    h.rotation_injective hsquare
  change (4 * k) • i = 0
  dsimp only [semidihedralTwist] at hindex
  norm_num [nsmul_eq_mul, Nat.cast_mul] at hindex ⊢
  linear_combination hindex

/-- The involutory coset-index kernel has `4*k` elements. -/
theorem natCard_involutoryCosetIndex (k : ℕ) (hk : 0 < k) :
    Nat.card (involutoryCosetIndex k) = 4 * k := by
  letI : NeZero (8 * k) := ⟨by omega⟩
  rw [IsAddCyclic.card_nsmulAddMonoidHom_ker]
  simp only [Nat.card_zmod]
  have hEight : 8 * k = 2 * (4 * k) := by omega
  rw [hEight]
  calc
    (2 * (4 * k)).gcd (4 * k) =
        (2 * (4 * k)).gcd (1 * (4 * k)) := by rw [one_mul]
    _ = (2 : ℕ).gcd 1 * (4 * k) :=
      Nat.gcd_mul_right 2 (4 * k) 1
    _ = 4 * k := by simp

end IsSemidihedralPresentation

/-! ## Transfer to a concrete linear copy -/

/-- An active involution in a fixed-point-free-center semidihedral copy
must be a coset normal form. -/
private theorem exists_eq_coset_of_active_semidihedral
    {r d k : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsSemidihedralPresentation P k)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    ∃ i : ZMod (8 * k), x = hP.coset i := by
  have hxOrder : orderOf x = 2 :=
    (mem_activePrimeOrderElements 2 P x).mp hx |>.1
  have hxActive : x ∈ nonzeroFixingElements P :=
    (mem_activePrimeOrderElements 2 P x).mp hx |>.2
  have hxNoncentral : x ∉ Subgroup.center P :=
    C.active_not_mem_center x hxActive
  rcases hP.exists_rotation_or_coset x with ⟨i, hi⟩ | ⟨i, hi⟩
  · exfalso
    apply hxNoncentral
    rw [hi]
    apply hP.rotation_mem_center_of_orderOf_eq_two
    simpa [← hi] using hxOrder
  · exact ⟨i, hi⟩

/-- A semidihedral copy of rotation order `8*k` has at most `4*k`
active involutions. -/
theorem card_activePrimeOrderElements_two_le_of_semidihedral
    {r d k : ℕ} [Fact r.Prime]
    (hk : 0 < k)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsSemidihedralPresentation P k)
    (C : CenterFixedPointFreeAction r d P) :
    (activePrimeOrderElements 2 P).card ≤ 4 * k := by
  classical
  letI : NeZero (8 * k) := ⟨by omega⟩
  let A := {x : P // x ∈ activePrimeOrderElements 2 P}
  let cosetIndex : A → ZMod (8 * k) := fun x ↦
    Classical.choose
      (exists_eq_coset_of_active_semidihedral P hP C x.1 x.2)
  have hcoset (x : A) :
      x.1 = hP.coset (cosetIndex x) :=
    Classical.choose_spec
      (exists_eq_coset_of_active_semidihedral P hP C x.1 x.2)
  let index : A →
      IsSemidihedralPresentation.involutoryCosetIndex k := fun x ↦ by
    apply hP.involutoryCosetIndexOf (cosetIndex x)
    rw [← hcoset x]
    have hxOrder :=
      (mem_activePrimeOrderElements 2 P x.1).mp x.2 |>.1
    simpa only [hxOrder] using pow_orderOf_eq_one x.1
  have hindex (x : A) :
      x.1 = hP.coset (index x).1 := by
    simpa [index] using hcoset x
  have hinjective : Function.Injective index := by
    intro x y hxy
    apply Subtype.ext
    rw [hindex x, hindex y, hxy]
  have hcard := Fintype.card_le_of_injective index hinjective
  have hkernelCard :
      Fintype.card
          (IsSemidihedralPresentation.involutoryCosetIndex k) =
        4 * k := by
    rw [← Nat.card_eq_fintype_card]
    exact
      IsSemidihedralPresentation.natCard_involutoryCosetIndex k hk
  calc
    (activePrimeOrderElements 2 P).card =
        Fintype.card A :=
      (Fintype.card_coe (activePrimeOrderElements 2 P)).symm
    _ ≤ Fintype.card
        (IsSemidihedralPresentation.involutoryCosetIndex k) :=
      hcard
    _ = 4 * k := hkernelCard

/-- Every active involution in a semidihedral linear copy has a
half-dimensional fixed rectangle. -/
theorem activeInvolution_fixedVectorSet_sq_le_of_semidihedral
    {r d k : ℕ} [Fact r.Prime]
    (hdeven : Even d) (hk : 0 < k)
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsSemidihedralPresentation P k)
    (C : CenterFixedPointFreeAction r d P)
    (x : P) (hx : x ∈ activePrimeOrderElements 2 P) :
    (fixedVectorSet x.1).ncard *
        (fixedVectorSet x.1).ncard ≤
      r ^ d := by
  obtain ⟨i, hi⟩ :=
    exists_eq_coset_of_active_semidihedral P hP C x hx
  let y : P :=
    hP.rotation ((2 * k : ℕ) : ZMod (8 * k))
  let zP : P :=
    hP.rotation ((4 * k : ℕ) : ZMod (8 * k))
  have hzCenter : zP ∈ Subgroup.center P := by
    simpa [zP] using hP.halfTurn_mem_center
  let z : Subgroup.center P := ⟨zP, hzCenter⟩
  have hzNe : z ≠ 1 := by
    intro hz
    apply hP.halfTurn_ne_one hk
    exact congrArg Subtype.val hz
  have hzSq : z ^ 2 = 1 := by
    apply Subtype.ext
    simpa [z, zP] using hP.halfTurn_sq
  have hxy : x * y = z.1 * y * x := by
    rw [hi]
    simpa [y, z, zP] using hP.coset_centralInvolutionCycle i
  exact
    fixedVectorSet_sq_le_of_symplecticType_centralInvolutionCycle
      hdeven P C x y z hzNe hzSq hxy

end LisiSabatini
