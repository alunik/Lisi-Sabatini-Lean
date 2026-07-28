module

public import LisiSabatini.LinearImprimitivityCoarsening
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Order.Atoms.Finite

/-!
# Canonical coarsening from a block of the permutation top

Let `S` be a linear system of imprimitivity.  A nonempty block `B` for the
induced permutation group on the fine block indices has pairwise-disjoint
translates which cover the index set (provided the top action is
pretransitive).  This file turns that block system into the concrete
equivariant quotient required by `EquivariantBlockIndexQuotient`.

The coarse index type is literally the orbit of `B` under the permutation
image.  The map from fine indices sends an index to the unique translate of
`B` containing it.  We construct the induced permutation representation,
prove surjectivity and equivariance of the containing-block map, and finally
obtain the corresponding coarsened linear system.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe uI uR uV

variable {I : Type uI} {R : Type uR} {V : Type uV}
variable [Ring R] [AddCommGroup V] [Module R V]
variable [Fintype I] [DecidableEq I]
variable {K : Subgroup (LinearMap.GeneralLinearGroup R V)}

namespace LinearImprimitivitySystem

variable (S : LinearImprimitivitySystem (I := I) K)

/-- The concrete image of the induced permutation action on the fine block
indices. -/
abbrev fineTop : Subgroup (Equiv.Perm I) := S.blockPerm.range

/-- The coarse index type associated to a block `B`: its elements are
precisely the translates of `B` under the fine permutation top. -/
def OrbitBlockIndex (B : Set I) :=
  {C : Set I // C ∈ Set.range (fun σ : S.fineTop => σ • B)}

noncomputable instance orbitBlockIndexFintype (B : Set I) :
    Fintype (S.OrbitBlockIndex B) := by
  classical
  exact Fintype.ofInjective
    (fun C : S.OrbitBlockIndex B => Fintype.finsetEquivSet.symm C.1)
    (fun C D h => Subtype.ext (Fintype.finsetEquivSet.symm.injective h))

noncomputable instance orbitBlockIndexDecidableEq (B : Set I) :
    DecidableEq (S.OrbitBlockIndex B) :=
  Classical.decEq _

/-- The original block, regarded as the distinguished member of its orbit. -/
def baseOrbitBlock (B : Set I) : S.OrbitBlockIndex B :=
  ⟨B, ⟨1, by simp⟩⟩

@[simp]
theorem baseOrbitBlock_coe (B : Set I) : (S.baseOrbitBlock B).1 = B :=
  rfl

/-- The element of the concrete fine permutation top induced by `g : K`. -/
def fineTopElement (g : K) : S.fineTop :=
  ⟨S.blockPerm g, ⟨g, rfl⟩⟩

@[simp]
theorem fineTopElement_coe (g : K) :
    (S.fineTopElement g : Equiv.Perm I) = S.blockPerm g :=
  rfl

@[simp]
theorem fineTopElement_one : S.fineTopElement 1 = 1 := by
  ext i
  simp [fineTopElement]

@[simp]
theorem fineTopElement_mul (g h : K) :
    S.fineTopElement (g * h) = S.fineTopElement g * S.fineTopElement h := by
  ext i
  simp [fineTopElement]

/-- Translation by an element of the fine permutation top, restricted to the
orbit block system. -/
def fineTopOrbitBlockEquiv (B : Set I) (g : S.fineTop) :
    S.OrbitBlockIndex B ≃ S.OrbitBlockIndex B where
  toFun C := ⟨g • C.1, by
    rcases C.2 with ⟨σ, hσ⟩
    refine ⟨g * σ, ?_⟩
    change (g * σ) • B = g • C.1
    rw [mul_smul]
    exact congrArg (fun A : Set I => g • A) hσ⟩
  invFun C := ⟨g⁻¹ • C.1, by
    rcases C.2 with ⟨σ, hσ⟩
    refine ⟨g⁻¹ * σ, ?_⟩
    change (g⁻¹ * σ) • B = g⁻¹ • C.1
    rw [mul_smul]
    exact congrArg (fun A : Set I => g⁻¹ • A) hσ⟩
  left_inv C := by
    apply Subtype.ext
    change g⁻¹ • (g • C.1) = C.1
    rw [inv_smul_smul]
  right_inv C := by
    apply Subtype.ext
    change g • (g⁻¹ • C.1) = C.1
    rw [smul_inv_smul]

@[simp]
theorem fineTopOrbitBlockEquiv_coe (B : Set I) (g : S.fineTop)
    (C : S.OrbitBlockIndex B) :
    (S.fineTopOrbitBlockEquiv B g C).1 = g • C.1 :=
  rfl

/-- The canonical action of the fine permutation top on the orbit block
system. -/
def fineTopOrbitBlockPerm (B : Set I) :
    S.fineTop →* Equiv.Perm (S.OrbitBlockIndex B) where
  toFun := S.fineTopOrbitBlockEquiv B
  map_one' := by
    ext C : 1
    apply Subtype.ext
    change (1 : S.fineTop) • C.1 = C.1
    rw [one_smul]
  map_mul' g h := by
    ext C : 1
    apply Subtype.ext
    change (g * h) • C.1 = g • (h • C.1)
    rw [mul_smul]

/-- The natural `fineTop`-action on the orbit block index type. -/
instance orbitBlockIndexMulAction (B : Set I) :
    MulAction S.fineTop (S.OrbitBlockIndex B) :=
  MulAction.compHom (S.OrbitBlockIndex B) (S.fineTopOrbitBlockPerm B)

@[simp]
theorem fineTop_smul_orbitBlockIndex_coe (B : Set I) (g : S.fineTop)
    (C : S.OrbitBlockIndex B) :
    (g • C).1 = g • C.1 :=
  rfl

/-- A group element of the original linear group acts on orbit blocks via
its image in the fine permutation top. -/
def orbitBlockEquiv (B : Set I) (g : K) :
    S.OrbitBlockIndex B ≃ S.OrbitBlockIndex B :=
  S.fineTopOrbitBlockEquiv B (S.fineTopElement g)

@[simp]
theorem orbitBlockEquiv_coe (B : Set I) (g : K)
    (C : S.OrbitBlockIndex B) :
    (S.orbitBlockEquiv B g C).1 =
      S.fineTopElement g • C.1 :=
  rfl

/-- The permutation representation induced on the orbit of the chosen
block. -/
def orbitBlockPerm (B : Set I) : K →* Equiv.Perm (S.OrbitBlockIndex B) where
  toFun := S.orbitBlockEquiv B
  map_one' := by
    ext C : 1
    apply Subtype.ext
    change S.fineTopElement 1 • C.1 = C.1
    simp
  map_mul' g h := by
    ext C : 1
    apply Subtype.ext
    change S.fineTopElement (g * h) • C.1 =
      S.fineTopElement g • (S.fineTopElement h • C.1)
    rw [fineTopElement_mul, mul_smul]

@[simp]
theorem orbitBlockPerm_apply_coe (B : Set I) (g : K)
    (C : S.OrbitBlockIndex B) :
    (S.orbitBlockPerm B g C).1 =
      S.fineTopElement g • C.1 :=
  rfl

@[simp]
theorem fineTopOrbitBlockPerm_fineTopElement (B : Set I) (g : K) :
    S.fineTopOrbitBlockPerm B (S.fineTopElement g) =
      S.orbitBlockPerm B g :=
  rfl

/-- The canonical fine-top action and the action induced from `K` have the
same concrete permutation image on orbit blocks. -/
theorem fineTopOrbitBlockPerm_range_eq (B : Set I) :
    (S.fineTopOrbitBlockPerm B).range = (S.orbitBlockPerm B).range := by
  apply le_antisymm
  · rintro τ ⟨σ, rfl⟩
    rcases σ.2 with ⟨g, hg⟩
    have hσ : S.fineTopElement g = σ := Subtype.ext hg
    exact ⟨g, by rw [← hσ, S.fineTopOrbitBlockPerm_fineTopElement]⟩
  · rintro τ ⟨g, rfl⟩
    exact ⟨S.fineTopElement g, S.fineTopOrbitBlockPerm_fineTopElement B g⟩

/-- The translates of a nonempty block form a partition of the fine block
indices. -/
theorem orbitBlock_isPartition (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    Setoid.IsPartition
      (Set.range (fun σ : S.fineTop => σ • B)) := by
  letI := hpre
  exact (hB.isBlockSystem hBne).1

/-- Every fine index belongs to a unique translate of `B`. -/
theorem existsUnique_orbitBlockIndex_mem (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (i : I) :
    ∃! C : S.OrbitBlockIndex B, i ∈ C.1 := by
  obtain ⟨C, hC, hunique⟩ := (S.orbitBlock_isPartition B hpre hB hBne).2 i
  refine ⟨⟨C, hC.1⟩, hC.2, ?_⟩
  intro D hiD
  apply Subtype.ext
  exact hunique D.1 ⟨D.2, hiD⟩

/-- The unique translate of `B` containing a given fine index. -/
def containingOrbitBlock (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (i : I) : S.OrbitBlockIndex B :=
  Classical.choose (S.existsUnique_orbitBlockIndex_mem B hpre hB hBne i)

@[simp]
theorem mem_containingOrbitBlock (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (i : I) :
    i ∈ (S.containingOrbitBlock B hpre hB hBne i).1 :=
  (Classical.choose_spec
    (S.existsUnique_orbitBlockIndex_mem B hpre hB hBne i)).1

/-- Characterization of the containing-block map by membership. -/
theorem containingOrbitBlock_eq_of_mem (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    {i : I} {C : S.OrbitBlockIndex B} (hiC : i ∈ C.1) :
    S.containingOrbitBlock B hpre hB hBne i = C :=
  (Classical.choose_spec
    (S.existsUnique_orbitBlockIndex_mem B hpre hB hBne i)).2 C hiC |>.symm

/-- A fine index maps to `C` exactly when it belongs to the underlying set
of the orbit block `C`. -/
@[simp]
theorem containingOrbitBlock_eq_iff_mem (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (i : I) (C : S.OrbitBlockIndex B) :
    S.containingOrbitBlock B hpre hB hBne i = C ↔ i ∈ C.1 := by
  constructor
  · intro h
    rw [← h]
    exact S.mem_containingOrbitBlock B hpre hB hBne i
  · exact S.containingOrbitBlock_eq_of_mem B hpre hB hBne

@[simp]
theorem containingOrbitBlock_eq_base_iff (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (i : I) :
    S.containingOrbitBlock B hpre hB hBne i = S.baseOrbitBlock B ↔
      i ∈ B := by
  exact S.containingOrbitBlock_eq_iff_mem B hpre hB hBne i
    (S.baseOrbitBlock B)

/-- Every orbit block is nonempty. -/
theorem orbitBlockIndex_nonempty (B : Set I) (hBne : B.Nonempty)
    (C : S.OrbitBlockIndex B) : C.1.Nonempty := by
  rcases C.2 with ⟨σ, hσ⟩
  rw [← hσ]
  obtain ⟨i, hi⟩ := hBne
  exact ⟨σ • i, by simpa using hi⟩

/-- The unique-containing-block map is onto the orbit block system. -/
theorem containingOrbitBlock_surjective (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    Function.Surjective (S.containingOrbitBlock B hpre hB hBne) := by
  intro C
  obtain ⟨i, hiC⟩ := S.orbitBlockIndex_nonempty B hBne C
  exact ⟨i, S.containingOrbitBlock_eq_of_mem B hpre hB hBne hiC⟩

/-- The containing-block map intertwines the fine and coarse permutation
actions. -/
theorem containingOrbitBlock_equivariant (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (g : K) (i : I) :
    S.containingOrbitBlock B hpre hB hBne (S.blockPerm g i) =
      S.orbitBlockPerm B g (S.containingOrbitBlock B hpre hB hBne i) := by
  apply S.containingOrbitBlock_eq_of_mem B hpre hB hBne
  change S.blockPerm g i ∈
    S.fineTopElement g •
      (S.containingOrbitBlock B hpre hB hBne i).1
  exact Set.mem_smul_set.2
    ⟨i, S.mem_containingOrbitBlock B hpre hB hBne i, rfl⟩

/-- Equivariance of the containing-block map for the full fine permutation
top (rather than only for elements displayed as images of `K`). -/
theorem containingOrbitBlock_fineTop_equivariant (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (g : S.fineTop) (i : I) :
    S.containingOrbitBlock B hpre hB hBne (g • i) =
      g • S.containingOrbitBlock B hpre hB hBne i := by
  apply S.containingOrbitBlock_eq_of_mem B hpre hB hBne
  change g • i ∈
    g • (S.containingOrbitBlock B hpre hB hBne i).1
  exact Set.mem_smul_set.2
    ⟨i, S.mem_containingOrbitBlock B hpre hB hBne i, rfl⟩

/-- The orbit-block action of the full fine top is pretransitive. -/
theorem orbitBlockIndex_isPretransitive (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    MulAction.IsPretransitive S.fineTop (S.OrbitBlockIndex B) := by
  refine ⟨fun C D => ?_⟩
  obtain ⟨i, hi⟩ := S.containingOrbitBlock_surjective B hpre hB hBne C
  obtain ⟨j, hj⟩ := S.containingOrbitBlock_surjective B hpre hB hBne D
  obtain ⟨g, hg⟩ := hpre.exists_smul_eq i j
  refine ⟨g, ?_⟩
  have heq := S.containingOrbitBlock_fineTop_equivariant B hpre hB hBne g i
  rw [hg, hi, hj] at heq
  exact heq.symm

/-- A proper nonempty fine block has at least two distinct translates. -/
theorem orbitBlockIndex_nontrivial_of_ne_univ (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (hBproper : B ≠ Set.univ) :
    Nontrivial (S.OrbitBlockIndex B) := by
  rw [Set.ne_univ_iff_exists_notMem] at hBproper
  obtain ⟨i, hi⟩ := hBproper
  rw [nontrivial_iff]
  refine ⟨S.baseOrbitBlock B,
    S.containingOrbitBlock B hpre hB hBne i, ?_⟩
  intro h
  apply hi
  exact (S.containingOrbitBlock_eq_base_iff B hpre hB hBne i).1 h.symm

/-- The stabilizer of the distinguished orbit block is exactly the
setwise stabilizer of the original block in the fine permutation top. -/
theorem stabilizer_baseOrbitBlock (B : Set I) :
    MulAction.stabilizer S.fineTop (S.baseOrbitBlock B) =
      MulAction.stabilizer S.fineTop B := by
  ext g
  simp only [MulAction.mem_stabilizer_iff]
  change S.fineTopOrbitBlockEquiv B g (S.baseOrbitBlock B) =
      S.baseOrbitBlock B ↔ g • B = B
  constructor
  · exact fun h => congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- The induced action on orbit blocks is pretransitive. -/
theorem orbitBlockPerm_isIndexPretransitive (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    ∀ C D : S.OrbitBlockIndex B,
      ∃ g : K, S.orbitBlockPerm B g C = D := by
  intro C D
  obtain ⟨i, hi⟩ := S.containingOrbitBlock_surjective B hpre hB hBne C
  obtain ⟨j, hj⟩ := S.containingOrbitBlock_surjective B hpre hB hBne D
  letI := hpre
  obtain ⟨σ, hσ⟩ := hpre.exists_smul_eq i j
  rcases σ.2 with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  have hgi : S.blockPerm g i = j := by
    rw [hg]
    exact hσ
  have heq := S.containingOrbitBlock_equivariant B hpre hB hBne g i
  rw [hgi, hi, hj] at heq
  exact heq.symm

/-- The canonical equivariant quotient of fine block indices associated to
the orbit of a nonempty permutation block. -/
def orbitBlockQuotient (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    EquivariantBlockIndexQuotient
      (J := S.OrbitBlockIndex B) S where
  indexMap := S.containingOrbitBlock B hpre hB hBne
  indexMap_surjective := S.containingOrbitBlock_surjective B hpre hB hBne
  blockPerm := S.orbitBlockPerm B
  indexMap_equivariant := S.containingOrbitBlock_equivariant B hpre hB hBne

/-- The linear system obtained by grouping fine summands along the
translates of a nonempty permutation block. -/
def coarsenAlongOrbitBlock (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    LinearImprimitivitySystem (I := S.OrbitBlockIndex B) K :=
  (S.orbitBlockQuotient B hpre hB hBne).coarsen

@[simp]
theorem coarsenAlongOrbitBlock_block (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (C : S.OrbitBlockIndex B) :
    (S.coarsenAlongOrbitBlock B hpre hB hBne).block C =
      ⨆ i, ⨆ (_ : S.containingOrbitBlock B hpre hB hBne i = C),
        S.block i :=
  rfl

/-- Intrinsic form of the coarse-block formula: the coarse summand indexed
by `C` is the supremum of exactly the fine summands whose indices lie in
`C`. -/
theorem coarsenAlongOrbitBlock_block_eq_iSup_mem (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (C : S.OrbitBlockIndex B) :
    (S.coarsenAlongOrbitBlock B hpre hB hBne).block C =
      ⨆ i, ⨆ (_ : i ∈ C.1), S.block i := by
  rw [S.coarsenAlongOrbitBlock_block B hpre hB hBne C]
  congr with i
  simp only [S.containingOrbitBlock_eq_iff_mem B hpre hB hBne]

@[simp]
theorem coarsenAlongOrbitBlock_blockPerm (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    (S.coarsenAlongOrbitBlock B hpre hB hBne).blockPerm =
      S.orbitBlockPerm B :=
  rfl

/-- The concrete permutation image of the coarsened system is
pretransitive. -/
theorem coarsenAlongOrbitBlock_blockPerm_range_isPretransitive (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    MulAction.IsPretransitive
      (S.coarsenAlongOrbitBlock B hpre hB hBne).blockPerm.range
      (S.OrbitBlockIndex B) := by
  refine ⟨fun C D => ?_⟩
  obtain ⟨g, hg⟩ := S.orbitBlockPerm_isIndexPretransitive B hpre hB hBne C D
  exact ⟨⟨S.orbitBlockPerm B g, ⟨g, rfl⟩⟩, hg⟩

/-- A block containing two distinct fine indices yields a genuinely smaller
coarse block set. -/
theorem orbitBlockIndex_card_lt_of_nontrivial (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    (hBnt : B.Nontrivial) :
    Fintype.card (S.OrbitBlockIndex B) < Fintype.card I := by
  apply (S.orbitBlockQuotient B hpre hB hBne).fintypeCard_lt_of_not_injective
  change ¬ Function.Injective (S.containingOrbitBlock B hpre hB hBne)
  intro hinj
  rcases hBnt with ⟨i, hi, j, hj, hij⟩
  apply hij
  apply hinj
  calc
    S.containingOrbitBlock B hpre hB hBne i = S.baseOrbitBlock B :=
      (S.containingOrbitBlock_eq_base_iff B hpre hB hBne i).2 hi
    _ = S.containingOrbitBlock B hpre hB hBne j :=
      (S.containingOrbitBlock_eq_base_iff B hpre hB hBne j).2 hj |>.symm

/-! ## Maximal blocks give primitive coarse tops -/

/-- On a finite nontrivial fine index set, a maximal proper block containing
any prescribed index exists.  This is the finite-poset selection step behind
the primitive coarsening theorem below. -/
theorem exists_maximalProperFineTopBlock [Nontrivial I] (i₀ : I) :
    ∃ C : MulAction.BlockMem S.fineTop i₀, IsCoatom C := by
  exact IsCoatomic.exists_coatom (MulAction.BlockMem S.fineTop i₀)

/-- A maximal proper block containing `i₀` makes the canonical fine-top
action on its translates primitive.  Maximality is expressed intrinsically
as the coatom condition in mathlib's ordered type of blocks containing
`i₀`. -/
theorem fineTop_orbitBlock_isPreprimitive_of_isCoatom (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    {i₀ : I} (hi₀ : i₀ ∈ B)
    (hmax : IsCoatom
      (⟨B, hi₀, hB⟩ : MulAction.BlockMem S.fineTop i₀)) :
    MulAction.IsPreprimitive S.fineTop (S.OrbitBlockIndex B) := by
  let b : MulAction.BlockMem S.fineTop i₀ := ⟨B, hi₀, hB⟩
  have hBproper : B ≠ Set.univ := by
    intro hBuniv
    apply hmax.ne_top
    apply Subtype.ext
    exact hBuniv
  letI : MulAction.IsPretransitive S.fineTop I := hpre
  letI : MulAction.IsPretransitive S.fineTop (S.OrbitBlockIndex B) :=
    S.orbitBlockIndex_isPretransitive B hpre hB hBne
  letI : Nontrivial (S.OrbitBlockIndex B) :=
    S.orbitBlockIndex_nontrivial_of_ne_univ B hpre hB hBne hBproper
  have hstabIci : IsCoatom
      ((MulAction.block_stabilizerOrderIso S.fineTop i₀) b) :=
    ((MulAction.block_stabilizerOrderIso S.fineTop i₀).isCoatom_iff b).2 hmax
  have hstab : IsCoatom (MulAction.stabilizer S.fineTop B) := by
    exact IsCoatom.of_isCoatom_coe_Ici hstabIci
  have hbase : IsCoatom
      (MulAction.stabilizer S.fineTop (S.baseOrbitBlock B)) := by
    rw [S.stabilizer_baseOrbitBlock B]
    exact hstab
  exact (MulAction.isCoatom_stabilizer_iff_preprimitive
    S.fineTop (S.baseOrbitBlock B)).1 hbase

/-- The concrete permutation image of the canonical orbit-block action is
primitive under the same maximal-block hypothesis. -/
theorem fineTopOrbitBlockPerm_range_isPreprimitive_of_isCoatom (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    {i₀ : I} (hi₀ : i₀ ∈ B)
    (hmax : IsCoatom
      (⟨B, hi₀, hB⟩ : MulAction.BlockMem S.fineTop i₀)) :
    MulAction.IsPreprimitive (S.fineTopOrbitBlockPerm B).range
      (S.OrbitBlockIndex B) := by
  letI : MulAction.IsPreprimitive S.fineTop (S.OrbitBlockIndex B) :=
    S.fineTop_orbitBlock_isPreprimitive_of_isCoatom
      B hpre hB hBne hi₀ hmax
  let φ : S.fineTop →* (S.fineTopOrbitBlockPerm B).range :=
    (S.fineTopOrbitBlockPerm B).rangeRestrict
  let f : S.OrbitBlockIndex B →ₑ[φ] S.OrbitBlockIndex B := {
    toFun := id
    map_smul' := by
      intro g C
      rfl
  }
  exact MulAction.IsPreprimitive.of_surjective
    (f := f) Function.surjective_id

/-- **Maximal-block primitive coarsening.**  Choosing a maximal proper block
of the fine permutation action produces a coarsened linear system whose
permutation top is primitive. -/
theorem coarsenAlongOrbitBlock_blockPerm_range_isPreprimitive_of_isCoatom
    (B : Set I)
    (hpre : MulAction.IsPretransitive S.fineTop I)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty)
    {i₀ : I} (hi₀ : i₀ ∈ B)
    (hmax : IsCoatom
      (⟨B, hi₀, hB⟩ : MulAction.BlockMem S.fineTop i₀)) :
    MulAction.IsPreprimitive
      (S.coarsenAlongOrbitBlock B hpre hB hBne).blockPerm.range
      (S.OrbitBlockIndex B) := by
  rw [S.coarsenAlongOrbitBlock_blockPerm B hpre hB hBne,
    ← S.fineTopOrbitBlockPerm_range_eq B]
  exact S.fineTopOrbitBlockPerm_range_isPreprimitive_of_isCoatom
    B hpre hB hBne hi₀ hmax

/-- **Existence of a primitive coarsening.**  For a finite nontrivial fine
block set, maximal-block selection and orbit-block coarsening combine into
one witness whose concrete permutation top is primitive. -/
theorem exists_primitiveCoarsening [Nontrivial I] (i₀ : I)
    (hpre : MulAction.IsPretransitive S.fineTop I) :
    ∃ C : MulAction.BlockMem S.fineTop i₀,
      IsCoatom C ∧
        MulAction.IsPreprimitive
          (S.coarsenAlongOrbitBlock C.1 hpre C.2.2
            ⟨i₀, C.2.1⟩).blockPerm.range
          (S.OrbitBlockIndex C.1) := by
  obtain ⟨C, hC⟩ := S.exists_maximalProperFineTopBlock i₀
  refine ⟨C, hC, ?_⟩
  exact
    S.coarsenAlongOrbitBlock_blockPerm_range_isPreprimitive_of_isCoatom
      C.1 hpre C.2.2 ⟨i₀, C.2.1⟩ C.2.1 hC

/-- Irreducibility supplies the required pretransitivity automatically. -/
def coarsenAlongOrbitBlockOfIrreducible (B : Set I)
    (hirr : IsIrreducible K)
    (hB : MulAction.IsBlock S.fineTop B) (hBne : B.Nonempty) :
    LinearImprimitivitySystem (I := S.OrbitBlockIndex B) K :=
  S.coarsenAlongOrbitBlock B
    (S.blockPerm_range_isPretransitive_of_irreducible hirr) hB hBne

/-- An irreducible action on a nontrivial finite block system therefore has
a maximal orbit-block coarsening with primitive concrete top. -/
theorem exists_primitiveCoarsening_of_irreducible [Nontrivial I] (i₀ : I)
    (hirr : IsIrreducible K) :
    ∃ C : MulAction.BlockMem S.fineTop i₀,
      IsCoatom C ∧
        MulAction.IsPreprimitive
          (S.coarsenAlongOrbitBlockOfIrreducible C.1 hirr C.2.2
            ⟨i₀, C.2.1⟩).blockPerm.range
          (S.OrbitBlockIndex C.1) := by
  simpa [coarsenAlongOrbitBlockOfIrreducible] using
    S.exists_primitiveCoarsening i₀
      (S.blockPerm_range_isPretransitive_of_irreducible hirr)

end LinearImprimitivitySystem

end LisiSabatini
