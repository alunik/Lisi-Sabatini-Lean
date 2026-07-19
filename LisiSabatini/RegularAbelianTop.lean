import LisiSabatini.SemiregularTopCore
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Centralizers of regular abelian permutation groups

Let `A` be an abelian subgroup of the permutation group of a set `I`.  If
`A` is transitive, then its action is automatically semiregular: an element
fixing one point fixes every point, because it commutes with the elements
carrying that point around the unique orbit.  Thus `A` is regular.

The same argument proves the permutation-theoretic bridge needed in the
imprimitive branch of the NCAS reduction.  A permutation commuting with
every element of `A` is determined by the image of one point.  Transitivity
provides an element of `A` with that same image, and abelianness then shows
that the two permutations agree everywhere.  Consequently the full ambient
centralizer of a regular abelian permutation group is the group itself.  In
particular, if `A ≤ T`, then the centralizer of `A` inside `T` is `A`.
-/

noncomputable section

namespace LisiSabatini

universe uI

variable {I : Type uI}

/-! ## Transitive and regular abelian permutation subgroups -/

/-- A permutation subgroup is transitive when any point can be carried to
any other point by one of its elements.  This proposition-valued definition
is convenient when transitivity is data attached to a particular subgroup,
without installing a global `MulAction.IsPretransitive` instance. -/
def IsTransitivePermutationSubgroup
    (A : Subgroup (Equiv.Perm I)) : Prop :=
  ∀ x y : I, ∃ a : A, (a : Equiv.Perm I) x = y

/-- A regular abelian permutation subgroup: transitive, semiregular, and
pairwise commuting.  Semiregularity uses the definition shared with the
single-marker imprimitive reduction in `SemiregularTop`. -/
structure IsRegularAbelianPermutationSubgroup
    (A : Subgroup (Equiv.Perm I)) : Prop where
  transitive : IsTransitivePermutationSubgroup A
  semiregular : IsSemiregularPermutationSubgroup A
  pairwise_commute : ∀ a b : A, Commute a b

/-- A transitive abelian permutation subgroup is automatically
semiregular.  The faithfulness needed here is built into the realization as
a subgroup of `Equiv.Perm I`. -/
theorem isSemiregularPermutationSubgroup_of_transitive_of_pairwiseCommute
    (A : Subgroup (Equiv.Perm I))
    (htrans : IsTransitivePermutationSubgroup A)
    (hcomm : ∀ a b : A, Commute a b) :
    IsSemiregularPermutationSubgroup A := by
  intro ω
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro a ha
  have haω : (a : Equiv.Perm I) ω = ω := by
    have := MulAction.mem_stabilizer_iff.mp ha
    exact this
  apply Subtype.ext
  apply Equiv.ext
  intro x
  obtain ⟨b, hb⟩ := htrans ω x
  have hab :
      (a : Equiv.Perm I) ((b : Equiv.Perm I) ω) =
        (b : Equiv.Perm I) ((a : Equiv.Perm I) ω) := by
    simpa only [Equiv.Perm.mul_apply] using
      congrArg (fun τ : Equiv.Perm I ↦ τ ω)
        (congrArg Subtype.val (hcomm a b).eq)
  calc
    (a : Equiv.Perm I) x =
        (a : Equiv.Perm I) ((b : Equiv.Perm I) ω) :=
      congrArg (a : Equiv.Perm I) hb.symm
    _ = (b : Equiv.Perm I) ((a : Equiv.Perm I) ω) := hab
    _ = (b : Equiv.Perm I) ω := congrArg (b : Equiv.Perm I) haω
    _ = x := hb
    _ = ((1 : A) : Equiv.Perm I) x := by rfl

/-- Package transitivity and pairwise commutativity as a regular abelian
permutation action. -/
theorem isRegularAbelianPermutationSubgroup_of_transitive_of_pairwiseCommute
    (A : Subgroup (Equiv.Perm I))
    (htrans : IsTransitivePermutationSubgroup A)
    (hcomm : ∀ a b : A, Commute a b) :
    IsRegularAbelianPermutationSubgroup A where
  transitive := htrans
  semiregular :=
    isSemiregularPermutationSubgroup_of_transitive_of_pairwiseCommute
      A htrans hcomm
  pairwise_commute := hcomm

/-! ## The ambient centralizer theorem -/

/-- A permutation commuting with every element of a transitive abelian
permutation subgroup belongs to that subgroup.  This is the elementwise,
slightly stronger engine behind the centralizer theorem. -/
theorem mem_of_commutes_with_transitive_abelian_permutationSubgroup
    (A : Subgroup (Equiv.Perm I))
    (htrans : IsTransitivePermutationSubgroup A)
    (hcomm : ∀ a b : A, Commute a b)
    {σ : Equiv.Perm I}
    (hσ : ∀ a : A, Commute (a : Equiv.Perm I) σ) :
    σ ∈ A := by
  classical
  by_cases hI : Nonempty I
  · let ω : I := Classical.choice hI
    obtain ⟨a, ha⟩ := htrans ω (σ ω)
    have haσ : (a : Equiv.Perm I) = σ := by
      apply Equiv.ext
      intro x
      obtain ⟨b, hb⟩ := htrans ω x
      have hab :
          (a : Equiv.Perm I) ((b : Equiv.Perm I) ω) =
            (b : Equiv.Perm I) ((a : Equiv.Perm I) ω) := by
        simpa only [Equiv.Perm.mul_apply] using
          congrArg (fun τ : Equiv.Perm I ↦ τ ω)
            (congrArg Subtype.val (hcomm a b).eq)
      have hbσ :
          (b : Equiv.Perm I) (σ ω) =
            σ ((b : Equiv.Perm I) ω) := by
        simpa only [Equiv.Perm.mul_apply] using
          congrArg (fun τ : Equiv.Perm I ↦ τ ω) (hσ b).eq
      calc
        (a : Equiv.Perm I) x =
            (a : Equiv.Perm I) ((b : Equiv.Perm I) ω) :=
          congrArg (a : Equiv.Perm I) hb.symm
        _ = (b : Equiv.Perm I) ((a : Equiv.Perm I) ω) := hab
        _ = (b : Equiv.Perm I) (σ ω) :=
          congrArg (b : Equiv.Perm I) ha
        _ = σ ((b : Equiv.Perm I) ω) := hbσ
        _ = σ x := congrArg σ hb
    rw [← haσ]
    exact a.2
  · have hσone : σ = 1 := by
      apply Equiv.ext
      intro x
      exact (hI ⟨x⟩).elim
    rw [hσone]
    exact A.one_mem

/-- The full ambient centralizer of a regular abelian permutation subgroup
is contained in that subgroup. -/
theorem centralizer_le_of_isRegularAbelianPermutationSubgroup
    (A : Subgroup (Equiv.Perm I))
    (hA : IsRegularAbelianPermutationSubgroup A) :
    Subgroup.centralizer (A : Set (Equiv.Perm I)) ≤ A := by
  intro σ hσ
  apply mem_of_commutes_with_transitive_abelian_permutationSubgroup
    A hA.transitive hA.pairwise_commute
  intro a
  exact Subgroup.mem_centralizer_iff.mp hσ a a.2

/-- A regular abelian permutation subgroup is exactly its centralizer in
the full symmetric group. -/
theorem centralizer_eq_of_isRegularAbelianPermutationSubgroup
    (A : Subgroup (Equiv.Perm I))
    (hA : IsRegularAbelianPermutationSubgroup A) :
    Subgroup.centralizer (A : Set (Equiv.Perm I)) = A := by
  apply le_antisymm
  · exact centralizer_le_of_isRegularAbelianPermutationSubgroup A hA
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      (hA.pairwise_commute ⟨b, hb⟩ ⟨a, ha⟩).eq

/-- If `A ≤ T`, then the centralizer of `A` inside `T`, represented as
the intersection of `T` with the ambient centralizer, is exactly `A`. -/
theorem inf_centralizer_eq_of_isRegularAbelianPermutationSubgroup
    (A T : Subgroup (Equiv.Perm I))
    (hAT : A ≤ T)
    (hA : IsRegularAbelianPermutationSubgroup A) :
    T ⊓ Subgroup.centralizer (A : Set (Equiv.Perm I)) = A := by
  rw [centralizer_eq_of_isRegularAbelianPermutationSubgroup A hA]
  exact inf_eq_right.mpr hAT

/-- Inclusion form of the relative-centralizer theorem. -/
theorem inf_centralizer_le_of_isRegularAbelianPermutationSubgroup
    (A T : Subgroup (Equiv.Perm I))
    (hA : IsRegularAbelianPermutationSubgroup A) :
    T ⊓ Subgroup.centralizer (A : Set (Equiv.Perm I)) ≤ A := by
  exact inf_le_right.trans
    (centralizer_le_of_isRegularAbelianPermutationSubgroup A hA)

end LisiSabatini
