import LisiSabatini.FixedPointFreeOffZero

/-!
# Translated palettes for fixed-point-free linear actions

For a linear group whose nonidentity elements fix no nonzero vector, every
nonzero vector is regular.  Consequently, an arbitrary affine translate of
such an action forbids at most one point: the negative of its translation.
A finite family smaller than the ambient module therefore has a common
regular translate, independently of the module dimension.

The active-index version counts only nontrivial acting groups.  This is the
form suited to families in which some local images vanish.
-/

noncomputable section

namespace LisiSabatini

universe uI uR uV

/-! ## One fixed-point-free action -/

/-- A nonzero vector is regular for a fixed-point-free-off-zero linear
action. -/
theorem stabilizer_eq_bot_of_fixedPointFreeOffZero_of_ne_zero
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : FixedPointFreeOffZero H) {v : V} (hv : v ≠ 0) :
    MulAction.stabilizer H v = ⊥ := by
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro g hg
  by_cases hgone : g = 1
  · exact hgone
  · have hfix : g • v = v := by
      rw [← MulAction.mem_stabilizer_iff]
      exact hg
    exact False.elim (hv (hH g hgone v hfix))

/-- Under a fixed-point-free-off-zero action, every nonregular vector is
zero. -/
theorem nonregularVectors_subset_singleton_of_fixedPointFreeOffZero
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : FixedPointFreeOffZero H) :
    nonregularVectors H ⊆ ({0} : Set V) := by
  intro v hv
  simp only [Set.mem_singleton_iff]
  by_contra hv0
  exact hv (stabilizer_eq_bot_of_fixedPointFreeOffZero_of_ne_zero H hH hv0)

/-- The bad locus of a fixed-point-free-off-zero action contains at most one
vector. -/
theorem ncard_nonregularVectors_le_one_of_fixedPointFreeOffZero
    {R : Type uR} {V : Type uV}
    [Semiring R] [AddCommMonoid V] [Module R V]
    (H : Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : FixedPointFreeOffZero H) :
    (nonregularVectors H).ncard ≤ 1 := by
  calc
    (nonregularVectors H).ncard ≤ ({0} : Set V).ncard :=
      Set.ncard_le_ncard
        (nonregularVectors_subset_singleton_of_fixedPointFreeOffZero H hH)
        (Set.toFinite _)
    _ = 1 := Set.ncard_singleton 0

/-! ## Arbitrary translated families -/

/-- In a finite additive group, fewer forbidden points than ambient points
cannot exhaust the group. -/
theorem exists_add_translates_ne_zero_of_natCard_lt
    {I : Type uI} {V : Type uV}
    [Finite I] [Finite V] [AddGroup V]
    (hcard : Nat.card I < Nat.card V) (t : I → V) :
    ∃ v : V, ∀ i, v + t i ≠ 0 := by
  by_contra h
  push Not at h
  have hsurjective : Function.Surjective (fun i : I ↦ -t i) := by
    intro v
    obtain ⟨i, hi⟩ := h v
    exact ⟨i, (add_eq_zero_iff_eq_neg.mp hi).symm⟩
  exact (not_le_of_gt hcard)
    (Nat.card_le_card_of_surjective _ hsurjective)

/-- All-dimensional fixed-point-free translated-palette theorem.

If the number of prescribed actions is smaller than the finite module, then
arbitrary translations have a common regular point. -/
theorem exists_common_regular_translate_of_fixedPointFreeOffZero
    {I : Type uI} {R : Type uR} {V : Type uV}
    [Finite I] [Finite V]
    [Semiring R] [AddCommGroup V] [Module R V]
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : ∀ i, FixedPointFreeOffZero (H i))
    (hcard : Nat.card I < Nat.card V) (t : I → V) :
    ∃ v : V, ∀ i, MulAction.stabilizer (H i) (v + t i) = ⊥ := by
  obtain ⟨v, hv⟩ := exists_add_translates_ne_zero_of_natCard_lt hcard t
  exact ⟨v, fun i ↦
    stabilizer_eq_bot_of_fixedPointFreeOffZero_of_ne_zero (H i) (hH i) (hv i)⟩

/-- Active-index form of the fixed-point-free translated-palette theorem.
Only nontrivial acting groups consume forbidden points. -/
theorem exists_common_regular_translate_of_active_fixedPointFreeOffZero
    {I : Type uI} {R : Type uR} {V : Type uV}
    [Fintype I] [Finite V]
    [Semiring R] [AddCommGroup V] [Module R V]
    (H : I → Subgroup (LinearMap.GeneralLinearGroup R V))
    (hH : ∀ i ∈ activeLinearIndices H, FixedPointFreeOffZero (H i))
    (hcard : (activeLinearIndices H).card < Nat.card V)
    (t : I → V) :
    ∃ v : V, ∀ i, MulAction.stabilizer (H i) (v + t i) = ⊥ := by
  let J := {i // i ∈ activeLinearIndices H}
  have hJcard : Nat.card J < Nat.card V := by
    simpa only [J, Nat.card_eq_finsetCard] using hcard
  obtain ⟨v, hv⟩ :=
    exists_common_regular_translate_of_fixedPointFreeOffZero
      (fun i : J ↦ H i.1) (fun i ↦ hH i.1 i.2) hJcard
        (fun i : J ↦ t i.1)
  refine ⟨v, fun i ↦ ?_⟩
  by_cases hi : i ∈ activeLinearIndices H
  · exact hv ⟨i, hi⟩
  · have hbot : H i = ⊥ := by
      simpa only [activeLinearIndices, Finset.mem_filter,
        Finset.mem_univ, true_and, not_ne_iff] using hi
    rw [hbot]
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g _hg
    apply Subtype.ext
    exact g.2

/-! ## Prime-field vector-space specializations -/

/-- Cardinal-specialized fixed-point-free palette theorem on
`(ZMod r)^d`: fewer than `r^d` actions have a common regular translate. -/
theorem exists_common_regular_translate_of_fixedPointFreeOffZero_zmod
    {I : Type uI} [Finite I]
    (r d : ℕ) (hr : Nat.Prime r)
    (H : I → Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (hH : ∀ i, FixedPointFreeOffZero (H i))
    (hcard : Nat.card I < r ^ d)
    (t : I → Fin d → ZMod r) :
    ∃ v, ∀ i, MulAction.stabilizer (H i) (v + t i) = ⊥ := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : NeZero r := ⟨hr.ne_zero⟩
  apply exists_common_regular_translate_of_fixedPointFreeOffZero H hH
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] using hcard

/-- Active-index cardinal specialization on `(ZMod r)^d`.  Only nontrivial
actions count toward the strict `r^d` palette bound. -/
theorem exists_common_regular_translate_of_active_fixedPointFreeOffZero_zmod
    {I : Type uI} [Fintype I]
    (r d : ℕ) (hr : Nat.Prime r)
    (H : I → Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    (hH : ∀ i ∈ activeLinearIndices H, FixedPointFreeOffZero (H i))
    (hcard : (activeLinearIndices H).card < r ^ d)
    (t : I → Fin d → ZMod r) :
    ∃ v, ∀ i, MulAction.stabilizer (H i) (v + t i) = ⊥ := by
  letI : Fact (Nat.Prime r) := ⟨hr⟩
  letI : NeZero r := ⟨hr.ne_zero⟩
  apply exists_common_regular_translate_of_active_fixedPointFreeOffZero H hH
  simpa only [Nat.card_fun, Nat.card_fin, Nat.card_zmod] using hcard

end LisiSabatini
