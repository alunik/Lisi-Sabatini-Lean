module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Perm.Support
public import Mathlib.Algebra.Group.Conj
public import Mathlib.Data.List.FinRange
public import Mathlib.Tactic.Group

/-!
# Centralizer invariants separating double cosets

If `z` centralizes `P` and `w` centralizes `Q`, then the conjugacy class of
`z * g * w * g⁻¹` is constant on the double coset `P * g * Q`. Any
conjugacy-invariant function of this word can therefore certify separation
of two double cosets.

For symmetric groups, fixed-point counts of powers give a directly
computable invariant. Their implementation scans `List.finRange n`; it
does not compute conjugacy classes or enumerate the symmetric group.
-/

@[expose] public section

namespace LisiSabatini

variable {G T : Type*} [Group G]

/-- The centralizer word used to distinguish double cosets. -/
def centralDoubleCosetWord (z w g : G) : G := z * g * w * g⁻¹

/-- Changing the double-coset representative conjugates the centralizer
word by the left multiplier. The two centralizers may be different. -/
theorem centralDoubleCosetWord_mul
    (P Q : Subgroup G) {z w a b : G}
    (hz : z ∈ Subgroup.centralizer (P : Set G))
    (hw : w ∈ Subgroup.centralizer (Q : Set G))
    (ha : a ∈ P) (hb : b ∈ Q) (g : G) :
    centralDoubleCosetWord z w (a * g * b) =
      a * centralDoubleCosetWord z w g * a⁻¹ := by
  have hza : z * a = a * z := (Subgroup.mem_centralizer_iff.mp hz a ha).symm
  have hbw : b * w = w * b := Subgroup.mem_centralizer_iff.mp hw b hb
  unfold centralDoubleCosetWord
  calc
    z * (a * g * b) * w * (a * g * b)⁻¹ =
        (z * a) * g * (b * w) * b⁻¹ * g⁻¹ * a⁻¹ := by group
    _ = (a * z) * g * (w * b) * b⁻¹ * g⁻¹ * a⁻¹ := by rw [hza, hbw]
    _ = a * (z * g * w * g⁻¹) * a⁻¹ := by group

/-- Every conjugacy-invariant function of the centralizer word is
constant under left multiplication by `P` and right multiplication by `Q`. -/
theorem centralDoubleCosetInvariant_mul
    (P Q : Subgroup G) (f : G → T)
    (hf : ∀ a x : G, f (a * x * a⁻¹) = f x) {z w a b : G}
    (hz : z ∈ Subgroup.centralizer (P : Set G))
    (hw : w ∈ Subgroup.centralizer (Q : Set G))
    (ha : a ∈ P) (hb : b ∈ Q) (g : G) :
    f (centralDoubleCosetWord z w (a * g * b)) =
      f (centralDoubleCosetWord z w g) := by
  rw [centralDoubleCosetWord_mul P Q hz hw ha hb, hf]

/-- Unequal invariant values give the same exact separation conclusion
as a checked list of failed subgroup-membership tests. -/
theorem doubleCoset_separated_of_centralInvariant_ne
    (P Q : Subgroup G) (f : G → T)
    (hf : ∀ a x : G, f (a * x * a⁻¹) = f x) {z w g h : G}
    (hz : z ∈ Subgroup.centralizer (P : Set G))
    (hw : w ∈ Subgroup.centralizer (Q : Set G))
    (hne : f (centralDoubleCosetWord z w g) ≠ f (centralDoubleCosetWord z w h)) :
    ∀ a ∈ P, g⁻¹ * a * h ∉ Q := by
  intro a ha hb
  let b := g⁻¹ * a * h
  have hbQ : b ∈ Q := hb
  have hh : h = a⁻¹ * g * b := by
    dsimp only [b]
    group
  have heq := centralDoubleCosetInvariant_mul P Q f hf hz hw (P.inv_mem ha) hbQ g
  rw [← hh] at heq
  exact hne heq.symm

/-- Count fixed points by a linear scan of the underlying finite set. -/
def permutationFixedCount {n : ℕ} (g : Equiv.Perm (Fin n)) : ℕ :=
  ((List.finRange n).filter fun i ↦ decide (g i = i)).length

/-- The computable list scan is the cardinal of the usual fixed-point
Finset. This bridge is used only in the invariant's correctness proof. -/
theorem permutationFixedCount_eq_card_filter {n : ℕ} (g : Equiv.Perm (Fin n)) :
    permutationFixedCount g = (Finset.univ.filter fun i ↦ g i = i).card := by
  calc
    permutationFixedCount g =
        ((List.finRange n).filter fun i ↦ decide (g i = i)).toFinset.card := by
      exact (List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _)).symm
    _ = (Finset.univ.filter fun i ↦ g i = i).card := by
      simp only [List.toFinset_filter, List.toFinset_finRange, decide_eq_true_eq]

/-- Conjugation bijects fixed points by relabeling the underlying set. -/
theorem permutationFixedCount_conj {n : ℕ} (a g : Equiv.Perm (Fin n)) :
    permutationFixedCount (a * g * a⁻¹) = permutationFixedCount g := by
  rw [permutationFixedCount_eq_card_filter, permutationFixedCount_eq_card_filter]
  apply Finset.card_equiv a.symm
  intro i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change a (g (a.symm i)) = i ↔ g (a.symm i) = a.symm i
  constructor
  · intro hi
    have h := congrArg a.symm hi
    simpa only [a.symm_apply_apply] using h
  · intro hi
    exact (congrArg a hi).trans (a.apply_symm_apply i)

/-- Fixed-point counts of powers remain conjugacy invariants. -/
theorem permutationFixedCount_pow_conj {n : ℕ}
    (a g : Equiv.Perm (Fin n)) (k : ℕ) :
    permutationFixedCount ((a * g * a⁻¹) ^ k) = permutationFixedCount (g ^ k) := by
  rw [conj_pow, permutationFixedCount_conj]

/-- A configurable finite list of fixed-point counts of powers. -/
def permutationFixedPowerProfile {n : ℕ}
    (powers : List ℕ) (g : Equiv.Perm (Fin n)) : List ℕ :=
  powers.map fun k ↦ permutationFixedCount (g ^ k)

theorem permutationFixedPowerProfile_conj {n : ℕ}
    (powers : List ℕ) (a g : Equiv.Perm (Fin n)) :
    permutationFixedPowerProfile powers (a * g * a⁻¹) =
      permutationFixedPowerProfile powers g := by
  simp only [permutationFixedPowerProfile, permutationFixedCount_pow_conj]

/-- A differing power profile certifies double-coset separation using
only directly evaluable finite lists of natural numbers. -/
theorem doubleCoset_separated_of_fixedPowerProfile_ne {n : ℕ}
    (P Q : Subgroup (Equiv.Perm (Fin n))) (powers : List ℕ)
    {z w g h : Equiv.Perm (Fin n)}
    (hz : z ∈ Subgroup.centralizer (P : Set _))
    (hw : w ∈ Subgroup.centralizer (Q : Set _))
    (hne : permutationFixedPowerProfile powers (centralDoubleCosetWord z w g) ≠
      permutationFixedPowerProfile powers (centralDoubleCosetWord z w h)) :
    ∀ a ∈ P, g⁻¹ * a * h ∉ Q :=
  doubleCoset_separated_of_centralInvariant_ne P Q (permutationFixedPowerProfile powers)
    (permutationFixedPowerProfile_conj powers) hz hw hne

/-- One inexpensive integer-valued double-coset invariant. -/
def centralFixedPowerInvariant {n : ℕ} (z w : Equiv.Perm (Fin n))
    (k : ℕ) (g : Equiv.Perm (Fin n)) : ℕ :=
  permutationFixedCount ((z * g * w * g⁻¹) ^ k)

/-- A fixed-power invariant is constant on `P`-`Q` double cosets when
its two parameters centralize the corresponding subgroups. -/
theorem centralFixedPowerInvariant_mul {n : ℕ}
    (P Q : Subgroup (Equiv.Perm (Fin n))) {z w a b : Equiv.Perm (Fin n)}
    (hz : z ∈ Subgroup.centralizer (P : Set _))
    (hw : w ∈ Subgroup.centralizer (Q : Set _))
    (ha : a ∈ P) (hb : b ∈ Q) (k : ℕ) (g : Equiv.Perm (Fin n)) :
    centralFixedPowerInvariant z w k (a * g * b) = centralFixedPowerInvariant z w k g :=
  centralDoubleCosetInvariant_mul P Q (fun x ↦ permutationFixedCount (x ^ k))
    (fun c x ↦ permutationFixedCount_pow_conj c x k) hz hw ha hb g

/-- A feature consists of the two centralizer parameters and a power. -/
abbrev CentralFixedPowerFeature (n : ℕ) :=
  Equiv.Perm (Fin n) × Equiv.Perm (Fin n) × ℕ

/-- A short, directly evaluable signature assembled from centralizer
fixed-power features. -/
def centralFixedPowerSignature {n : ℕ}
    (features : List (CentralFixedPowerFeature n)) (g : Equiv.Perm (Fin n)) : List ℕ :=
  features.map fun f ↦ centralFixedPowerInvariant f.1 f.2.1 f.2.2 g

/-- Each signature coordinate is invariant on the double coset. -/
theorem centralFixedPowerSignature_mul {n : ℕ}
    (P Q : Subgroup (Equiv.Perm (Fin n)))
    (features : List (CentralFixedPowerFeature n))
    (hfeatures : ∀ f ∈ features,
      f.1 ∈ Subgroup.centralizer (P : Set _) ∧
      f.2.1 ∈ Subgroup.centralizer (Q : Set _))
    {a b : Equiv.Perm (Fin n)} (ha : a ∈ P) (hb : b ∈ Q)
    (g : Equiv.Perm (Fin n)) :
    centralFixedPowerSignature features (a * g * b) = centralFixedPowerSignature features g := by
  unfold centralFixedPowerSignature
  apply List.map_congr_left
  intro f hf
  exact centralFixedPowerInvariant_mul P Q (hfeatures f hf).1 (hfeatures f hf).2 ha hb f.2.2 g

/-- Unequal short signatures separate whole double cosets. Equal
signatures make no assertion and may be handled by the negative-test
certificates instead. -/
theorem doubleCoset_separated_of_centralFixedPowerSignature_ne {n : ℕ}
    (P Q : Subgroup (Equiv.Perm (Fin n)))
    (features : List (CentralFixedPowerFeature n))
    (hfeatures : ∀ f ∈ features,
      f.1 ∈ Subgroup.centralizer (P : Set _) ∧
      f.2.1 ∈ Subgroup.centralizer (Q : Set _))
    {g h : Equiv.Perm (Fin n)}
    (hne : centralFixedPowerSignature features g ≠ centralFixedPowerSignature features h) :
    ∀ a ∈ P, g⁻¹ * a * h ∉ Q := by
  intro a ha hb
  let b := g⁻¹ * a * h
  have hbQ : b ∈ Q := hb
  have hh : h = a⁻¹ * g * b := by
    dsimp only [b]
    group
  have heq := centralFixedPowerSignature_mul P Q features hfeatures (P.inv_mem ha) hbQ g
  rw [← hh] at heq
  exact hne heq.symm

end LisiSabatini
