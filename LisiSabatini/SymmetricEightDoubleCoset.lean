module

public import LisiSabatini.SylowDoubleCosetBound
public import Mathlib.GroupTheory.DoubleCoset

/-!
# Double cosets with a prescribed Sylow-intersection size

The cardinal formula applies to arbitrary finite subgroups. Its minimum-two
specialization is the counting step needed for the Sylow 2-subgroups of S₈.
The finite S₈ witnesses and the proof that no trivial intersection exists are
separate hypotheses, not consequences of the counting argument.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace LisiSabatini

universe uG

private theorem mem_conjugate_subgroup_iff
    {G : Type uG} [Group G] (K : Subgroup G) (g z : G) :
    z ∈ MulAut.conj g • K ↔ g⁻¹ * z * g ∈ K := by
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (MulAut.conj g)⁻¹ z ∈ K ↔ _
  rw [MulAut.conj_inv_apply]

/-- The fiber of the double-coset parametrization is an intersection coset. -/
private def doubleCosetFiberEquiv
    {G : Type uG} [Group G] (H K : Subgroup G) (g : G) (a : H) (b : K) :
    ↥(H ⊓ MulAut.conj g • K) ≃
      {cd : H × K // (cd.1 : G) * g * (cd.2 : G) = (a : G) * g * (b : G)} where
  toFun z := ⟨(⟨(a : G) * z, H.mul_mem a.property z.property.1⟩,
    ⟨g⁻¹ * (z : G)⁻¹ * g * (b : G), K.mul_mem
      (by simpa only [mul_inv_rev, inv_inv, mul_assoc] using
        K.inv_mem ((mem_conjugate_subgroup_iff K g z).mp z.property.2)) b.property⟩),
    by dsimp; group⟩
  invFun cd := ⟨(a : G)⁻¹ * cd.val.1,
    H.mul_mem (H.inv_mem a.property) cd.val.1.property,
    (mem_conjugate_subgroup_iff K g _).mpr (by
      have heq : g⁻¹ * ((a : G)⁻¹ * (cd.val.1 : G)) * g =
          (b : G) * (cd.val.2 : G)⁻¹ := by
        calc
          _ = g⁻¹ * (a : G)⁻¹ * ((cd.val.1 : G) * g * (cd.val.2 : G)) *
              (cd.val.2 : G)⁻¹ := by group
          _ = g⁻¹ * (a : G)⁻¹ * ((a : G) * g * (b : G)) *
              (cd.val.2 : G)⁻¹ := by rw [cd.property]
          _ = _ := by group
      rw [heq]
      exact K.mul_mem b.property (K.inv_mem cd.val.2.property))⟩
  left_inv z := by apply Subtype.ext; dsimp; group
  right_inv cd := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext; dsimp; group
    · apply Subtype.ext
      dsimp
      have h := cd.property
      change (cd.val.1 : G) * g * (cd.val.2 : G) = (a : G) * g * (b : G) at h
      calc
        _ = g⁻¹ * (cd.val.1 : G)⁻¹ * ((a : G) * g * (b : G)) := by group
        _ = g⁻¹ * (cd.val.1 : G)⁻¹ * ((cd.val.1 : G) * g * (cd.val.2 : G)) :=
          congrArg (fun x : G ↦ g⁻¹ * (cd.val.1 : G)⁻¹ * x) h.symm
        _ = _ := by group

/-- Every fiber of the product parametrization has the intersection size. -/
private theorem card_doubleCoset_fiber
    {G : Type uG} [Group G] (H K : Subgroup G) (g : G)
    (y : DoubleCoset.doubleCoset g (H : Set G) K) :
    Nat.card {ab : H × K // (ab.1 : G) * g * (ab.2 : G) = (y : G)} =
      Nat.card ↥(H ⊓ MulAut.conj g • K) := by
  obtain ⟨a, ha, b, hb, hy⟩ := DoubleCoset.mem_doubleCoset.mp y.property
  simpa only [hy] using (Nat.card_congr (doubleCosetFiberEquiv H K g ⟨a, ha⟩ ⟨b, hb⟩)).symm

/-- Multiplicative double-coset cardinal formula, without division. -/
theorem card_doubleCoset_mul_card_inter
    {G : Type uG} [Group G] (H K : Subgroup G) [Finite H] [Finite K] (g : G) :
    Nat.card (DoubleCoset.doubleCoset g (H : Set G) K) *
      Nat.card ↥(H ⊓ MulAut.conj g • K) = Nat.card H * Nat.card K := by
  classical
  let f : H × K → DoubleCoset.doubleCoset g (H : Set G) K := fun ab ↦
    ⟨(ab.1 : G) * g * (ab.2 : G),
      DoubleCoset.mem_doubleCoset.mpr ⟨ab.1, ab.1.property, ab.2, ab.2.property, rfl⟩⟩
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨a, ha, b, hb, hy⟩ := DoubleCoset.mem_doubleCoset.mp y.property
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hy.symm⟩
  let : Finite (DoubleCoset.doubleCoset g (H : Set G) K) := Finite.of_surjective f hf
  let : Fintype (DoubleCoset.doubleCoset g (H : Set G) K) := Fintype.ofFinite _
  have hfib (y : DoubleCoset.doubleCoset g (H : Set G) K) :
      Nat.card {ab : H × K // f ab = y} = Nat.card ↥(H ⊓ MulAut.conj g • K) := by
    rw [← card_doubleCoset_fiber H K g y]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun ab ↦ Subtype.ext_iff
  have heq := Nat.card_congr (Equiv.sigmaFiberEquiv f)
  rw [Nat.card_sigma, Nat.card_prod] at heq
  simpa only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    ← Nat.card_eq_fintype_card] using heq

/-- The familiar quotient form $|HgK|=|H||K|/|H\cap gKg^{-1}|$. -/
theorem card_doubleCoset_eq_div_card_inter
    {G : Type uG} [Group G] (H K : Subgroup G) [Finite H] [Finite K] (g : G) :
    Nat.card (DoubleCoset.doubleCoset g (H : Set G) K) =
      Nat.card H * Nat.card K / Nat.card ↥(H ⊓ MulAut.conj g • K) := by
  have : Finite (H ⊓ MulAut.conj g • K : Subgroup G) :=
    Finite.of_injective (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective _)
  rw [← card_doubleCoset_mul_card_inter H K g, Nat.mul_div_cancel]
  exact Nat.card_pos (α := ↥(H ⊓ MulAut.conj g • K))

/-- Conjugators in one double coset have equal intersection cardinalities. -/
theorem card_inter_eq_of_mem_doubleCoset
    {G : Type uG} [Group G] (H K : Subgroup G) [Finite H] [Finite K]
    {g y : G} (hy : y ∈ DoubleCoset.doubleCoset g (H : Set G) K) :
    Nat.card ↥(H ⊓ MulAut.conj y • K) = Nat.card ↥(H ⊓ MulAut.conj g • K) := by
  have hg := card_doubleCoset_mul_card_inter H K g
  have hy' := card_doubleCoset_mul_card_inter H K y
  rw [DoubleCoset.doubleCoset_eq_of_mem hy] at hy'
  have hpos : 0 < Nat.card (DoubleCoset.doubleCoset g (H : Set G) K) := by
    apply Nat.pos_of_ne_zero
    intro hzero
    rw [hzero, zero_mul] at hg
    exact (Nat.mul_pos (Nat.card_pos (α := H)) (Nat.card_pos (α := K))).ne' hg.symm
  exact Nat.eq_of_mul_eq_mul_left hpos (hy'.trans hg.symm)

/-- A chosen cardinality-minimizing intersection is inclusion-minimal. -/
theorem isMinimalSylowInter_of_card_le
    {G : Type uG} [Group G] [Finite G] {p : ℕ} (P : Sylow p G) {g : G}
    (hmin : ∀ y : G, Nat.card (sylowInter P g) ≤ Nat.card (sylowInter P y)) :
    IsMinimalSylowInter P g := by
  intro y hy
  exact (Subgroup.eq_of_le_of_card_ge hy (hmin y)).symm.le

/-- A two-element intersection is minimal when every intersection is nontrivial. -/
theorem isMinimalSylowInter_of_card_two
    {G : Type uG} [Group G] [Finite G] {p : ℕ} (P : Sylow p G) {g : G}
    (hnontrivial : ∀ y : G, sylowInter P y ≠ ⊥)
    (hg : Nat.card (sylowInter P g) = 2) : IsMinimalSylowInter P g := by
  apply isMinimalSylowInter_of_card_le P
  intro y
  rw [hg]
  by_contra h
  exact hnontrivial y (Subgroup.eq_bot_of_card_le _ (by omega))

/-- A double coset lies in the fixed-cardinality stratum of Sylow intersections. -/
theorem card_sylowInter_eq_of_mem_doubleCoset
    {G : Type uG} [Group G] [Finite G] {p : ℕ} (P : Sylow p G)
    {g y : G} (hy : y ∈ DoubleCoset.doubleCoset g (P : Set G) P) :
    Nat.card (sylowInter P y) = Nat.card (sylowInter P g) := by
  simpa only [sylowInter, Sylow.coe_subgroup_smul] using
    card_inter_eq_of_mem_doubleCoset (P : Subgroup G) P hy

/-- A minimal cardinality stratum has at least the size of its double coset. -/
theorem card_div_card_inter_le_minimal_conjugators
    {G : Type uG} [Group G] [Finite G] {p : ℕ} (P : Sylow p G) {g : G}
    (hmin : ∀ y : G, Nat.card (sylowInter P g) ≤ Nat.card (sylowInter P y)) :
    Nat.card P * Nat.card P / Nat.card (sylowInter P g) ≤
      {y : G | IsMinimalSylowInter P y}.ncard := by
  have hsubset : DoubleCoset.doubleCoset g (P : Set G) P ⊆
      {y : G | IsMinimalSylowInter P y} := by
    intro y hy
    apply isMinimalSylowInter_of_card_le P
    intro z
    rw [card_sylowInter_eq_of_mem_doubleCoset P hy]
    exact hmin z
  have hcard := Set.ncard_le_ncard hsubset
  rw [← Nat.card_coe_set_eq] at hcard
  change Nat.card (DoubleCoset.doubleCoset g ((P : Subgroup G) : Set G)
    ((P : Subgroup G) : Set G)) ≤ _ at hcard
  rw [card_doubleCoset_eq_div_card_inter (P : Subgroup G) (P : Subgroup G) g] at hcard
  simpa only [sylowInter, Sylow.coe_subgroup_smul] using hcard

/-- At the S₈ Sylow-2 parameters, one size-two intersection gives at least
8192 minimal conjugators, provided all intersections are nontrivial. -/
theorem eight_sylow_two_minimal_conjugators_bound
    {G : Type uG} [Group G] [Finite G] (P : Sylow 2 G) {g : G}
    (hP : Nat.card P = 128)
    (hnontrivial : ∀ y : G, sylowInter P y ≠ ⊥)
    (hg : Nat.card (sylowInter P g) = 2) :
    8192 ≤ {y : G | IsMinimalSylowInter P y}.ncard := by
  have hmin (y : G) : Nat.card (sylowInter P g) ≤ Nat.card (sylowInter P y) := by
    rw [hg]
    by_contra h
    exact hnontrivial y (Subgroup.eq_bot_of_card_le _ (by omega))
  have h := card_div_card_inter_le_minimal_conjugators P hmin
  simpa only [hP, hg, Nat.reduceMul, Nat.reduceDiv] using h

/-- The complementary count at the degree-eight parameters. -/
theorem eight_sylow_two_bad_conjugators_bound
    {G : Type uG} [Group G] [Finite G] (P : Sylow 2 G) {g : G}
    (hP : Nat.card P = 128)
    (hnontrivial : ∀ y : G, sylowInter P y ≠ ⊥)
    (hg : Nat.card (sylowInter P g) = 2) :
    {y : G | ¬ IsMinimalSylowInter P y}.ncard + 8192 ≤ Nat.card G := by
  have hgood := eight_sylow_two_minimal_conjugators_bound P hP hnontrivial hg
  have hpartition := Set.ncard_add_ncard_compl {y : G | IsMinimalSylowInter P y}
  change {y : G | IsMinimalSylowInter P y}.ncard +
    {y : G | ¬ IsMinimalSylowInter P y}.ncard = Nat.card G at hpartition
  omega

/-- The degree-eight Sylow-2 failure density is at most $251/315$. -/
theorem eight_sylow_two_bad_probability_le
    {G : Type uG} [Group G] [Finite G] (P : Sylow 2 G) {g : G}
    (hG : Nat.card G = 40320) (hP : Nat.card P = 128)
    (hnontrivial : ∀ y : G, sylowInter P y ≠ ⊥)
    (hg : Nat.card (sylowInter P g) = 2) :
    ({y : G | ¬ IsMinimalSylowInter P y}.ncard : ℝ) / Nat.card G ≤ 251 / 315 := by
  have h := eight_sylow_two_bad_conjugators_bound P hP hnontrivial hg
  rw [hG] at h ⊢
  have hbad : {y : G | ¬ IsMinimalSylowInter P y}.ncard ≤ 32128 := by omega
  have hreal : ({y : G | ¬ IsMinimalSylowInter P y}.ncard : ℝ) ≤ 32128 := by
    exact_mod_cast hbad
  norm_num only [Nat.cast_ofNat]
  linarith

/-- Inclusion-minimality for two independently prescribed Sylow rows. -/
def IsMinimalMixedSylowInter
    {G : Type uG} [Group G] {p : ℕ} (P Q : Sylow p G) (x : G) : Prop :=
  ∀ y : G, mixedSylowInter P Q y ≤ mixedSylowInter P Q x →
    mixedSylowInter P Q x ≤ mixedSylowInter P Q y

/-- The mixed predicate restricts to the original conjecture's predicate. -/
theorem isMinimalMixedSylowInter_self_iff
    {G : Type uG} [Group G] {p : ℕ} (P : Sylow p G) (x : G) :
    IsMinimalMixedSylowInter P P x ↔ IsMinimalSylowInter P x := Iff.rfl

/-- Changing the two rows independently conjugates every intersection. -/
theorem mixedSylowInter_conjugate_rows
    {G : Type uG} [Group G] {p : ℕ}
    (P Q : Sylow p G) (a b x : G) :
    mixedSylowInter (a • P) (b • Q) (a * x * b⁻¹) =
      MulAut.conj a • mixedSylowInter P Q x := by
  have hsmul : (a * x * b⁻¹) • (b • Q) = a • (x • Q) := by
    rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one, mul_smul]
  rw [mixedSylowInter, hsmul, Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul,
    ← Subgroup.smul_inf]
  rfl

/-- Independent row changes preserve inclusion-minimality exactly. -/
theorem isMinimalMixedSylowInter_conjugate_rows_iff
    {G : Type uG} [Group G] {p : ℕ}
    (P Q : Sylow p G) (a b x : G) :
    IsMinimalMixedSylowInter (a • P) (b • Q) (a * x * b⁻¹) ↔
      IsMinimalMixedSylowInter P Q x := by
  constructor
  · intro h y hy
    have h' := h (a * y * b⁻¹)
    rw [mixedSylowInter_conjugate_rows, mixedSylowInter_conjugate_rows] at h'
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp
      (h' (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hy))
  · intro h y hy
    obtain ⟨z, rfl⟩ := ((Equiv.mulLeft a).trans (Equiv.mulRight b⁻¹)).surjective y
    change mixedSylowInter (a • P) (b • Q) (a * z * b⁻¹) ≤
      mixedSylowInter (a • P) (b • Q) (a * x * b⁻¹) at hy
    change mixedSylowInter (a • P) (b • Q) (a * x * b⁻¹) ≤
      mixedSylowInter (a • P) (b • Q) (a * z * b⁻¹)
    rw [mixedSylowInter_conjugate_rows, mixedSylowInter_conjugate_rows] at hy ⊢
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr
      (h z (Subgroup.pointwise_smul_le_pointwise_smul_iff.mp hy))

/-- The full-group count of minimal mixed conjugators is independent of both rows. -/
theorem ncard_minimal_mixed_conjugators_eq_reference
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q R : Sylow p G) :
    {x : G | IsMinimalMixedSylowInter P Q x}.ncard =
      {x : G | IsMinimalSylowInter R x}.ncard := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G R P
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G R Q
  symm
  apply Set.ncard_congr'
  apply ((Equiv.mulLeft a).trans (Equiv.mulRight b⁻¹)).subtypeEquiv
  intro x
  exact (isMinimalMixedSylowInter_conjugate_rows_iff R R a b x).symm

/-- The full-group count of nonminimal mixed conjugators is independent of both rows. -/
theorem ncard_nonminimal_mixed_conjugators_eq_reference
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P Q R : Sylow p G) :
    {x : G | ¬ IsMinimalMixedSylowInter P Q x}.ncard =
      {x : G | ¬ IsMinimalSylowInter R x}.ncard := by
  obtain ⟨a, rfl⟩ := MulAction.exists_smul_eq G R P
  obtain ⟨b, rfl⟩ := MulAction.exists_smul_eq G R Q
  symm
  apply Set.ncard_congr'
  apply ((Equiv.mulLeft a).trans (Equiv.mulRight b⁻¹)).subtypeEquiv
  intro x
  exact not_congr (isMinimalMixedSylowInter_conjugate_rows_iff R R a b x).symm

/-- Minimal-conjugator density can be checked at any one Sylow subgroup. -/
theorem ncard_minimal_sylow_conjugators_eq_reference
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P R : Sylow p G) :
    {x : G | IsMinimalSylowInter P x}.ncard =
      {x : G | IsMinimalSylowInter R x}.ncard :=
  ncard_minimal_mixed_conjugators_eq_reference P P R

/-- Nonminimal-conjugator density can be checked at any one Sylow subgroup. -/
theorem ncard_nonminimal_sylow_conjugators_eq_reference
    {G : Type uG} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P R : Sylow p G) :
    {x : G | ¬ IsMinimalSylowInter P x}.ncard =
      {x : G | ¬ IsMinimalSylowInter R x}.ncard :=
  ncard_nonminimal_mixed_conjugators_eq_reference P P R

/-- One reference Sylow-2 certificate gives the same bound for every mixed pair. -/
theorem eight_sylow_two_mixed_bad_probability_le_of_reference
    {G : Type uG} [Group G] [Finite G] (R P Q : Sylow 2 G) {g : G}
    (hG : Nat.card G = 40320) (hR : Nat.card R = 128)
    (hnontrivial : ∀ y : G, sylowInter R y ≠ ⊥)
    (hg : Nat.card (sylowInter R g) = 2) :
    ({y : G | ¬ IsMinimalMixedSylowInter P Q y}.ncard : ℝ) /
      Nat.card G ≤ 251 / 315 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [ncard_nonminimal_mixed_conjugators_eq_reference P Q R]
  exact eight_sylow_two_bad_probability_le R hG hR hnontrivial hg

/-- One reference Sylow-2 certificate gives the bound for every prescribed row. -/
theorem eight_sylow_two_bad_probability_le_of_reference
    {G : Type uG} [Group G] [Finite G] (R P : Sylow 2 G) {g : G}
    (hG : Nat.card G = 40320) (hR : Nat.card R = 128)
    (hnontrivial : ∀ y : G, sylowInter R y ≠ ⊥)
    (hg : Nat.card (sylowInter R g) = 2) :
    ({y : G | ¬ IsMinimalSylowInter P y}.ncard : ℝ) / Nat.card G ≤ 251 / 315 :=
  eight_sylow_two_mixed_bad_probability_le_of_reference R P P hG hR hnontrivial hg

end LisiSabatini
