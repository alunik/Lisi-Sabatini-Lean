import LisiSabatini.AffineTwoBaseTranslates
import LisiSabatini.TwoOrbitAvoidingCountCore

/-!
# Orbit reserve for affine two-base synchronization

Imprimitive propagation needs more than the existence of one common affine
two-base.  On the doubled module it needs a common regular point outside two
prescribed orbits of one distinguished component.  This file states that
recursive invariant and records the square-amplification estimate which
turns a one-point orbit reserve into the required two-point reserve.
-/

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uI uV

/-- The recursively stable strengthening of CATB: every admissible normal
prime-component family in the diagonal action on `V × V` has two-orbit
avoiding common affine regular translates. -/
def CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn
    (r : ℕ) (V : Type uV)
    [AddCommGroup V] [Module (ZMod r) V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)) : Prop :=
  ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
    (∀ i, Nat.Prime (p i)) →
    Function.Injective p →
    (∀ i, p i ≠ r) →
    ∀ H : I → Subgroup K,
      (∀ i, (H i).Normal) →
      (∀ i, IsPGroup (p i) (H i)) →
      TwoOrbitAvoidingCommonRegularTranslates
        (fun i ↦
          ((H i).map K.subtype).map
            (diagonalGeneralLinearHom (ZMod r) V))

/-- The two-orbit recursive invariant immediately implies ordinary CATB. -/
theorem
    CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.commonAffineTwoBaseTranslatesOn
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (h :
      CommonDiagonalAffineTwoOrbitAvoidingTranslatesOn.{uI}
        r V K) :
    CommonAffineTwoBaseTranslatesOn.{uI} r V K := by
  rw [commonAffineTwoBaseTranslatesOn_iff_diagonal]
  intro I _ p hp hinj hcross H hHnormal hHp t
  exact
    (h p hp hinj hcross H hHnormal hHp).commonRegularTranslates t

/-- Squaring a finite family amplifies a one-point reserve of one group
orbit into a two-point reserve for two group orbits. -/
private theorem sum_sq_add_two_mul_lt_sq_of_sum_add_lt
    {I : Type uI} [Fintype I]
    (n : I → ℕ) (C N : ℕ)
    (h : (∑ i, n i) + C < N) :
    (∑ i, n i * n i) + 2 * C < N * N := by
  let S := ∑ i, n i
  have hnLe (i : I) : n i ≤ S := by
    dsimp only [S]
    exact Finset.single_le_sum
      (fun j _ ↦ Nat.zero_le (n j)) (Finset.mem_univ i)
  have hsquares :
      (∑ i, n i * n i) ≤ S * S := by
    calc
      (∑ i, n i * n i) ≤ ∑ i, n i * S := by
        exact Finset.sum_le_sum fun i _ ↦
          Nat.mul_le_mul_left (n i) (hnLe i)
      _ = S * S := by
        rw [← Finset.sum_mul]
  have hstep : S + C + 1 ≤ N := by
    dsimp only [S]
    omega
  have hstrict :
      S * S + 2 * C < (S + C + 1) * (S + C + 1) := by
    nlinarith
  calc
    (∑ i, n i * n i) + 2 * C ≤ S * S + 2 * C :=
      Nat.add_le_add_right hsquares _
    _ < (S + C + 1) * (S + C + 1) := hstrict
    _ ≤ N * N := Nat.mul_le_mul hstep hstep

/-- A one-point common-regularity budget with one full group-orbit reserve
implies two-orbit avoidance for the diagonal two-point actions.

This bridge is deliberately stated for arbitrary finite linear subgroups.
The structural quasiprimitive arguments only have to prove the sharper
one-point budget on the right. -/
theorem
    twoOrbitAvoidingCommonRegularTranslates_diagonal_of_onePointReserve
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {I : Type uI} [Fintype I]
    (A : I →
      Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (hreserve : ∀ j₀,
      (∑ i, (nonregularVectors (A i)).ncard) +
          Nat.card (A j₀) <
        Nat.card V) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun i ↦
        (A i).map (diagonalGeneralLinearHom (ZMod r) V)) := by
  apply
    twoOrbitAvoidingCommonRegularTranslates_of_sum_ncard_add_two_mul_natCard_lt
  intro j₀
  let n : I → ℕ := fun i ↦ (nonregularVectors (A i)).ncard
  let N := Nat.card V
  let C := Nat.card (A j₀)
  have hsquare :
      (∑ i, n i * n i) + 2 * C < N * N :=
    sum_sq_add_two_mul_lt_sq_of_sum_add_lt n C N
      (by simpa [n, C, N] using hreserve j₀)
  have hbad (i : I) :
      (nonregularVectors
        ((A i).map
          (diagonalGeneralLinearHom (ZMod r) V))).ncard ≤
        n i * n i := by
    have hset :
        affineTwoBaseBadSet (A i) 0 0 =
          nonregularVectors
            ((A i).map
              (diagonalGeneralLinearHom (ZMod r) V)) := by
      ext z
      simpa using
        mem_affineTwoBaseBadSet_iff_mem_nonregularVectors_diagonal
          (A i) 0 0 z
    rw [← hset]
    exact ncard_affineTwoBaseBadSet_le_nonregular_sq (A i) 0 0
  have hsum :
      (∑ i,
        (nonregularVectors
          ((A i).map
            (diagonalGeneralLinearHom (ZMod r) V))).ncard) ≤
        ∑ i, n i * n i :=
    Finset.sum_le_sum fun i _ ↦ hbad i
  have hmapCard :
      Nat.card
          ((A j₀).map
            (diagonalGeneralLinearHom (ZMod r) V)) =
        C := by
    simpa [C] using
      Subgroup.card_map_of_injective
        (diagonalGeneralLinearHom_injective (ZMod r) V)
  rw [hmapCard, Nat.card_prod]
  exact (Nat.add_le_add_right hsum (2 * C)).trans_lt hsquare

/-- A regular point has a full-size orbit. -/
private theorem ncard_orbit_eq_natCard_of_stabilizer_eq_bot
    {R : Type*} {W : Type*}
    [Semiring R] [AddCommGroup W] [Module R W] [Finite W]
    (H : Subgroup (LinearMap.GeneralLinearGroup R W))
    (c : W) (hregular : MulAction.stabilizer H c = ⊥) :
    (MulAction.orbit H c).ncard = Nat.card H := by
  letI : Finite H := finite_linearSubgroup_of_finite H
  have hinjective : Function.Injective (fun g : H ↦ g • c) := by
    intro g h hgh
    change g • c = h • c at hgh
    let k : H := h⁻¹ * g
    have hkFix : k • c = c := by
      dsimp only [k]
      rw [mul_smul, hgh, inv_smul_smul]
    have hkMem : k ∈ MulAction.stabilizer H c :=
      MulAction.mem_stabilizer_iff.mpr hkFix
    have hkOne : k = 1 :=
      (Subgroup.eq_bot_iff_forall _).mp hregular k hkMem
    exact (inv_mul_eq_one.mp hkOne).symm
  rw [MulAction.orbit, ← Set.image_univ,
    Set.ncard_image_of_injective _ hinjective,
    Set.ncard_univ]

/-- It is equivalent in the square-amplification bridge to reserve one
actual orbit at every point.  The bad-set bound first supplies a common
regular point; its orbit then has the full group cardinality needed by the
preceding theorem. -/
theorem
    twoOrbitAvoidingCommonRegularTranslates_diagonal_of_onePointOrbitReserve
    {r : ℕ} {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {I : Type uI} [Fintype I]
    (A : I →
      Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    (hreserve : ∀ (j₀ : I) (c : V),
      (∑ i, (nonregularVectors (A i)).ncard) +
          (MulAction.orbit (A j₀) c).ncard <
        Nat.card V) :
    TwoOrbitAvoidingCommonRegularTranslates
      (fun i ↦
        (A i).map (diagonalGeneralLinearHom (ZMod r) V)) := by
  apply
    twoOrbitAvoidingCommonRegularTranslates_diagonal_of_onePointReserve A
  intro j₀
  have hsum :
      (∑ i, (nonregularVectors (A i)).ncard) < Nat.card V := by
    have h := hreserve j₀ 0
    omega
  obtain ⟨c, hc⟩ :=
    exists_avoids_of_sum_ncard_lt
      (fun i ↦ nonregularVectors (A i)) hsum
  have hregular : MulAction.stabilizer (A j₀) c = ⊥ := by
    simpa [nonregularVectors] using hc j₀
  have horbit :
      (MulAction.orbit (A j₀) c).ncard = Nat.card (A j₀) :=
    ncard_orbit_eq_natCard_of_stabilizer_eq_bot
      (A j₀) c hregular
  simpa only [horbit] using hreserve j₀ c

end LisiSabatini
