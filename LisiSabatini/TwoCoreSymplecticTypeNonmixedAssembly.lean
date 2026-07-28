module

public import LisiSabatini.TwoCoreSymplecticTypeMixedAssembly

/-!
# Assembly for the nonmixed maximal-class heads

The central half-turn in the cyclic rotation subgroup acts as `-1`.
Because the rotation subgroup is a cyclic `2`-group, this makes its action
on nonzero vectors free.  Hence its order divides the number of nonzero
vectors.  For a semidihedral head, the exact active-involution count is
half the rotation order, which immediately gives half-density.
-/

@[expose] public section

noncomputable section

open scoped commutatorElement

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

namespace BergerMaximalClassHead

variable {r d : ℕ} [Fact r.Prime]
  (P : Subgroup
    (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
  [Finite P]

set_option synthInstance.maxHeartbeats 100000 in
-- The nested subgroup action on the nonzero-vector subtype requires a
-- larger instance-synthesis budget than the default deterministic limit.
/-- The rotation subgroup of any maximal-class `2`-head acts freely on
the nonzero vectors when the center acts fixed-point-freely. -/
theorem rotationOrder_dvd_nonzero
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2)
    (head : BergerMaximalClassHead P)
    (C : CenterFixedPointFreeAction r d P) :
    head.rotationOrder ∣ r ^ d - 1 := by
  classical
  let V := Fin d → ZMod r
  let R := Subgroup.zpowers head.rotation
  letI : DistribMulAction R V :=
    { smul := fun g v => g.1.1.1 v
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun g => g.1.1.1.map_zero
      smul_add := fun g => g.1.1.1.map_add }
  letI : IsCyclic R := inferInstance
  have hRP : IsPGroup 2 R :=
    hP.to_subgroup R
  let zR : R :=
    ⟨head.halfTurn, by
      change
        head.rotation ^ (head.rotationOrder / 2) ∈
          Subgroup.zpowers head.rotation
      exact
        (Subgroup.zpowers head.rotation).pow_mem
          (Subgroup.mem_zpowers head.rotation) _⟩
  have hzRNe : zR ≠ 1 := by
    intro hz
    apply head.halfTurn_ne_one
    exact congrArg Subtype.val hz
  have hzRSq : zR ^ 2 = 1 := by
    apply Subtype.ext
    exact head.halfTurn_sq
  have hzROrder : orderOf zR = 2 := by
    apply orderOf_eq_prime
    · exact hzRSq
    · exact hzRNe
  let z : Subgroup.center P :=
    ⟨head.halfTurn, head.halfTurn_mem_center⟩
  have hzOperator :
      z.1.1.1 =
        -(1 : Module.End (ZMod r) V) :=
    centralInvolution_eq_neg_one_of_centerFixedPointFree
      P C z (by
        intro hz
        apply head.halfTurn_ne_one
        exact congrArg Subtype.val hz)
      (by
        apply Subtype.ext
        exact head.halfTurn_sq)
  have hzAction (v : V) :
      (zR • v : V) = -v := by
    change head.halfTurn.1.1 v = -v
    exact
      congrArg
        (fun T : Module.End (ZMod r) V => T v)
        hzOperator
  have htwo : (2 : ZMod r) ≠ 0 :=
    two_ne_zero_zmod_of_prime_ne_two
      (Fact.out : r.Prime) hrTwo
  have hnegFixed (v : V) (hv : -v = v) :
      v = 0 := by
    have hvadd : v + v = 0 := by
      calc
        v + v = -v + v := by rw [hv]
        _ = 0 := neg_add_cancel v
    have htwoSmul :
        (2 : ZMod r) • v = 0 := by
      simpa [two_smul (R := ZMod r)] using hvadd
    exact
      (smul_eq_zero.mp htwoSmul).resolve_left htwo
  let V0 := {v : V // v ≠ 0}
  letI : SMul R V0 :=
    ⟨fun g v ↦
      ⟨(g • v.1 : V), by
        intro hzero
        apply v.2
        apply MulAction.injective g
        exact hzero.trans (smul_zero g).symm⟩⟩
  letI : MulAction R V0 :=
    Subtype.coe_injective.mulAction
      (fun v : V0 ↦ (v.1 : V))
      (fun g v ↦ by
        change ((g • v : V0).1 : V) = (g • v.1 : V)
        rfl)
  letI : Finite V0 := inferInstance
  have hstab (v : V0) :
      MulAction.stabilizer R v = ⊥ := by
    have hvBase :
        MulAction.stabilizer R v.1 = ⊥ :=
      stabilizer_eq_bot_of_cyclic_twoGroup_of_involution_neg
        hRP zR hzROrder hzAction hnegFixed v.1 v.2
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    have hgBase :
        g ∈ MulAction.stabilizer R v.1 := by
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      exact congrArg Subtype.val hg
    rw [hvBase] at hgBase
    simpa using hgBase
  have hdiv :
      Nat.card R ∣ Nat.card V0 :=
    natCard_dvd_natCard_of_stabilizers_bot hstab
  have hRcard :
      Nat.card R = head.rotationOrder := by
    dsimp only [R]
    rw [Nat.card_zpowers, head.orderOf_rotation]
  have hVcard :
      Nat.card V = r ^ d := by
    simp only [V, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hV0card :
      Nat.card V0 = Nat.card V - 1 := by
    letI : Fintype V := Fintype.ofFinite V
    letI : Fintype V0 := Fintype.ofFinite V0
    rw [Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card]
    change
      Fintype.card {v : V // v ≠ 0} =
        Fintype.card V - 1
    calc
      Fintype.card {v : V // v ≠ 0} =
          Fintype.card V -
            Fintype.card {v : V // v = 0} :=
        Fintype.card_subtype_compl
          (fun v : V ↦ v = 0)
      _ = Fintype.card V - 1 := by
        simp
  rw [hRcard, hV0card, hVcard] at hdiv
  exact hdiv

end BergerMaximalClassHead

set_option synthInstance.maxHeartbeats 100000 in
-- The two nested subgroup actions need a larger deterministic
-- typeclass-synthesis budget.
set_option maxHeartbeats 1000000 in
-- The regular-orbit contradiction involves several nested action
-- structures and pointwise linear-map extensionality steps.
private theorem dihedral_rotationOrder_comparison
    {r d k : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2) (hd : 0 < d) (hk : 0 < k)
    (e : P ≃* DihedralGroup (4 * k))
    (C : CenterFixedPointFreeAction r d P) :
    4 * k ∣ r ^ d - 1 ∧
      2 * (4 * k) ≤ r ^ d - 1 := by
  classical
  letI : NeZero (4 * k) := ⟨by omega⟩
  let V := Fin d → ZMod r
  let a : P := e.symm (DihedralGroup.r 1)
  let b : P := e.symm (DihedralGroup.sr 0)
  let R := Subgroup.zpowers a
  letI : DistribMulAction P V :=
    { smul := fun g v => g.1.1 v
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun g => g.1.1.map_zero
      smul_add := fun g => g.1.1.map_add }
  letI : DistribMulAction R V :=
    { smul := fun g v => g.1.1.1 v
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun g => g.1.1.1.map_zero
      smul_add := fun g => g.1.1.1.map_add }
  letI : IsCyclic R := inferInstance
  have hRP : IsPGroup 2 R :=
    hP.to_subgroup R
  have haOrder : orderOf a = 4 * k := by
    dsimp only [a]
    rw [e.symm.orderOf_eq]
    exact DihedralGroup.orderOf_r_one
  let zP : P :=
    e.symm
      (DihedralGroup.r
        ((2 * k : ℕ) : ZMod (4 * k)))
  have hzPpow : a ^ (2 * k) = zP := by
    apply e.injective
    simp only [a, zP, e.apply_symm_apply,
      map_pow, DihedralGroup.r_one_pow, Nat.cast_mul]
  let zR : R :=
    ⟨zP, by
      rw [← hzPpow]
      exact
        (Subgroup.zpowers a).pow_mem
          (Subgroup.mem_zpowers a) _⟩
  have hzRNe : zR ≠ 1 := by
    intro hz
    apply DihedralGroup.r_two_mul_ne_one k hk
    have hzPone : zP = 1 :=
      congrArg Subtype.val hz
    have := congrArg e hzPone
    simpa [zP] using this
  have hzRSq : zR ^ 2 = 1 := by
    apply Subtype.ext
    apply e.injective
    simpa [zR, zP] using
      DihedralGroup.r_two_mul_sq k
  have hzROrder : orderOf zR = 2 := by
    apply orderOf_eq_prime
    · exact hzRSq
    · exact hzRNe
  let z : Subgroup.center P :=
    ⟨zP, by
      exact (MulEquivClass.apply_mem_center_iff e).mp
        (by
          simpa [zP] using
            DihedralGroup.r_two_mul_mem_center k)⟩
  have hzOperator :
      z.1.1.1 =
        -(1 : Module.End (ZMod r) V) :=
    centralInvolution_eq_neg_one_of_centerFixedPointFree
      P C z (by
        intro hz
        apply hzRNe
        apply Subtype.ext
        exact
          congrArg
            (fun q : Subgroup.center P => q.1) hz)
      (by
        apply Subtype.ext
        exact
          congrArg
            (fun q : R => q.1) hzRSq)
  have hzAction (v : V) :
      (zR • v : V) = -v := by
    change zP.1.1 v = -v
    exact
      congrArg
        (fun T : Module.End (ZMod r) V => T v)
        hzOperator
  have htwo : (2 : ZMod r) ≠ 0 :=
    two_ne_zero_zmod_of_prime_ne_two
      (Fact.out : r.Prime) hrTwo
  have hnegFixed (v : V) (hv : -v = v) :
      v = 0 := by
    have hvadd : v + v = 0 := by
      calc
        v + v = -v + v := by rw [hv]
        _ = 0 := neg_add_cancel v
    have htwoSmul :
        (2 : ZMod r) • v = 0 := by
      simpa [two_smul (R := ZMod r)] using hvadd
    exact
      (smul_eq_zero.mp htwoSmul).resolve_left htwo
  let V0 := {v : V // v ≠ 0}
  letI : SMul R V0 :=
    ⟨fun g v ↦
      ⟨(g • v.1 : V), by
        intro hzero
        apply v.2
        apply MulAction.injective g
        exact hzero.trans (smul_zero g).symm⟩⟩
  letI : MulAction R V0 :=
    Subtype.coe_injective.mulAction
      (fun v : V0 ↦ (v.1 : V))
      (fun g v ↦ by
        change ((g • v : V0).1 : V) = (g • v.1 : V)
        rfl)
  letI : Fintype R := Fintype.ofFinite R
  letI : Fintype V0 := Fintype.ofFinite V0
  have hstab (v : V0) :
      MulAction.stabilizer R v = ⊥ := by
    have hvBase :
        MulAction.stabilizer R v.1 = ⊥ :=
      stabilizer_eq_bot_of_cyclic_twoGroup_of_involution_neg
        hRP zR hzROrder hzAction hnegFixed v.1 v.2
    apply (Subgroup.eq_bot_iff_forall _).mpr
    intro g hg
    have hgBase :
        g ∈ MulAction.stabilizer R v.1 := by
      rw [MulAction.mem_stabilizer_iff] at hg ⊢
      exact congrArg Subtype.val hg
    rw [hvBase] at hgBase
    simpa using hgBase
  have hRcard :
      Fintype.card R = 4 * k := by
    rw [← Nat.card_eq_fintype_card, Nat.card_zpowers,
      haOrder]
  have hVcard :
      Nat.card V = r ^ d := by
    simp only [V, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hV0card :
      Fintype.card V0 = r ^ d - 1 := by
    letI : Fintype V := Fintype.ofFinite V
    rw [← Nat.card_eq_fintype_card]
    change
      Nat.card {v : V // v ≠ 0} = r ^ d - 1
    rw [show
      Nat.card {v : V // v ≠ 0} =
          Nat.card V - 1 by
        rw [Nat.card_eq_fintype_card,
          Nat.card_eq_fintype_card]
        change
          Fintype.card {v : V // v ≠ 0} =
            Fintype.card V - 1
        calc
          Fintype.card {v : V // v ≠ 0} =
              Fintype.card V -
                Fintype.card {v : V // v = 0} :=
            Fintype.card_subtype_compl
              (fun v : V ↦ v = 0)
          _ = Fintype.card V - 1 := by simp,
      hVcard]
  have hdiv :
      4 * k ∣ r ^ d - 1 := by
    have h :=
      natCard_dvd_natCard_of_stabilizers_bot hstab
    rw [Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, hRcard, hV0card] at h
    exact h
  have hpredPos : 0 < r ^ d - 1 := by
    have hrLePow : r ≤ r ^ d := by
      calc
        r = r ^ 1 := by simp
        _ ≤ r ^ d :=
          Nat.pow_le_pow_right (Fact.out : r.Prime).pos
            (by omega)
    have hrTwoLe := (Fact.out : r.Prime).two_le
    omega
  refine ⟨hdiv, ?_⟩
  by_contra htwoN
  have hlt : r ^ d - 1 < 2 * (4 * k) := by omega
  have hcardEq :
      4 * k = r ^ d - 1 := by
    obtain ⟨c, hc⟩ := hdiv
    have hcNe : c ≠ 0 := by
      intro hcZero
      subst c
      simp at hc
      omega
    have hcLt : c < 2 := by
      by_contra hcNot
      have htwoLe : 2 ≤ c := by omega
      have hmul :=
        Nat.mul_le_mul_left (4 * k) htwoLe
      rw [← hc] at hmul
      omega
    have hcOne : c = 1 := by omega
    subst c
    simpa using hc.symm
  let i0 : Fin d := ⟨0, hd⟩
  let v : V0 :=
    ⟨fun _ ↦ 1, by
      intro hv
      have := congrFun hv i0
      exact one_ne_zero this⟩
  let orbitMap : R → V0 := fun g ↦ g • v
  have horbitInjective :
      Function.Injective orbitMap := by
    intro g h hgh
    have hmem :
        h⁻¹ * g ∈ MulAction.stabilizer R v := by
      rw [MulAction.mem_stabilizer_iff]
      change g • v = h • v at hgh
      rw [mul_smul, hgh, inv_smul_smul]
    rw [hstab v] at hmem
    have hinvMul : h⁻¹ * g = 1 := by simpa using hmem
    exact (inv_mul_eq_one.mp hinvMul).symm
  have horbitCard :
      Fintype.card R = Fintype.card V0 := by
    rw [hRcard, hV0card, hcardEq]
  have horbitSurjective :
      Function.Surjective orbitMap :=
    ((Fintype.bijective_iff_injective_and_card orbitMap).2
      ⟨horbitInjective, horbitCard⟩).2
  let aR : R :=
    ⟨a, Subgroup.mem_zpowers a⟩
  let L : Module.End (ZMod r) V :=
    1 + a.1.1
  have hLne : L v.1 ≠ 0 := by
    intro hzero
    have hav : (aR • v.1 : V) = -v.1 := by
      apply eq_neg_of_add_eq_zero_left
      simpa [L, aR, add_comm] using hzero
    have haNeg (w : V) :
        (aR • w : V) = -w := by
      by_cases hw : w = 0
      · simp [hw]
      · obtain ⟨g, hg⟩ :=
          horbitSurjective ⟨w, hw⟩
        have hgv : (g • v.1 : V) = w :=
          congrArg Subtype.val hg
        calc
          (aR • w : V) =
              aR • (g • v.1) := by rw [hgv]
          _ = g • (aR • v.1) := by
            rw [← mul_smul, mul_comm, mul_smul]
          _ = g • (-v.1) := by rw [hav]
          _ = -(g • v.1) := map_neg g.1.1.1 v.1
          _ = -w := by rw [hgv]
    have haSq : a ^ 2 = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply LinearMap.ext
      intro w
      change aR • (aR • w) = w
      rw [haNeg, haNeg, neg_neg]
    have hadiv : 4 * k ∣ 2 := by
      rw [← haOrder]
      exact orderOf_dvd_iff_pow_eq_one.mpr haSq
    have := Nat.le_of_dvd (by omega : 0 < 2) hadiv
    omega
  let Lv : V0 := ⟨L v.1, hLne⟩
  obtain ⟨s, hs⟩ := horbitSurjective Lv
  have hsv : (s • v.1 : V) = L v.1 :=
    congrArg Subtype.val hs
  have hLpoint (w : V) :
      w + (a • w : V) = (s.1 • w : V) := by
    have hLs : L = s.1.1.1 := by
      apply LinearMap.ext
      intro u
      by_cases hu : u = 0
      · simp [hu, L]
      · obtain ⟨g, hg⟩ :=
          horbitSurjective ⟨u, hu⟩
        have hgu : (g • v.1 : V) = u :=
          congrArg Subtype.val hg
        calc
          L u = L (g • v.1) := by rw [hgu]
          _ = g • L v.1 := by
            change
              g • v.1 + aR • (g • v.1) =
                g • (v.1 + aR • v.1)
            rw [smul_add, ← mul_smul, mul_comm,
              mul_smul]
          _ = g • (s • v.1) := by rw [← hsv]
          _ = s • (g • v.1) := by
            rw [← mul_smul, mul_comm, mul_smul]
          _ = s.1.1.1 u := by
            rw [hgu]
            rfl
    have :=
      congrArg
        (fun T : Module.End (ZMod r) V => T w) hLs
    simpa [L] using this
  have hba :
      b * a = a⁻¹ * b := by
    apply e.injective
    simp [a, b]
  have hbs :
      b * s.1 = s.1⁻¹ * b := by
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.mp s.2
    rw [← hn]
    calc
      b * a ^ n =
          (b * a ^ n * b⁻¹) * b := by group
      _ = (b * a * b⁻¹) ^ n * b := by
        rw [conj_zpow]
      _ = (a⁻¹) ^ n * b := by
        congr 2
        calc
          b * a * b⁻¹ =
              (b * a) * b⁻¹ := by group
          _ = (a⁻¹ * b) * b⁻¹ := by rw [hba]
          _ = a⁻¹ := by group
      _ = (a ^ n)⁻¹ * b := by
        rw [inv_zpow]
  have hLinvPoint (w : V) :
      w + (a⁻¹ • w : V) =
        (s.1⁻¹ • w : V) := by
    let u : V := b⁻¹ • w
    have hbu : (b • u : V) = w := by
      simp [u]
    calc
      w + (a⁻¹ • w : V) =
          b • u + a⁻¹ • (b • u) := by rw [hbu]
      _ = b • u + b • (a • u) := by
        have h :=
          congrArg (fun x : P ↦ (x • u : V)) hba
        simpa [mul_smul] using h.symm
      _ = b • (u + a • u) := by
        rw [smul_add]
      _ = b • (s.1 • u) := by rw [hLpoint]
      _ = s.1⁻¹ • (b • u) := by
        have h :=
          congrArg (fun x : P ↦ (x • u : V)) hbs
        simpa [mul_smul] using h
      _ = s.1⁻¹ • w := by rw [hbu]
  have hpoly (w : V) :
      w + (a • w : V) + (a⁻¹ • w : V) = 0 := by
    have happly :=
      congrArg (fun u : V ↦ (s.1 • u : V))
        (hLinvPoint w)
    change
      s.1 • (w + a⁻¹ • w) =
        s.1 • (s.1⁻¹ • w) at happly
    rw [smul_add, smul_inv_smul] at happly
    rw [← hLpoint w,
      ← hLpoint (a⁻¹ • w)] at happly
    simp only [smul_inv_smul] at happly
    have htwoSum :
        (w + a • w) + (a⁻¹ • w + w) = w :=
      happly
    linear_combination htwoSum
  have haCube : a ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro w
    have h1 := hpoly (a • w)
    have h2 := hpoly (a • (a • w))
    simp only [inv_smul_smul] at h1 h2
    change
      a • (a • (a • w)) = w
    linear_combination h2 - h1
  have hadiv : 4 * k ∣ 3 := by
    rw [← haOrder]
    exact orderOf_dvd_iff_pow_eq_one.mpr haCube
  have := Nat.le_of_dvd (by omega : 0 < 3) hadiv
  omega

/-- The cyclic rotation subgroup in a pure dihedral core acts freely on
nonzero vectors, so its order divides the number of nonzero vectors. -/
theorem dihedral_rotationOrder_dvd_nonzero
    {r d k : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2) (hd : 0 < d) (hk : 0 < k)
    (e : P ≃* DihedralGroup (4 * k))
    (C : CenterFixedPointFreeAction r d P) :
    4 * k ∣ r ^ d - 1 :=
  (dihedral_rotationOrder_comparison
    P hP hrTwo hd hk e C).1

/-- A pure dihedral rotation subgroup cannot be transitive on the
nonzero vectors of an odd-characteristic module.  Consequently two
full rotation orbits fit among the nonzero vectors. -/
theorem dihedral_rotationOrder_two_le_nonzero
    {r d k : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Finite P]
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2) (hd : 0 < d) (hk : 0 < k)
    (e : P ≃* DihedralGroup (4 * k))
    (C : CenterFixedPointFreeAction r d P) :
    2 * (4 * k) ≤ r ^ d - 1 :=
  (dihedral_rotationOrder_comparison
    P hP hrTwo hd hk e C).2

/-- The central half-turn in a dihedral presentation is a commutator. -/
private theorem dihedral_halfTurn_mem_commutator
    {P : Type*} [Group P]
    {k : ℕ}
    (e : P ≃* DihedralGroup (4 * k)) :
    e.symm
        (DihedralGroup.r
          ((2 * k : ℕ) : ZMod (4 * k))) ∈
      commutator P := by
  let x :=
    e.symm
      (DihedralGroup.sr (0 : ZMod (4 * k)))
  let y :=
    e.symm
      (DihedralGroup.r
        ((k : ℕ) : ZMod (4 * k)))
  let z :=
    e.symm
      (DihedralGroup.r
        ((2 * k : ℕ) : ZMod (4 * k)))
  have hcycle :
      x * y = z * y * x := by
    apply e.injective
    simpa [x, y, z] using
      DihedralGroup.reflection_centralInvolutionCycle
        k (0 : ZMod (4 * k))
  have hz : z = ⁅x, y⁆ := by
    rw [commutatorElement_def]
    calc
      z = z * y * x * x⁻¹ * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [hcycle]
  rw [show
    e.symm
        (DihedralGroup.r
          ((2 * k : ℕ) : ZMod (4 * k))) = z by rfl, hz]
  exact
    Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)

/-- The central half-turn in a semidihedral presentation is a commutator. -/
private theorem semidihedral_halfTurn_mem_commutator
    {P : Type*} [Group P]
    {k : ℕ}
    (presentation : IsSemidihedralPresentation P k) :
    presentation.rotation
        ((4 * k : ℕ) : ZMod (8 * k)) ∈
      commutator P := by
  let x := presentation.coset (0 : ZMod (8 * k))
  let y :=
    presentation.rotation
      ((2 * k : ℕ) : ZMod (8 * k))
  let z :=
    presentation.rotation
      ((4 * k : ℕ) : ZMod (8 * k))
  have hcycle :
      x * y = z * y * x := by
    simpa [x, y, z] using
      presentation.coset_centralInvolutionCycle
        (0 : ZMod (8 * k))
  have hz : z = ⁅x, y⁆ := by
    rw [commutatorElement_def]
    calc
      z = z * y * x * x⁻¹ * y⁻¹ := by group
      _ = x * y * x⁻¹ * y⁻¹ := by rw [hcycle]
  rw [show
    presentation.rotation
        ((4 * k : ℕ) : ZMod (8 * k)) = z by rfl, hz]
  exact
    Subgroup.commutator_mem_commutator
      (Subgroup.mem_top x) (Subgroup.mem_top y)

/-- A pure dihedral mapped `2`-core satisfies both half-density
estimates. -/
theorem dihedral_halfDensity
    {r d k : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2) (hd : 0 < d) (hk : 0 < k)
    (e : P ≃* DihedralGroup (4 * k))
    (C : CenterFixedPointFreeAction r d P) :
    2 * (activePrimeOrderElements 2 P).card ≤
        r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d := by
  have hrotationLe :
      2 * (4 * k) ≤ r ^ d - 1 :=
    dihedral_rotationOrder_two_le_nonzero
      P hP hrTwo hd hk e C
  have hactive :=
    card_activePrimeOrderElements_two_le_of_dihedral
      (by omega) P e C
  have hdeven : Even d := by
    let zP : P :=
      e.symm
        (DihedralGroup.r
          ((2 * k : ℕ) : ZMod (4 * k)))
    let z : Subgroup.center P :=
      ⟨zP, by
        exact (MulEquivClass.apply_mem_center_iff e).mp
          (by
            simpa [zP] using
              DihedralGroup.r_two_mul_mem_center k)⟩
    apply
      even_dimension_of_centralInvolution_mem_commutator
        hrTwo P C z
    · intro hz
      apply DihedralGroup.r_two_mul_ne_one k hk
      have hzP : zP = 1 :=
        congrArg
          (fun q : Subgroup.center P => q.1) hz
      have := congrArg e hzP
      simpa [zP] using this
    · apply Subtype.ext
      apply e.injective
      simpa [z, zP] using
        DihedralGroup.r_two_mul_sq k
    · exact dihedral_halfTurn_mem_commutator e
  constructor
  · exact
      (Nat.mul_le_mul_left 2 hactive).trans
        hrotationLe
  · intro g hg
    exact
      activeInvolution_fixedVectorSet_sq_le_of_dihedral
        hdeven hk P e C g hg

/-- A pure semidihedral mapped `2`-core satisfies both half-density
estimates. -/
theorem semidihedral_halfDensity
    {r d k : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hP : IsPGroup 2 P)
    (hrTwo : r ≠ 2) (hd : 0 < d) (hk : 0 < k)
    (presentation : IsSemidihedralPresentation P k)
    (C : CenterFixedPointFreeAction r d P) :
    2 * (activePrimeOrderElements 2 P).card ≤
        r ^ d - 1 ∧
      ∀ g ∈ activePrimeOrderElements 2 P,
        (fixedVectorSet g.1).ncard *
            (fixedVectorSet g.1).ncard ≤
          r ^ d := by
  let head : BergerMaximalClassHead P :=
    .semidihedral k hk presentation
  have hrotationDvd :
      8 * k ∣ r ^ d - 1 := by
    simpa [head, BergerMaximalClassHead.rotationOrder] using
      head.rotationOrder_dvd_nonzero P hP hrTwo C
  have hpredPos : 0 < r ^ d - 1 := by
    have hrTwoLe := (Fact.out : r.Prime).two_le
    have hrLePow : r ≤ r ^ d := by
      calc
        r = r ^ 1 := by simp
        _ ≤ r ^ d :=
          Nat.pow_le_pow_right (Fact.out : r.Prime).pos
            (by omega)
    omega
  have hrotationLe :
      8 * k ≤ r ^ d - 1 :=
    Nat.le_of_dvd hpredPos hrotationDvd
  have hactive :=
    card_activePrimeOrderElements_two_le_of_semidihedral
      hk P presentation C
  have hdeven : Even d := by
    let z : Subgroup.center P :=
      ⟨presentation.rotation
          ((4 * k : ℕ) : ZMod (8 * k)),
        presentation.halfTurn_mem_center⟩
    apply
      even_dimension_of_centralInvolution_mem_commutator
        hrTwo P C z
    · intro hz
      apply presentation.halfTurn_ne_one hk
      exact congrArg Subtype.val hz
    · apply Subtype.ext
      exact presentation.halfTurn_sq
    · exact
        semidihedral_halfTurn_mem_commutator presentation
  constructor
  · calc
      2 * (activePrimeOrderElements 2 P).card ≤
          2 * (4 * k) :=
        Nat.mul_le_mul_left 2 hactive
      _ = 8 * k := by omega
      _ ≤ r ^ d - 1 := hrotationLe
  · intro g hg
    exact
      activeInvolution_fixedVectorSet_sq_le_of_semidihedral
        hdeven hk P presentation C g hg

end LisiSabatini
