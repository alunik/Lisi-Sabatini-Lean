module

public import LisiSabatini.EigenspaceCyclingBound

/-!
# Fixed-space cycles with operator-valued eigenvalues

The usual extraspecial fixed-space argument is often stated after a central
element has been diagonalized over the ground field.  That split scalar
description is unnecessary for the linear-algebra step.  This file proves an
operator-valued version.

Let `x` and the operators `z i` commute.  If every difference
`z i - z j`, for `i != j`, is injective, then the equalizer spaces

`ker (x - z i)`

are independent.  The proof is the operator Vandermonde argument in a form
which does not require writing down a product: apply `x - z i` to a relation,
use induction on its finite support, and cancel `z j - z i` on every remaining
summand.  Iterating this isolates all summands exactly as the product
`prod (x - z j)` would.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uK uV uI

open scoped DirectSum

@[simp]
theorem generalLinearEnd_one
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V] :
    generalLinearEnd
      (1 : LinearMap.GeneralLinearGroup K V) = 1 :=
  map_one (Units.coeHom (Module.End K V))

@[simp]
theorem generalLinearEnd_mul
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (g h : LinearMap.GeneralLinearGroup K V) :
    generalLinearEnd (g * h) = generalLinearEnd g * generalLinearEnd h :=
  map_mul (Units.coeHom (Module.End K V)) g h

@[simp]
theorem generalLinearEnd_pow
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (g : LinearMap.GeneralLinearGroup K V) (n : ℕ) :
    generalLinearEnd (g ^ n) = (generalLinearEnd g) ^ n :=
  map_pow (Units.coeHom (Module.End K V)) g n

/-- A power of an operator of finite multiplicative order is injective.  No
finite-dimensional hypothesis is needed. -/
theorem end_pow_injective_of_pow_eq_one
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (z : Module.End K V) {q n : ℕ} (hzq : z ^ q = 1) (hn : n ≤ q) :
    Function.Injective (z ^ n) := by
  intro a b hab
  have happly := congrArg (fun v ↦ (z ^ (q - n)) v) hab
  change (z ^ (q - n)) ((z ^ n) a) =
    (z ^ (q - n)) ((z ^ n) b) at happly
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add,
    Nat.sub_add_cancel hn, hzq, Module.End.one_apply,
    Module.End.one_apply] at happly
  exact happly

/-- If all nontrivial powers below the order have fixed-point-free
difference from the identity, then a larger power minus a smaller power is
injective. -/
theorem end_pow_sub_pow_injective_of_pow_eq_one
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (z : Module.End K V) {q i j : ℕ}
    (hzq : z ^ q = 1)
    (hfree : ∀ k, 0 < k → k < q →
      Function.Injective (z ^ k - (1 : Module.End K V)))
    (hi : i < q) (hji : j < i) :
    Function.Injective (z ^ i - z ^ j) := by
  have hjq : j ≤ q := (hji.trans hi).le
  have hkpos : 0 < i - j := Nat.sub_pos_of_lt hji
  have hklt : i - j < q := (Nat.sub_le i j).trans_lt hi
  have hfactor : z ^ j * (z ^ (i - j) - 1) = z ^ i - z ^ j := by
    rw [mul_sub, mul_one, ← pow_add, Nat.add_sub_of_le hji.le]
  intro a b hab
  rw [← hfactor] at hab
  have hab' : (z ^ j) ((z ^ (i - j) - 1) a) =
      (z ^ j) ((z ^ (i - j) - 1) b) := by
    simpa only [Module.End.mul_apply] using hab
  exact hfree (i - j) hkpos hklt
    (end_pow_injective_of_pow_eq_one z hzq hjq hab')

/-- Under the finite-order/fixed-point-free hypotheses, distinct powers of
an operator have injective difference. -/
theorem pairwise_injective_end_pow_sub_of_pow_eq_one
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (z : Module.End K V) {q : ℕ}
    (hzq : z ^ q = 1)
    (hfree : ∀ k, 0 < k → k < q →
      Function.Injective (z ^ k - (1 : Module.End K V))) :
    Pairwise (fun i j : Fin q ↦
      Function.Injective (z ^ (i : ℕ) - z ^ (j : ℕ))) := by
  intro i j hij
  have hval : (i : ℕ) ≠ (j : ℕ) := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hij' | hji'
  · have hrev := end_pow_sub_pow_injective_of_pow_eq_one z hzq hfree
      j.isLt hij'
    intro a b hab
    apply hrev
    have habneg := congrArg Neg.neg hab
    simpa only [LinearMap.sub_apply, neg_sub] using habneg
  · exact end_pow_sub_pow_injective_of_pow_eq_one z hzq hfree i.isLt hji'

/-- Iterating the relation `x * y = z * y * x` produces an operator-valued
eigenvalue cycle.  Centrality is needed only in the form `z * y = y * z`. -/
theorem end_mul_pow_cycle
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (x y z : Module.End K V)
    (hxy : x * y = z * y * x) (hzy : Commute z y) :
    ∀ n : ℕ, x * y ^ n = z ^ n * y ^ n * x := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        x * y ^ (n + 1) = (x * y ^ n) * y := by
          rw [pow_succ, mul_assoc]
        _ = (z ^ n * y ^ n * x) * y := by rw [ih]
        _ = z ^ n * y ^ n * (x * y) := by simp only [mul_assoc]
        _ = z ^ n * y ^ n * (z * y * x) := by rw [hxy]
        _ = z ^ n * (y ^ n * z) * y * x := by
          simp only [mul_assoc]
        _ = z ^ n * (z * y ^ n) * y * x := by
          rw [(hzy.symm.pow_left n).eq]
        _ = z ^ (n + 1) * y ^ (n + 1) * x := by
          rw [pow_succ, pow_succ]
          simp only [mul_assoc]

/-- Powers of an injective endomorphism remain injective. -/
theorem end_pow_injective_of_injective
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (y : Module.End K V) (hy : Function.Injective y) :
    ∀ n : ℕ, Function.Injective (y ^ n) := by
  intro n
  induction n with
  | zero =>
      intro a b hab
      simpa only [pow_zero, Module.End.one_apply] using hab
  | succ n ih =>
      intro a b hab
      apply hy
      apply ih
      simpa only [pow_succ, Module.End.mul_apply] using hab

/-- Injectivity of `z - 1` is exactly fixed-point-freeness away from zero.
This reformulation is convenient when the central operator comes from a
group action. -/
theorem end_sub_one_injective_iff_fixedPointFree
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (z : Module.End K V) :
    Function.Injective (z - (1 : Module.End K V)) ↔
      ∀ v : V, z v = v → v = 0 := by
  constructor
  · intro hinj v hv
    apply hinj
    simp only [LinearMap.sub_apply, hv, Module.End.one_apply, sub_self,
      map_zero]
  · intro hfixed a b hab
    apply sub_eq_zero.mp
    apply hfixed (a - b)
    have hzero : (z - 1) (a - b) = 0 := by
      rw [map_sub, hab, sub_self]
    simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hzero

/-- The `i`-th translate of the fixed space of `x` under `y`. -/
def operatorFixedCycleSubspace
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (x y : Module.End K V) (i : ℕ) : Submodule K V :=
  (LinearMap.ker (x - 1)).map (y ^ i)

/-- The commutation cycle sends the `i`-th translated fixed space into the
operator-valued eigenspace `ker (x - z^i)`. -/
theorem operatorFixedCycleSubspace_le_ker_sub_pow
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (x y z : Module.End K V)
    (hxy : x * y = z * y * x) (hzy : Commute z y) (i : ℕ) :
    operatorFixedCycleSubspace x y i ≤ LinearMap.ker (x - z ^ i) := by
  rintro w ⟨v, hv, rfl⟩
  rw [LinearMap.mem_ker]
  have hvx : x v = v := by
    have hvann : (x - 1) v = 0 := LinearMap.mem_ker.mp hv
    simpa only [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] using hvann
  have hcycle_apply : x ((y ^ i) v) = (z ^ i) ((y ^ i) (x v)) := by
    have hcycle := end_mul_pow_cycle x y z hxy hzy i
    have happly := congrArg (fun f : Module.End K V ↦ f v) hcycle
    simpa only [Module.End.mul_apply] using happly
  simp only [LinearMap.sub_apply, hcycle_apply, hvx, sub_self]

/-- Operator-valued eigenspaces are independent when the operators commute
with the common left-hand operator and have injective pairwise differences.

This is an abstract, nonsplit replacement for independence of eigenspaces
with distinct scalar eigenvalues. -/
theorem iSupIndep_ker_sub_of_commute_of_injective_sub
    {K : Type uK} {V : Type uV} {I : Type uI}
    [Field K] [AddCommGroup V] [Module K V]
    (x : Module.End K V) (z : I → Module.End K V)
    (hxz : ∀ i, Commute x (z i))
    (hzz : Pairwise (fun i j ↦ Commute (z i) (z j)))
    (hinj : Pairwise (fun i j ↦ Function.Injective (z i - z j))) :
    iSupIndep (fun i ↦ LinearMap.ker (x - z i)) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro v _hv _hsum i hi
      simp at hi
  | @insert i s hi ih =>
      intro v hv hsum k hk
      have hvi_mem : v i ∈ LinearMap.ker (x - z i) :=
        hv i (Finset.mem_insert_self i s)
      have hvi_ann : (x - z i) (v i) = 0 :=
        LinearMap.mem_ker.mp hvi_mem
      have hsep_sum : ∑ j ∈ s, (x - z i) (v j) = 0 := by
        have happly := congrArg (fun w ↦ (x - z i) w) hsum
        rw [Finset.sum_insert hi] at happly
        change (x - z i) (v i + ∑ j ∈ s, v j) = (x - z i) 0 at happly
        rw [map_add, hvi_ann, zero_add, map_sum, map_zero] at happly
        exact happly
      have hrewrite (j : I) (hj : j ∈ s) :
          (x - z i) (v j) = (z j - z i) (v j) := by
        have hvj_mem : v j ∈ LinearMap.ker (x - z j) :=
          hv j (Finset.mem_insert_of_mem hj)
        have hvj_ann : (x - z j) (v j) = 0 :=
          LinearMap.mem_ker.mp hvj_mem
        have hxv : x (v j) = z j (v j) := by
          simpa [LinearMap.sub_apply, sub_eq_zero] using hvj_ann
        simp only [LinearMap.sub_apply, hxv]
      have htransformed_sum : ∑ j ∈ s, (z j - z i) (v j) = 0 := by
        calc
          ∑ j ∈ s, (z j - z i) (v j) =
              ∑ j ∈ s, (x - z i) (v j) := by
                apply Finset.sum_congr rfl
                intro j hj
                exact (hrewrite j hj).symm
          _ = 0 := hsep_sum
      have htransformed_mem (j : I) (hj : j ∈ s) :
          (z j - z i) (v j) ∈ LinearMap.ker (x - z j) := by
        rw [LinearMap.mem_ker]
        have hji : j ≠ i := by
          intro hji
          subst j
          exact hi hj
        have hcomm_x : Commute x (z j - z i) :=
          (hxz j).sub_right (hxz i)
        have hcomm_zj : Commute (z j) (z j - z i) :=
          (Commute.refl (z j)).sub_right (hzz hji)
        have hcomm : Commute (x - z j) (z j - z i) :=
          hcomm_x.sub_left hcomm_zj
        have hvj_ann : (x - z j) (v j) = 0 :=
          LinearMap.mem_ker.mp (hv j (Finset.mem_insert_of_mem hj))
        rw [← Module.End.mul_apply, hcomm.eq, Module.End.mul_apply,
          hvj_ann, map_zero]
      have hrest_zero : ∀ j ∈ s, v j = 0 := by
        have hzero := ih (fun j ↦ (z j - z i) (v j))
          htransformed_mem htransformed_sum
        intro j hj
        have hji : j ≠ i := by
          intro hji
          subst j
          exact hi hj
        apply hinj hji
        simpa using hzero j hj
      rcases Finset.mem_insert.mp hk with rfl | hk
      · rw [Finset.sum_insert hi] at hsum
        simpa [Finset.sum_eq_zero hrest_zero] using hsum
      · exact hrest_zero k hk

/-- The translated fixed spaces in a nonsplit operator cycle are independent.
The only spectral hypothesis is that every nontrivial power of `z` has
injective difference from the identity. -/
theorem iSupIndep_operatorFixedCycleSubspace
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    (x y z : Module.End K V) {q : ℕ}
    (hxy : x * y = z * y * x)
    (hxz : Commute x z) (hzy : Commute z y)
    (hzq : z ^ q = 1)
    (hfree : ∀ k, 0 < k → k < q →
      Function.Injective (z ^ k - (1 : Module.End K V))) :
    iSupIndep (fun i : Fin q ↦
      operatorFixedCycleSubspace x y (i : ℕ)) := by
  have hker : iSupIndep (fun i : Fin q ↦
      LinearMap.ker (x - z ^ (i : ℕ))) := by
    apply iSupIndep_ker_sub_of_commute_of_injective_sub x
      (fun i : Fin q ↦ z ^ (i : ℕ))
    · intro i
      exact hxz.pow_right (i : ℕ)
    · intro i j _hij
      exact Commute.pow_pow_self z (i : ℕ) (j : ℕ)
    · exact pairwise_injective_end_pow_sub_of_pow_eq_one z hzq hfree
  apply hker.mono
  intro i
  exact operatorFixedCycleSubspace_le_ker_sub_pow x y z hxy hzy (i : ℕ)

/-- Dimension form of the nonsplit operator-cycle bound.  Invertibility of
`y` is used only through injectivity, to ensure that every translated fixed
space has the same dimension as the original one. -/
theorem mul_finrank_ker_sub_one_le_of_operator_cycle
    {K : Type uK} {V : Type uV}
    [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (x y z : Module.End K V) {q : ℕ}
    (hy : Function.Injective y)
    (hxy : x * y = z * y * x)
    (hxz : Commute x z) (hzy : Commute z y)
    (hzq : z ^ q = 1)
    (hfree : ∀ k, 0 < k → k < q →
      Function.Injective (z ^ k - (1 : Module.End K V))) :
    q * Module.finrank K (LinearMap.ker (x - 1)) ≤
      Module.finrank K V := by
  classical
  let E : Fin q → Submodule K V := fun i ↦
    operatorFixedCycleSubspace x y (i : ℕ)
  have hind : iSupIndep E :=
    iSupIndep_operatorFixedCycleSubspace x y z hxy hxz hzy hzq hfree
  let inclusion : (⨁ i : Fin q, E i) →ₗ[K] V :=
    DirectSum.coeLinearMap E
  have hinclusion : Function.Injective inclusion :=
    hind.dfinsupp_lsum_injective
  have hfinrank := LinearMap.finrank_le_finrank_of_injective hinclusion
  have hdim : ∀ i : Fin q,
      Module.finrank K (E i) =
        Module.finrank K (LinearMap.ker (x - 1)) := by
    intro i
    let e : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo (y ^ (i : ℕ))
      (end_pow_injective_of_injective y hy (i : ℕ))
    have heq := e.finrank_map_eq (LinearMap.ker (x - 1))
    convert heq using 1
    congr 1
  calc
    q * Module.finrank K (LinearMap.ker (x - 1)) =
        ∑ _i : Fin q, Module.finrank K (LinearMap.ker (x - 1)) := by simp
    _ = ∑ i : Fin q, Module.finrank K (E i) := by
      apply Finset.sum_congr rfl
      intro i _hi
      exact (hdim i).symm
    _ = Module.finrank K (⨁ i : Fin q, E i) := by
      rw [Module.finrank_directSum]
    _ ≤ Module.finrank K V := hfinrank

/-- Prime-field cardinal form of the nonsplit operator-cycle estimate.  The
central operator `z` need not have any eigenvalue in the ground field: it is
enough that `z^q = 1` and every `z^k - 1`, for `0 < k < q`, is injective. -/
theorem ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_operator_cycle
    {r d q : ℕ} [Fact r.Prime]
    (hq : 0 < q)
    (x y : LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))
    (z : Module.End (ZMod r) (Fin d → ZMod r))
    (hxy : generalLinearEnd x * generalLinearEnd y =
      z * generalLinearEnd y * generalLinearEnd x)
    (hxz : Commute (generalLinearEnd x) z)
    (hzy : Commute z (generalLinearEnd y))
    (hzq : z ^ q = 1)
    (hfree : ∀ k, 0 < k → k < q →
      Function.Injective
        (z ^ k - (1 : Module.End (ZMod r) (Fin d → ZMod r)))) :
    (nonzeroFixedVectorSet x).ncard ≤ r ^ (d / q) - 1 := by
  have hmulRaw := mul_finrank_ker_sub_one_le_of_operator_cycle
    (generalLinearEnd x) (generalLinearEnd y) z
    y.toLinearEquiv.injective hxy hxz hzy hzq hfree
  have hmul : q * Module.finrank (ZMod r) (fixedSpace x) ≤ d := by
    have hx : fixedSpace x = LinearMap.ker (generalLinearEnd x - 1) := by
      ext v
      rfl
    rw [hx]
    simpa only [Module.finrank_fin_fun] using hmulRaw
  have hdim : Module.finrank (ZMod r) (fixedSpace x) ≤ d / q := by
    apply (Nat.le_div_iff_mul_le hq).2
    simpa [Nat.mul_comm] using hmul
  rw [ncard_nonzeroFixedVectorSet_eq_pow_finrank_sub_one_zmod]
  exact Nat.sub_le_sub_right
    (Nat.pow_le_pow_right (Fact.out : r.Prime).pos hdim) 1

/-- General-linear-group wrapper for the nonsplit operator-cycle estimate.
This is the direct analogue of scalar eigenspace cycling, but the central
element is retained as an operator rather than identified with a scalar in
the ground field. -/
theorem ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_GL_operator_cycle
    {r d q : ℕ} [Fact r.Prime]
    (hq : 0 < q)
    (x y z : LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))
    (hxy : x * y = z * y * x)
    (hxz : Commute x z) (hzy : Commute z y)
    (hzq : z ^ q = 1)
    (hfree : ∀ k, 0 < k → k < q →
      Function.Injective
        ((generalLinearEnd z) ^ k -
          (1 : Module.End (ZMod r) (Fin d → ZMod r)))) :
    (nonzeroFixedVectorSet x).ncard ≤ r ^ (d / q) - 1 := by
  apply ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_operator_cycle
    hq x y (generalLinearEnd z)
  · calc
      generalLinearEnd x * generalLinearEnd y =
          generalLinearEnd (x * y) := (generalLinearEnd_mul x y).symm
      _ = generalLinearEnd (z * y * x) := congrArg generalLinearEnd hxy
      _ = generalLinearEnd z * generalLinearEnd y * generalLinearEnd x := by simp
  · calc
      generalLinearEnd x * generalLinearEnd z =
          generalLinearEnd (x * z) := (generalLinearEnd_mul x z).symm
      _ = generalLinearEnd (z * x) := congrArg generalLinearEnd hxz.eq
      _ = generalLinearEnd z * generalLinearEnd x := generalLinearEnd_mul z x
  · calc
      generalLinearEnd z * generalLinearEnd y =
          generalLinearEnd (z * y) := (generalLinearEnd_mul z y).symm
      _ = generalLinearEnd (y * z) := congrArg generalLinearEnd hzy.eq
      _ = generalLinearEnd y * generalLinearEnd z := generalLinearEnd_mul y z
  · rw [← generalLinearEnd_pow, hzq, generalLinearEnd_one]
  · exact hfree

/-- Fixed-point-free version of the general-linear nonsplit cycle bound.
This is usually the most natural group-theoretic interface: no nonidentity
power of the central element fixes a nonzero vector. -/
theorem ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_GL_fixedPointFree_cycle
    {r d q : ℕ} [Fact r.Prime]
    (hq : 0 < q)
    (x y z : LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))
    (hxy : x * y = z * y * x)
    (hxz : Commute x z) (hzy : Commute z y)
    (hzq : z ^ q = 1)
    (hfixed : ∀ k, 0 < k → k < q → ∀ v : Fin d → ZMod r,
      (z ^ k).toLinearEquiv v = v → v = 0) :
    (nonzeroFixedVectorSet x).ncard ≤ r ^ (d / q) - 1 := by
  apply ncard_nonzeroFixedVectorSet_le_pow_div_sub_one_of_GL_operator_cycle
    hq x y z hxy hxz hzy hzq
  intro k hkpos hklt
  rw [end_sub_one_injective_iff_fixedPointFree]
  intro v hv
  apply hfixed k hkpos hklt v
  change generalLinearEnd (z ^ k) v = v
  rw [generalLinearEnd_pow]
  exact hv

end LisiSabatini
