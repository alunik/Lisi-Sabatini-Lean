module

public import LisiSabatini.SchurFieldCore
public import LisiSabatini.CyclicCenterSymplectic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Weyl bases over a Schur field

This file isolates the multi-commutator step in the finite-field
Stone--von Neumann argument.  A family of nonzero vectors which are joint
eigenvectors for a separating family of endomorphisms is linearly
independent.  Applied to conjugation on the Schur-linear endomorphism
algebra, this gives the full symplectic prime power.  The canonical
order-prime central kernel embeds faithfully in the Schur field, which
supplies the required field-order divisor directly.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uD uV uI uJ

/-! ## Joint eigenvectors -/

/-- Nonzero joint eigenvectors with distinct joint eigenvalue functions are
linearly independent.  Unlike the usual one-operator eigenspace lemma, the
separating endomorphism is allowed to depend on the pair of indices. -/
theorem linearIndependent_of_joint_eigenvectors
    {D : Type uD} {V : Type uV} {I : Type uI} {J : Type uJ}
    [Field D] [AddCommGroup V] [Module D V]
    (T : J → Module.End D V) (mu : I → J → D) (v : I → V)
    (hmu : Function.Injective mu)
    (hv : ∀ i, v i ≠ 0)
    (heigen : ∀ j i, T j (v i) = mu i j • v i) :
    LinearIndependent D v := by
  classical
  rw [linearIndependent_iff']
  intro s g hrel i hi
  have aux : ∀ t : Finset I, ∀ c : I → D,
      (∑ x ∈ t, c x • v x) = 0 → ∀ x ∈ t, c x = 0 := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
        intro c _ x hx
        simp at hx
    | @insert a t ha ih =>
        intro c hsum x hx
        have hsum' : c a • v a + ∑ y ∈ t, c y • v y = 0 := by
          simpa [Finset.sum_insert ha] using hsum
        have htail : ∀ y ∈ t, c y = 0 := by
          intro y hy
          have hay : a ≠ y := by
            intro h
            subst y
            exact ha hy
          have hmune : mu a ≠ mu y := fun h ↦ hay (hmu h)
          obtain ⟨j, hj⟩ := Function.ne_iff.mp hmune
          have hT :
              (∑ z ∈ insert a t, (c z * mu z j) • v z) = 0 := by
            have h := congrArg (T j) hsum
            simpa only [map_sum, map_smul, map_zero, heigen,
              smul_smul] using h
          have hscaled :
              (∑ z ∈ insert a t, (c z * mu a j) • v z) = 0 := by
            have h := congrArg (fun w : V ↦ mu a j • w) hsum
            simpa only [Finset.smul_sum, smul_smul, mul_comm, smul_zero] using h
          have hdifference :
              (∑ z ∈ insert a t,
                (c z * (mu z j - mu a j)) • v z) = 0 := by
            calc
              (∑ z ∈ insert a t,
                  (c z * (mu z j - mu a j)) • v z) =
                  (∑ z ∈ insert a t, (c z * mu z j) • v z) -
                    ∑ z ∈ insert a t, (c z * mu a j) • v z := by
                    rw [← Finset.sum_sub_distrib]
                    apply Finset.sum_congr rfl
                    intro z _
                    simp only [mul_sub, sub_smul]
              _ = 0 := by rw [hT, hscaled, sub_self]
          have hsmall :
              (∑ z ∈ t, (c z * (mu z j - mu a j)) • v z) = 0 := by
            simpa [Finset.sum_insert ha] using hdifference
          have hcoef := ih (fun z ↦ c z * (mu z j - mu a j)) hsmall y hy
          exact (mul_eq_zero.mp hcoef).resolve_right (sub_ne_zero.mpr hj.symm)
        by_cases hxa : x = a
        · subst x
          have hca : c a • v a = 0 := by
            have hsumzero : (∑ y ∈ t, c y • v y) = 0 := by
              apply Finset.sum_eq_zero
              intro y hy
              rw [htail y hy, zero_smul]
            simpa [hsumzero] using hsum'
          exact (smul_eq_zero.mp hca).resolve_right (hv a)
        · exact htail x (Finset.mem_of_mem_insert_of_ne hx hxa)
  exact aux s g hrel i hi

/-! ## Central-coset operators span by Jacobson density -/

/-- A fixed representative of a central coset. -/
noncomputable def centralQuotientLift
    {P : Type*} [Group P] (u : P ⧸ Subgroup.center P) : P :=
  Classical.choose (QuotientGroup.mk'_surjective (Subgroup.center P) u)

@[simp]
theorem centralQuotientLift_mk
    {P : Type*} [Group P] (u : P ⧸ Subgroup.center P) :
    QuotientGroup.mk' (Subgroup.center P) (centralQuotientLift u) = u :=
  Classical.choose_spec (QuotientGroup.mk'_surjective (Subgroup.center P) u)

section SchurCosets

open scoped MonoidAlgebra

variable {k P S : Type*} [Field k] [Group P]
  [AddCommGroup S] [Module k S] [Module k[P] S]
  [IsScalarTower k k[P] S] [SMulCommClass k[P] k S]

/-- A central group element acts as a module endomorphism over the full
group algebra. -/
def centralModuleAction (z : Subgroup.center P) :
    Module.End k[P] S where
  toFun s := MonoidAlgebra.of k P z.1 • s
  map_add' x y := smul_add _ _ _
  map_smul' c s := by
    change MonoidAlgebra.of k P z.1 • (c • s) =
      c • (MonoidAlgebra.of k P z.1 • s)
    let hzcomm : ∀ g : P, Commute z.1 g := fun g ↦
      (Subgroup.mem_center_iff.mp z.2 g).symm
    rw [← mul_smul, (MonoidAlgebra.of_commute hzcomm c).eq, mul_smul]

/-- The action of the whole group algebra, regarded as linear over the
diamond-free Schur field. -/
def SchurField.algebraAction
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (a : k[P]) : Module.End (SchurField k[P] S) S where
  toFun s := a • s
  map_add' x y := smul_add _ _ _
  map_smul' f s := by
    change a • f.val s = f.val (a • s)
    exact (f.val.map_smul a s).symm

omit [Module k S] [IsScalarTower k k[P] S] [SMulCommClass k[P] k S] in
@[simp]
theorem SchurField.algebraAction_add
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (a b : k[P]) :
    SchurField.algebraAction (S := S) (a + b) =
      SchurField.algebraAction (S := S) a +
        SchurField.algebraAction (S := S) b := by
  ext s
  exact add_smul a b s

omit [Module k S] [IsScalarTower k k[P] S] [SMulCommClass k[P] k S] in
/-- Jacobson density, transported from the native Schur endomorphism ring
to the separate commutative `SchurField` carrier. -/
theorem SchurField.algebraAction_surjective
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    [Module.Finite (Module.End k[P] S) S] :
    Function.Surjective
      (SchurField.algebraAction (k := k) (P := P) (S := S)) := by
  intro f
  let fNative : Module.End (Module.End k[P] S) S :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun d s ↦ f.map_smul (SchurField.mk d) s }
  obtain ⟨a, ha⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective fNative
  refine ⟨a, ?_⟩
  apply LinearMap.ext
  intro s
  exact DFunLike.congr_fun ha s

omit [Module k S] [IsScalarTower k k[P] S] [SMulCommClass k[P] k S] in
/-- Every group operator is a Schur-scalar multiple of the operator of its
chosen central-coset representative. -/
theorem SchurField.algebraAction_of_mem_span_centralQuotientLift
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (g : P) :
    SchurField.algebraAction (S := S) (MonoidAlgebra.of k P g) ∈
      Submodule.span (SchurField k[P] S)
        (Set.range fun u : P ⧸ Subgroup.center P ↦
          SchurField.linearAction (k := k) S (centralQuotientLift u)) := by
  classical
  let u : P ⧸ Subgroup.center P :=
    QuotientGroup.mk' (Subgroup.center P) g
  let representative : P := centralQuotientLift u
  have hquot : QuotientGroup.mk' (Subgroup.center P) g =
      QuotientGroup.mk' (Subgroup.center P) representative := by
    exact (centralQuotientLift_mk u).symm
  have hzmem : g / representative ∈ Subgroup.center P :=
    QuotientGroup.eq_iff_div_mem.mp hquot
  let z : Subgroup.center P := ⟨g / representative, hzmem⟩
  let scalar : SchurField k[P] S := ⟨centralModuleAction z⟩
  have hfactor :
      SchurField.algebraAction (S := S) (MonoidAlgebra.of k P g) =
        scalar • SchurField.linearAction (k := k) S representative := by
    apply LinearMap.ext
    intro s
    change MonoidAlgebra.of k P g • s =
      MonoidAlgebra.of k P z.1 •
        (MonoidAlgebra.of k P representative • s)
    rw [← mul_smul, ← map_mul]
    congr 2
    dsimp only [z]
    simp [div_eq_mul_inv, mul_assoc]
  rw [hfactor]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  exact ⟨u, rfl⟩

/-- The chosen central-coset operators span the full Schur-linear
endomorphism algebra.  This is the spanning half of the finite
Stone--von Neumann basis theorem; it is unconditional once the constituent
is simple and finite over its Schur endomorphism ring. -/
theorem SchurField.span_centralQuotientLift_linearAction_eq_top
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    [Module.Finite (Module.End k[P] S) S] :
    Submodule.span (SchurField k[P] S)
        (Set.range fun u : P ⧸ Subgroup.center P ↦
          SchurField.linearAction (k := k) S (centralQuotientLift u)) = ⊤ := by
  apply top_unique
  intro f hf
  clear hf
  obtain ⟨a, rfl⟩ :=
    SchurField.algebraAction_surjective
      (k := k) (P := P) (S := S) f
  induction a using MonoidAlgebra.induction_on with
  | hM g =>
      exact SchurField.algebraAction_of_mem_span_centralQuotientLift
        (k := k) (S := S) g
  | hadd a b ha hb =>
      rw [SchurField.algebraAction_add]
      exact Submodule.add_mem _ ha hb
  | hsmul c a ha =>
      have heq : SchurField.algebraAction (S := S) (c • a) =
          algebraMap k (SchurField k[P] S) c •
            SchurField.algebraAction (S := S) a := by
        apply LinearMap.ext
        intro s
        change (c • a) • s = c • (a • s)
        exact smul_assoc c a s
      rw [heq]
      exact Submodule.smul_mem _ _ ha

end SchurCosets

/-! ## Nondegenerate commutator characters give independence -/

namespace IsOddCyclicCenterClassTwo

variable {q : ℕ} {P : Type*} [Group P] [Finite P]

/-- Skew-symmetry of the kernel-valued central-quotient pairing. -/
theorem centralQuotientKernelPairing_swap
    (hP : IsOddCyclicCenterClassTwo q P)
    (x y : P ⧸ Subgroup.center P) :
    hP.centralQuotientKernelPairing x y =
      (hP.centralQuotientKernelPairing y x)⁻¹ := by
  induction x using QuotientGroup.induction_on with
  | _ x =>
      induction y using QuotientGroup.induction_on with
      | _ y =>
          apply Subtype.ext
          exact (commutatorElement_inv y x).symm

/-- The commutator pairing is nondegenerate in its second variable as
well as its first. -/
theorem centralQuotientKernelPairing_right_injective
    (hP : IsOddCyclicCenterClassTwo q P) :
    Function.Injective
      (fun y : P ⧸ Subgroup.center P ↦
        fun x ↦ hP.centralQuotientKernelPairing x y) := by
  intro y z hyz
  apply hP.centralQuotientKernelPairing_injective
  apply MonoidHom.ext
  intro x
  calc
    hP.centralQuotientKernelPairing y x =
        (hP.centralQuotientKernelPairing x y)⁻¹ :=
      hP.centralQuotientKernelPairing_swap y x
    _ = (hP.centralQuotientKernelPairing x z)⁻¹ := by
      have hx := congrFun hyz x
      change hP.centralQuotientKernelPairing x y =
        hP.centralQuotientKernelPairing x z at hx
      exact congrArg Inv.inv hx
    _ = hP.centralQuotientKernelPairing z x :=
      (hP.centralQuotientKernelPairing_swap z x).symm

end IsOddCyclicCenterClassTwo

section CyclicCenterWeyl

open scoped MonoidAlgebra
open scoped commutatorElement

variable {k P V : Type*} [Field k] [Group P] [Finite P]
  [AddCommGroup V] [Module k V]
  (rho : Representation k P V)

/-- Inclusion of the canonical order-`q` kernel into the full center. -/
def centerPrimeKernelToCenterHom
    {q : ℕ} :
    centerPrimeKernel q P →* Subgroup.center P where
  toFun z := ⟨z.1, centerPrimeKernel_le_center q P z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The faithful central character, restricted to the canonical
order-`q` commutator kernel and transported to the Schur field. -/
def kernelSchurScalarHom
    {q : ℕ}
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (_hP : IsOddCyclicCenterClassTwo q P) :
    centerPrimeKernel q P →* SchurField k[P] S :=
  (fullCenterSchurScalarHom rho S).comp
    (centerPrimeKernelToCenterHom (q := q) (P := P))

@[simp]
theorem kernelSchurScalarHom_val
    {q : ℕ}
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hP : IsOddCyclicCenterClassTwo q P)
    (z : centerPrimeKernel q P) :
    (kernelSchurScalarHom rho S hP z).val =
      centralConstituentAction rho S
        (centerPrimeKernelToCenterHom (q := q) (P := P) z) :=
  rfl

/-- Faithfulness of a homogeneous constituent makes the restricted
commutator scalar character injective. -/
theorem kernelSchurScalarHom_injective_of_decomposition
    {q : ℕ}
    (hfaith : Function.Injective rho)
    {S : Submodule k[P] rho.asModule} {b : ℕ}
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (e : rho.asModule ≃ₗ[k[P]] Fin b → S)
    (hP : IsOddCyclicCenterClassTwo q P) :
    Function.Injective (kernelSchurScalarHom rho S hP) := by
  apply Function.Injective.comp
    (fullCenterSchurScalarHom_injective_of_decomposition rho hfaith e)
  intro x y hxy
  apply Subtype.ext
  exact congrArg (fun z : Subgroup.center P ↦ (z : P)) hxy

/-- The joint eigenvalue of a central-coset operator under conjugation by
another central-coset representative. -/
def schurCommutatorEigenvalue
    {q : ℕ}
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hP : IsOddCyclicCenterClassTwo q P)
    (u h : P ⧸ Subgroup.center P) : SchurField k[P] S :=
  kernelSchurScalarHom rho S hP
    (hP.centralQuotientKernelPairing h u)

/-- Conjugation by a group operator, as a Schur-linear endomorphism of
the Schur-linear endomorphism algebra. -/
def SchurField.conjugationOperator
    (S : Type*) [AddCommGroup S] [Module k[P] S]
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (g : P) :
    Module.End (SchurField k[P] S)
      (Module.End (SchurField k[P] S) S) where
  toFun f := SchurField.linearAction (k := k) S g * f *
    SchurField.linearAction (k := k) S g⁻¹
  map_add' f g' := by
    simp only [mul_add, add_mul]
  map_smul' c f := by
    apply LinearMap.ext
    intro s
    change SchurField.linearAction (k := k) S g
        (c • f (SchurField.linearAction (k := k) S g⁻¹ s)) =
      c • SchurField.linearAction (k := k) S g
        (f (SchurField.linearAction (k := k) S g⁻¹ s))
    exact LinearMap.map_smul _ _ _

/-- Central-coset operators are joint eigenvectors for conjugation, with
eigenvalues given by the faithful commutator character. -/
theorem SchurField.conjugationOperator_centralQuotientLift
    {q : ℕ}
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hP : IsOddCyclicCenterClassTwo q P)
    (h u : P ⧸ Subgroup.center P) :
    SchurField.conjugationOperator (k := k) S (centralQuotientLift h)
        (SchurField.linearAction (k := k) S (centralQuotientLift u)) =
      schurCommutatorEigenvalue rho S hP u h •
        SchurField.linearAction (k := k) S (centralQuotientLift u) := by
  change SchurField.linearAction (k := k) S (centralQuotientLift h) *
      SchurField.linearAction (k := k) S (centralQuotientLift u) *
        SchurField.linearAction (k := k) S (centralQuotientLift h)⁻¹ =
    schurCommutatorEigenvalue rho S hP u h •
      SchurField.linearAction (k := k) S (centralQuotientLift u)
  let x : P := centralQuotientLift h
  let y : P := centralQuotientLift u
  calc
    SchurField.linearAction (k := k) S x *
          SchurField.linearAction (k := k) S y *
            SchurField.linearAction (k := k) S x⁻¹ =
        SchurField.linearAction (k := k) S ((x * y) * x⁻¹) := by
      rw [SchurField.linearAction_mul, SchurField.linearAction_mul]
    _ = SchurField.linearAction (k := k) S (⁅x, y⁆ * y) := by
      congr 1
      simp only [commutatorElement_def]
      group
    _ = schurCommutatorEigenvalue rho S hP u h •
          SchurField.linearAction (k := k) S y := by
      have hpair : hP.centralQuotientKernelPairing h u =
          hP.kernelCommutator x y := by
        have hx : QuotientGroup.mk' (Subgroup.center P) x = h := by
          exact centralQuotientLift_mk h
        have hy : QuotientGroup.mk' (Subgroup.center P) y = u := by
          exact centralQuotientLift_mk u
        calc
          hP.centralQuotientKernelPairing h u =
              hP.centralQuotientKernelPairing
                (QuotientGroup.mk' (Subgroup.center P) x)
                (QuotientGroup.mk' (Subgroup.center P) y) := by
            rw [hx, hy]
          _ = hP.kernelCommutator x y :=
            hP.centralQuotientKernelPairing_mk_mk x y
      apply LinearMap.ext
      intro s
      rw [schurCommutatorEigenvalue, hpair]
      change MonoidAlgebra.of k P (⁅x, y⁆ * y) • s =
        (kernelSchurScalarHom rho S hP (hP.kernelCommutator x y)).val
          (MonoidAlgebra.of k P y • s)
      rw [kernelSchurScalarHom_val]
      change MonoidAlgebra.of k P (⁅x, y⁆ * y) • s =
        MonoidAlgebra.of k P ⁅x, y⁆ •
          (MonoidAlgebra.of k P y • s)
      rw [map_mul, mul_smul]

/-- The chosen central-coset operators are linearly independent over the
Schur field.  This is the independence half of the finite
Stone--von Neumann basis theorem. -/
theorem SchurField.linearIndependent_centralQuotientLift_linearAction
    {q : ℕ}
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hfaith : Function.Injective rho) {b : ℕ}
    (e : rho.asModule ≃ₗ[k[P]] Fin b → S)
    (hP : IsOddCyclicCenterClassTwo q P) :
    LinearIndependent (SchurField k[P] S)
      (fun u : P ⧸ Subgroup.center P ↦
        SchurField.linearAction (k := k) S (centralQuotientLift u)) := by
  let mu : (P ⧸ Subgroup.center P) →
      (P ⧸ Subgroup.center P) → SchurField k[P] S :=
    schurCommutatorEigenvalue rho S hP
  have hmu : Function.Injective mu := by
    intro u v huv
    apply hP.centralQuotientKernelPairing_right_injective
    apply funext
    intro h
    apply kernelSchurScalarHom_injective_of_decomposition
      rho hfaith e hP
    exact congrFun huv h
  apply linearIndependent_of_joint_eigenvectors
    (fun h ↦ SchurField.conjugationOperator (k := k) S
      (centralQuotientLift h)) mu
  · exact hmu
  · intro u hu
    letI : Nontrivial S := IsSimpleModule.nontrivial k[P] S
    have hinv := SchurField.linearAction_mul_inv
      (k := k) S (centralQuotientLift u)
    rw [hu, zero_mul] at hinv
    exact (zero_ne_one :
      (0 : Module.End (SchurField k[P] S) S) ≠ 1) hinv
  · intro h u
    exact SchurField.conjugationOperator_centralQuotientLift
      rho S hP h u

end CyclicCenterWeyl

/-! ## The full finite-field Stone--von Neumann degree -/

open scoped MonoidAlgebra

/-- For a faithful homogeneous representation of an odd cyclic-center
class-two `q`-group, the dimension of a simple constituent over its Schur
field is exactly `q^n`, where `n` is the intrinsic symplectic rank.

The proof does not assume a splitting field.  Jacobson density says that
the chosen operators indexed by `P / Z(P)` span the Schur-linear
endomorphism algebra.  The nondegenerate commutator pairing and faithful
central character make them linearly independent.  Hence

`(dim_D S)^2 = |P/Z(P)| = q^(2*n)`,

and positivity gives the asserted square root.  Separately, the faithful
central character embeds the canonical order-`q` subgroup in `Dˣ`, so
Lagrange gives `q ∣ |Dˣ| = r^a - 1` directly; no determinant argument is
needed. -/
theorem HomogeneousDimensionData.exists_schurDegree_fullMultiplicity
    {r d q : ℕ} [Fact r.Prime]
    {P : Type*} [Group P] [Finite P]
    (rho : Representation (ZMod r) P (Fin d → ZMod r))
    (H : HomogeneousDimensionData r d rho)
    (hfaith : Function.Injective rho)
    (hP : IsOddCyclicCenterClassTwo q P) :
    ∃ a : ℕ,
      0 < a ∧
      q ∣ r ^ a - 1 ∧
      Nat.card (Module.End (ZMod r)[P] H.constituent) = r ^ a ∧
      Module.finrank (ZMod r) H.constituent =
        a * q ^ hP.cyclicCenterStructuralRank := by
  classical
  let S := H.constituent
  letI : IsSimpleModule (ZMod r)[P] S := H.constituent_simple
  letI : Module.Finite (ZMod r) S :=
    Module.Finite.of_injective
      (S.subtype.restrictScalars (ZMod r)) S.subtype_injective
  letI : Finite rho.asModule :=
    rho.asModuleEquiv.toEquiv.finite_iff.mpr inferInstance
  letI : Finite S := Finite.of_injective S.subtype S.subtype_injective
  letI : Module.Finite (ZMod r) (Module.End (ZMod r)[P] S) :=
    moduleFinite_schurEnd
      (k := ZMod r) (A := (ZMod r)[P]) (S := S)
  letI : Finite (Module.End (ZMod r)[P] S) :=
    Module.finite_of_finite (ZMod r)
  let D := SchurField (ZMod r)[P] S
  letI : Field D := by
    dsimp only [D]
    infer_instance
  letI moduleDS : Module D S := by
    dsimp only [D]
    infer_instance
  letI : SMul D S :=
    moduleDS.toDistribMulAction.toMulAction.toSemigroupAction.toSMul
  letI : Module.Free D S := Module.Free.of_divisionRing D S
  letI : Fintype D := Fintype.ofFinite D
  letI : Fintype S := Fintype.ofFinite S
  letI : Module.Finite D S := ⟨⟨Finset.univ, by simp⟩⟩
  letI : Module.Finite (Module.End (ZMod r)[P] S) S :=
    ⟨⟨Finset.univ, by simp⟩⟩
  letI : Fintype (P ⧸ Subgroup.center P) := Fintype.ofFinite _
  have hLI : LinearIndependent D
      (fun u : P ⧸ Subgroup.center P ↦
        SchurField.linearAction (k := ZMod r) S (centralQuotientLift u)) :=
    SchurField.linearIndependent_centralQuotientLift_linearAction
      rho S hfaith H.decomposition.some hP
  have hspan : Submodule.span D
      (Set.range fun u : P ⧸ Subgroup.center P ↦
        SchurField.linearAction (k := ZMod r) S (centralQuotientLift u)) = ⊤ :=
    SchurField.span_centralQuotientLift_linearAction_eq_top
      (k := ZMod r) (P := P) (S := S)
  have hEndCard : Module.finrank D (Module.End D S) =
      Nat.card (P ⧸ Subgroup.center P) := by
    have hspanCard := finrank_span_eq_card hLI
    rw [hspan] at hspanCard
    simpa only [finrank_top, Fintype.card_eq_nat_card] using hspanCard
  have hsquare : Module.finrank D S * Module.finrank D S =
      Nat.card (P ⧸ Subgroup.center P) := by
    rw [← Module.finrank_linearMap D D S S]
    exact hEndCard
  have hmexact : Module.finrank D S =
      q ^ hP.cyclicCenterStructuralRank := by
    apply Nat.mul_self_inj.mp
    calc
      Module.finrank D S * Module.finrank D S =
          Nat.card (P ⧸ Subgroup.center P) := hsquare
      _ = q ^ (2 * hP.cyclicCenterStructuralRank) :=
        hP.cyclicCenterStructuralRank_card_quotient_center
      _ = q ^ hP.cyclicCenterStructuralRank *
          q ^ hP.cyclicCenterStructuralRank := by
        rw [two_mul, pow_add]
  let a₀ := Module.finrank (ZMod r) D
  have ha₀ : 0 < a₀ := Module.finrank_pos
  have hdim₀ : Module.finrank (ZMod r) S =
      a₀ * q ^ hP.cyclicCenterStructuralRank := by
    calc
      Module.finrank (ZMod r) S =
          Module.finrank (ZMod r) D * Module.finrank D S :=
        (Module.finrank_mul_finrank (ZMod r) D S).symm
      _ = a₀ * q ^ hP.cyclicCenterStructuralRank := by
        rw [hmexact]
  have hcardD : Nat.card D = r ^ a₀ := by
    simpa only [a₀, Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod r) (V := D))
  have hcardEnd₀ : Nat.card (Module.End (ZMod r)[P] S) = r ^ a₀ := by
    calc
      Nat.card (Module.End (ZMod r)[P] S) = Nat.card D :=
        (Nat.card_congr
          (SchurField.equiv (A := (ZMod r)[P]) (S := S))).symm
      _ = r ^ a₀ := hcardD
  let f := kernelSchurScalarHom rho S hP
  have hf : Function.Injective f :=
    kernelSchurScalarHom_injective_of_decomposition
      rho hfaith H.decomposition.some hP
  have hfUnits : Function.Injective f.toHomUnits := by
    intro x y hxy
    apply hf
    exact congrArg Units.val hxy
  have hdvd := Subgroup.card_dvd_of_injective f.toHomUnits hfUnits
  have hfieldDvd : q ∣ r ^ a₀ - 1 := by
    have hdvd' : q ∣ Nat.card D - 1 := by
      simpa only [hP.card_centerPrimeKernel, Nat.card_units, D] using hdvd
    rwa [hcardD] at hdvd'
  exact ⟨a₀, ha₀, hfieldDvd, hcardEnd₀, hdim₀⟩

end LisiSabatini
