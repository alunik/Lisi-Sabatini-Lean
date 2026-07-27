import LisiSabatini.SchurWeylBasis
import LisiSabatini.TwoCoreSymplecticTypeInnerRestriction

/-!
# Stone--von Neumann degree for extraspecial two-groups

The existing Schur-field Weyl-basis theorem is stated for odd
cyclic-center class-two groups.  The mixed Hall--Berger branch instead
needs the characteristic-two group-theoretic case: an extraspecial
`2`-group represented over a field of odd characteristic.

The proof below is characteristic-free at the module-theoretic level.
For a faithful homogeneous representation, the central character on one
simple constituent is faithful.  Operators indexed by `P / Z(P)` are
joint eigenvectors for conjugation, with eigenvalues supplied by the
commutator central character.  The extraspecial commutator pairing is
nondegenerate, so these operators are linearly independent over the Schur
field.  Jacobson density supplies spanning.  Hence, if

`|P| = 2 e²`,

then the Schur-linear dimension of a simple constituent is exactly `e`.
-/

noncomputable section

namespace LisiSabatini

open scoped MonoidAlgebra
open scoped commutatorElement

set_option backward.isDefEq.respectTransparency false

universe uK uP uV

namespace TwoCoreSchur

variable {k : Type uK} {P : Type uP} {V : Type uV}
variable [Field k] [Group P] [Finite P]
variable [AddCommGroup V] [Module k V]
variable (rho : Representation k P V)

/-- A commutator, regarded as an element of the center when the derived
subgroup is central. -/
def commutatorCenter
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (x y : P) : Subgroup.center P :=
  ⟨⁅x, y⁆,
    hcomm.commutator_le_center
      (Subgroup.commutator_mem_commutator
        (Subgroup.mem_top x) (Subgroup.mem_top y))⟩

/-- The Schur-field eigenvalue attached to one central coset and one
conjugating element. -/
def commutatorEigenvalue
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (u : P ⧸ Subgroup.center P) (g : P) :
    SchurField k[P] S :=
  fullCenterSchurScalarHom rho S
    (commutatorCenter hcomm g (centralQuotientLift u))

@[simp]
theorem commutatorEigenvalue_val
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (u : P ⧸ Subgroup.center P) (g : P) :
    (commutatorEigenvalue rho S hcomm u g).val =
      centralConstituentAction rho S
        (commutatorCenter hcomm g (centralQuotientLift u)) :=
  rfl

/-- Central-coset operators are joint eigenvectors for conjugation, with
eigenvalues given by the faithful central commutator character. -/
theorem conjugationOperator_centralQuotientLift
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (g : P) (u : P ⧸ Subgroup.center P) :
    SchurField.conjugationOperator (k := k) S g
        (SchurField.linearAction (k := k) S
          (centralQuotientLift u)) =
      commutatorEigenvalue rho S hcomm u g •
        SchurField.linearAction (k := k) S
          (centralQuotientLift u) := by
  let y : P := centralQuotientLift u
  change
    SchurField.linearAction (k := k) S g *
          SchurField.linearAction (k := k) S y *
            SchurField.linearAction (k := k) S g⁻¹ =
      commutatorEigenvalue rho S hcomm u g •
        SchurField.linearAction (k := k) S y
  calc
    SchurField.linearAction (k := k) S g *
          SchurField.linearAction (k := k) S y *
            SchurField.linearAction (k := k) S g⁻¹ =
        SchurField.linearAction (k := k) S ((g * y) * g⁻¹) := by
      rw [SchurField.linearAction_mul, SchurField.linearAction_mul]
    _ = SchurField.linearAction (k := k) S (⁅g, y⁆ * y) := by
      congr 1
      simp only [commutatorElement_def]
      group
    _ = commutatorEigenvalue rho S hcomm u g •
          SchurField.linearAction (k := k) S y := by
      apply LinearMap.ext
      intro s
      rw [commutatorEigenvalue]
      change
        MonoidAlgebra.of k P (⁅g, y⁆ * y) • s =
          (fullCenterSchurScalarHom rho S
            (commutatorCenter hcomm g y)).val
              (MonoidAlgebra.of k P y • s)
      change
        MonoidAlgebra.of k P (⁅g, y⁆ * y) • s =
          MonoidAlgebra.of k P ⁅g, y⁆ •
            (MonoidAlgebra.of k P y • s)
      rw [map_mul, mul_smul]

/-- The joint Schur commutator characters separate the central cosets. -/
theorem commutatorEigenvalue_injective
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hfaith : Function.Injective rho) {b : ℕ}
    (decomposition : rho.asModule ≃ₗ[k[P]] Fin b → S)
    (hcomm : HasCentralCommutatorOfOrderTwo P) :
    Function.Injective
      (fun u : P ⧸ Subgroup.center P ↦
        fun g : P ↦ commutatorEigenvalue rho S hcomm u g) := by
  intro u v huv
  let a : P := centralQuotientLift u
  let b' : P := centralQuotientLift v
  have hscalar :
      Function.Injective (fullCenterSchurScalarHom rho S) :=
    fullCenterSchurScalarHom_injective_of_decomposition
      rho hfaith decomposition
  have hcommEq : ∀ g : P, ⁅g, a⁆ = ⁅g, b'⁆ := by
    intro g
    let za : Subgroup.center P := commutatorCenter hcomm g a
    let zb : Subgroup.center P := commutatorCenter hcomm g b'
    have hz : za = zb := by
      apply hscalar
      exact congrFun huv g
    exact congrArg Subtype.val hz
  have hcenter : a / b' ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply commutatorElement_eq_one_iff_mul_comm.mp
    have hgbInvMem :
        ⁅g, b'⁻¹⁆ ∈ Subgroup.center P :=
      hcomm.commutator_le_center
        (Subgroup.commutator_mem_commutator
          (Subgroup.mem_top g) (Subgroup.mem_top b'⁻¹))
    have hgbInv : ⁅g, b'⁻¹⁆ = ⁅g, b'⁆⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      calc
        ⁅g, b'⁆ * ⁅g, b'⁻¹⁆ = ⁅g, b' * b'⁻¹⁆ :=
          (commutatorElement_mul_right_of_mem_center
            g b' b'⁻¹ hgbInvMem).symm
        _ = 1 := by simp
    calc
      ⁅g, a / b'⁆ = ⁅g, a⁆ * ⁅g, b'⁻¹⁆ :=
        by
          simpa only [div_eq_mul_inv] using
            commutatorElement_mul_right_of_mem_center
              g a b'⁻¹ hgbInvMem
      _ = ⁅g, a⁆ * ⁅g, b'⁆⁻¹ := by rw [hgbInv]
      _ = 1 := by rw [hcommEq g, mul_inv_cancel]
  calc
    u = QuotientGroup.mk' (Subgroup.center P) a :=
      (centralQuotientLift_mk u).symm
    _ = QuotientGroup.mk' (Subgroup.center P) b' :=
      QuotientGroup.eq_iff_div_mem.mpr hcenter
    _ = v := centralQuotientLift_mk v

/-- The central-coset operators are linearly independent over the Schur
field for a faithful homogeneous representation of a group with central
commutator of order two. -/
theorem linearIndependent_centralQuotientLift
    (S : Submodule k[P] rho.asModule)
    [IsSimpleModule k[P] S] [Finite (Module.End k[P] S)]
    (hfaith : Function.Injective rho) {b : ℕ}
    (decomposition : rho.asModule ≃ₗ[k[P]] Fin b → S)
    (hcomm : HasCentralCommutatorOfOrderTwo P) :
    LinearIndependent (SchurField k[P] S)
      (fun u : P ⧸ Subgroup.center P ↦
        SchurField.linearAction (k := k) S
          (centralQuotientLift u)) := by
  let mu : (P ⧸ Subgroup.center P) → P → SchurField k[P] S :=
    fun u g ↦ commutatorEigenvalue rho S hcomm u g
  apply linearIndependent_of_joint_eigenvectors
    (fun g : P ↦ SchurField.conjugationOperator (k := k) S g)
    mu
  · exact
      commutatorEigenvalue_injective
        rho S hfaith decomposition hcomm
  · intro u hu
    letI : Nontrivial S := IsSimpleModule.nontrivial k[P] S
    have hinv :=
      SchurField.linearAction_mul_inv
        (k := k) S (centralQuotientLift u)
    rw [hu, zero_mul] at hinv
    exact
      (zero_ne_one :
        (0 : Module.End (SchurField k[P] S) S) ≠ 1) hinv
  · intro g u
    exact
      conjugationOperator_centralQuotientLift
        rho S hcomm g u

end TwoCoreSchur

/-! ## Exact extraspecial degree -/

/-- A faithful homogeneous representation of an extraspecial `2`-group
of order `2 e²` has a simple constituent of Schur-linear degree `e`.
Equivalently, if its Schur field has degree `a` over the ground prime
field, then the constituent has ground-field dimension `a e`. -/
theorem HomogeneousDimensionData.exists_extraspecialTwo_schurDegree
    {r d e : ℕ} [Fact r.Prime]
    {P : Type uP} [Group P] [Finite P]
    (rho : Representation (ZMod r) P (Fin d → ZMod r))
    (H : HomogeneousDimensionData r d rho)
    (hfaith : Function.Injective rho)
    (hP : IsExtraspecial 2 P)
    (hcard : Nat.card P = 2 * e * e) :
    ∃ a : ℕ,
      0 < a ∧
      Nat.card (Module.End (ZMod r)[P] H.constituent) = r ^ a ∧
      Module.finrank (ZMod r) H.constituent = a * e := by
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
  have hLI :
      LinearIndependent D
        (fun u : P ⧸ Subgroup.center P ↦
          SchurField.linearAction (k := ZMod r) S
            (centralQuotientLift u)) :=
    TwoCoreSchur.linearIndependent_centralQuotientLift
      rho S hfaith H.decomposition.some
        hP.hasCentralCommutatorOfOrderTwo
  have hspan :
      Submodule.span D
        (Set.range fun u : P ⧸ Subgroup.center P ↦
          SchurField.linearAction (k := ZMod r) S
            (centralQuotientLift u)) = ⊤ :=
    SchurField.span_centralQuotientLift_linearAction_eq_top
      (k := ZMod r) (P := P) (S := S)
  have hEndCard :
      Module.finrank D (Module.End D S) =
        Nat.card (P ⧸ Subgroup.center P) := by
    have hspanCard := finrank_span_eq_card hLI
    rw [hspan] at hspanCard
    simpa only [finrank_top, Fintype.card_eq_nat_card] using hspanCard
  have hsquare :
      Module.finrank D S * Module.finrank D S =
        Nat.card (P ⧸ Subgroup.center P) := by
    rw [← Module.finrank_linearMap D D S S]
    exact hEndCard
  have hquotientCard :
      Nat.card (P ⧸ Subgroup.center P) = e * e := by
    have hmul := (Subgroup.center P).index_mul_card
    rw [hP.card_center, hcard] at hmul
    have hmul' :
        2 * (Subgroup.center P).index = 2 * (e * e) := by
      simpa only [mul_assoc, mul_comm, mul_left_comm] using hmul
    have hindex : (Subgroup.center P).index = e * e :=
      Nat.mul_left_cancel (by norm_num) hmul'
    rw [← (Subgroup.center P).index_eq_card]
    exact hindex
  have hmexact : Module.finrank D S = e := by
    apply Nat.mul_self_inj.mp
    exact hsquare.trans hquotientCard
  let a := Module.finrank (ZMod r) D
  have ha : 0 < a := Module.finrank_pos
  have hdim :
      Module.finrank (ZMod r) S = a * e := by
    calc
      Module.finrank (ZMod r) S =
          Module.finrank (ZMod r) D * Module.finrank D S :=
        (Module.finrank_mul_finrank (ZMod r) D S).symm
      _ = a * e := by rw [hmexact]
  have hcardD : Nat.card D = r ^ a := by
    simpa only [a, Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := ZMod r) (V := D))
  have hcardEnd :
      Nat.card (Module.End (ZMod r)[P] S) = r ^ a := by
    calc
      Nat.card (Module.End (ZMod r)[P] S) = Nat.card D :=
        (Nat.card_congr
          (SchurField.equiv
            (A := (ZMod r)[P]) (S := S))).symm
      _ = r ^ a := hcardD
  exact ⟨a, ha, hcardEnd, hdim⟩

end LisiSabatini
