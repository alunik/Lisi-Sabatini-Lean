module

public import LisiSabatini.BlockStabilizerLocalAction
public import LisiSabatini.MappedPCoreFrattini
public import LisiSabatini.MappedPCoreCyclicCenterClassTwo
public import LisiSabatini.PrimitiveTopMixedPrimeCoreDominationCore
public import LisiSabatini.ActiveTopOneOrbitComposition

/-!
# Direct primewise affine regularity

This proof-only module carries out the dimension descent directly.  It does
not first materialize a block-stabilizer tower and then fold that tower, and
it does not pass through abstract node or quasiprimitive-leaf records.

The induction invariant is the marked, one-orbit-avoiding form of normal
component synchronization.  At a quasiprimitive action the mixed prime-core
theorem closes the leaf.  At an imprimitive action, Clifford extraction gives
a strict primitive-top presentation and the induction hypotheses for its
faithful block-stabilizer local actions feed directly into the active-top
composition theorem.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uJ uV

/-! ## Direct composition through one imprimitive layer -/

namespace PrimeFieldPrimitiveInternalImprimitivityPresentation

variable {r b e : ℕ} {V : Type uV}
variable [AddCommGroup V] [Module (ZMod r) V]
variable {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}

/-- One-orbit synchronization in every faithful block-stabilizer local
action propagates directly through the primitive top. -/
theorem normalComponentOrbitAvoidingSynchronizationOn_of_children
    (P : PrimeFieldPrimitiveInternalImprimitivityPresentation
      r b e V K)
    (hlocal : ∀ i : Fin b,
      NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r
        (Fin e → ZMod r) (P.blockStabilizerLocalAction i)) :
    NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r V K := by
  have hblock : NormalComponentOrbitAvoidingSynchronizationOn.{uJ} r
      (Fin b → Fin e → ZMod r) P.blockAction := by
    let D := P.imprimitiveLinearActionData
    let : Nonempty (Fin b) := Fin.pos_iff_nonempty.mp
      (P.blockCount_one_lt.trans' Nat.zero_lt_one)
    let : Finite D.blockPerm.range :=
      P.toPrimitiveImprimitivityPresentation.top_finite
    let : FaithfulSMul D.blockPerm.range (Fin b) :=
      P.toPrimitiveImprimitivityPresentation.top_faithful
    let : MulAction.IsPreprimitive D.blockPerm.range (Fin b) :=
      P.toPrimitiveImprimitivityPresentation.top_preprimitive
    intro J _ p hp hinj hpTwo hcross H hHnormal hHp
    cases isEmpty_or_nonempty J with
    | inl hJ =>
        let : IsEmpty J := hJ
        intro j
        exact isEmptyElim j
    | inr hJ =>
        let : Nonempty J := hJ
        apply
          D.orbitAvoidingCommonRegularTranslates_of_primitiveTop_of_localOneOrbit
            p hp hinj hpTwo H hHnormal hHp
        intro i
        have hi := hlocal i p hp hinj hpTwo hcross
          (fun j ↦
            P.componentBaseInBlockStabilizerLocalActionOfBlockAction
              (H j) i)
          (fun j ↦
            P.componentBaseInBlockStabilizerLocalActionOfBlockAction_normal
              (H j) (hHnormal j) i)
          (fun j ↦
            P.componentBaseInBlockStabilizerLocalActionOfBlockAction_isPGroup
              (H j) (hHp j) i)
        simpa only [
          P.map_componentBaseInBlockStabilizerLocalActionOfBlockAction_subtype_eq_commonLocalGL]
          using hi
  intro J _ p hp hinj hpTwo hcross H hHnormal hHp
  exact
    (NCASLinearEquiv.normalComponentOrbitAvoidingSynchronizationOn_of_conjugate.{uJ, uV, 0}
      P.coordinates K hblock)
      p hp hinj hpTwo hcross H hHnormal hHp

end PrimeFieldPrimitiveInternalImprimitivityPresentation

/-! ## Direct quasiprimitive leaf -/

open PrimeCoreMixedCyclicCenterFullSchurFamilyRows

/-- Hobby's theorem and the mixed prime-core orbit bound give marked normal
component synchronization at every positive-dimensional quasiprimitive
prime-field action. -/
theorem quasiprimitiveNormalComponentOrbitAvoidingSynchronization
    {r d : ℕ} [Fact r.Prime]
    {K : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))}
    (hd : 0 < d) (hrTwo : r ≠ 2)
    (hqp : IsQuasiprimitiveLinearAction r d K) :
    NormalComponentOrbitAvoidingSynchronization.{uJ} r d K := by
  let : NeZero r := ⟨(Fact.out : Nat.Prime r).ne_zero⟩
  intro J _ p hp hinj hpTwo hcross H hHnormal hHp
  exact
    orbitAvoidingCommonRegularTranslates_of_quasiprimitive
      hrTwo hd hp hpTwo hcross hinj hqp
      (fun j hne hnoncomm ↦ by
        let hA : IsAdmissibleNoncommutingPrimeCore r d (p j) K :=
          ⟨hp j, hpTwo j, hcross j, hne, hnoncomm⟩
        exact
          mapped_pCore_isOddCyclicCenterClassTwo_of_frattini_isMulCommutative
            (Fact.out : Nat.Prime r) hqp hA
            (mapped_pCore_frattini_isMulCommutative_of_quasiprimitive
              (Fact.out : Nat.Prime r) hqp hA))
      H hHnormal hHp

/-! ## Fused dimension recursion -/

/-- **Marked primewise affine regularity.**

The simultaneous regular vector may additionally be chosen outside an
arbitrary orbit of one distinguished normal prime component.  The proof is
one strong induction on dimension; no intermediate descent tree is built. -/
theorem primewiseAffineOrbitAvoidance_of_irreducible
    {r d : ℕ} [Fact r.Prime]
    {K : Subgroup (LinearMap.GeneralLinearGroup
      (ZMod r) (Fin d → ZMod r))}
    (hrTwo : r ≠ 2)
    (hirr : IsIrreducibleLinearAction r d K)
    (hd : 0 < d) :
    NormalComponentOrbitAvoidingSynchronization.{uJ} r d K := by
  induction d using Nat.strong_induction_on with
  | h d ih =>
      rcases
          quasiprimitiveLinearAction_or_strictInternalImprimitivityPresentation
            r d K hirr with hqp | hS
      · exact
          quasiprimitiveNormalComponentOrbitAvoidingSynchronization
            hd hrTwo hqp
      · obtain ⟨S⟩ := hS
        exact
          S.presentation
            |>.normalComponentOrbitAvoidingSynchronizationOn_of_children
              (fun i ↦
                ih S.localDimension S.localDimension_lt
                  (S.presentation.blockStabilizerLocalAction_irreducible i)
                  S.presentation.localDimension_pos)

end LisiSabatini
