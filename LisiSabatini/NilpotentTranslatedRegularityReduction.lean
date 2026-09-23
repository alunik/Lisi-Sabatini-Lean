module

public import LisiSabatini.NilpotentTranslatedRegularityInduction
public import LisiSabatini.NilpotentTranslatedRegularityAssembly
public import LisiSabatini.NilpotentTranslatedRegularityBridge
public import LisiSabatini.NilpotentTranslatedRegularitySemisimple
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.DFinsupp

/-!
# Completely reducible nilpotent translated regularity

The irreducible theorem is assembled using the actual projections of the
given global regular vectors. Pure constituents retain their single active
row's reference projection. Mixed constituents retain the 2-stabilizer and
make the odd stabilizers trivial. No projected reference is assumed regular.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uK uV

private theorem sylow_coe_cast {K : Type*} [Group K] {p q : ℕ}
    (h : p = q) (P : Sylow p K) :
    ((h ▸ P : Sylow q K) : Subgroup K) = (P : Subgroup K) := by
  subst q
  rfl

/-- On an irreducible constituent, arbitrary reference stabilizers can be
preserved simultaneously. The pure case uses the reference itself. -/
theorem exists_sylow_translates_preserving_references_of_irreducible
    {r : ℕ} [Fact r.Prime] {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    [FiniteDimensional (ZMod r) V] [Nontrivial V]
    (K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V))
    [Finite K] [Group.IsNilpotent K]
    (hirr : LinearImprimitivitySystem.IsIrreducible K)
    (hcop : r.Coprime (Nat.card K))
    {I : Type uI} [Finite I] (p : I → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p)
    (P : ∀ i, Sylow (p i) K) (a t : I → V) :
    ∃ v : V, ∀ i,
      MulAction.stabilizer ((P i : Subgroup K).map K.subtype) (v + t i) ≤
        MulAction.stabilizer ((P i : Subgroup K).map K.subtype) (a i) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  by_cases hI : IsEmpty I
  · let : IsEmpty I := hI
    exact ⟨0, fun i ↦ isEmptyElim i⟩
  let : Nonempty I := not_isEmpty_iff.mp hI
  by_cases hpure : ∃ owner : I, ∀ i, i ≠ owner → (P i : Subgroup K) = ⊥
  · obtain ⟨owner, howner⟩ := hpure
    refine ⟨a owner - t owner, fun i ↦ ?_⟩
    by_cases hi : i = owner
    · subst i
      rw [sub_add_cancel]
    · rw [howner i hi, Subgroup.map_bot]
      exact le_of_eq (Subsingleton.elim _ _)
  let J := {i : I // p i ≠ 2 ∧ (P i : Subgroup K) ≠ ⊥}
  have hactive : ∃ i, (P i : Subgroup K) ≠ ⊥ := by
    by_contra h
    push Not at h
    exact hpure ⟨Classical.choice inferInstance, fun i _ ↦ h i⟩
  have hJ : Nonempty J := by
    by_contra h
    have hoddZero (i : I) (hi : p i ≠ 2) : (P i : Subgroup K) = ⊥ := by
      by_contra hPi
      exact h ⟨⟨i, hi, hPi⟩⟩
    obtain ⟨owner, howner⟩ := hactive
    have hownerTwo : p owner = 2 := by
      by_contra hi
      exact howner (hoddZero owner hi)
    apply hpure
    refine ⟨owner, fun i hio ↦ hoddZero i ?_⟩
    intro hiTwo
    exact hio (hinj (hiTwo.trans hownerTwo.symm))
  let : Nonempty J := hJ
  let T : Sylow 2 K := Classical.choice inferInstance
  let : Unique (Sylow 2 K) := Sylow.unique_of_normal T inferInstance
  have htwoImage (i : I) (hi : p i = 2) :
      (P i : Subgroup K) = (T : Subgroup K) := by
    exact (sylow_coe_cast hi (P i)).symm.trans
      (congrArg (fun Q : Sylow 2 K ↦ (Q : Subgroup K))
        (Subsingleton.elim (hi ▸ P i) T))
  have hsupport : (T : Subgroup K) ≠ ⊥ ∨ 2 ≤ Fintype.card J := by
    by_cases hT : (T : Subgroup K) = ⊥
    · right
      have hnotSub : ¬ Subsingleton J := by
        intro hsub
        let : Subsingleton J := hsub
        let owner : J := Classical.choice inferInstance
        apply hpure
        refine ⟨owner.1, fun i hio ↦ ?_⟩
        by_cases hiTwo : p i = 2
        · exact (htwoImage i hiTwo).trans hT
        · by_contra hPi
          have hi : (⟨i, hiTwo, hPi⟩ : J) = owner := Subsingleton.elim _ _
          exact hio (congrArg Subtype.val hi)
      let : Nontrivial J := not_subsingleton_iff_nontrivial.mp hnotSub
      exact Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
    · exact Or.inl hT
  let aTwo : V := if h : ∃ i, p i = 2 then a h.choose else 0
  let tTwo : V := if h : ∃ i, p i = 2 then t h.choose else 0
  have hJinj : Function.Injective (fun j : J ↦ p j.1) := by
    intro i j hij
    exact Subtype.ext (hinj hij)
  obtain ⟨v, hvTwo, hvOdd, _⟩ :=
    exists_translated_regular_sylows_of_irreducible_mixed K hirr hcop
      (fun j : J ↦ p j.1) (fun j ↦ hp j.1) (fun j ↦ j.2.1) hJinj
      (fun j ↦ P j.1) (fun j ↦ j.2.2) T hsupport aTwo tTwo
      (fun j ↦ t j.1) (Classical.choice inferInstance) 0
  refine ⟨v, fun i ↦ ?_⟩
  by_cases hiTwo : p i = 2
  · have hex : ∃ j, p j = 2 := ⟨i, hiTwo⟩
    have hchosen : hex.choose = i := hinj (hex.choose_spec.trans hiTwo.symm)
    have haTwo : aTwo = a i := by simp [aTwo, hex, hchosen]
    have htTwo : tTwo = t i := by simp [tTwo, hex, hchosen]
    rw [htwoImage i hiTwo, ← haTwo, ← htTwo]
    exact hvTwo
  · by_cases hPi : (P i : Subgroup K) = ⊥
    · rw [hPi, Subgroup.map_bot]
      exact le_of_eq (Subsingleton.elim _ _)
    · let j : J := ⟨i, hiTwo, hPi⟩
      rw [hvOdd j]
      exact bot_le

/-- Pull back a stabilizer containment from the faithful image of a
representation. -/
private theorem actionPointStabilizer_le_of_range_stabilizer_le
    {G : Type*} [Group G] {R : Type*} [Semiring R]
    {V : Type*} [AddCommMonoid V] [Module R V]
    (ρ : G →* LinearMap.GeneralLinearGroup R V) (x a : V)
    (h : MulAction.stabilizer ρ.range x ≤ MulAction.stabilizer ρ.range a) :
    actionPointStabilizer ρ x ≤ actionPointStabilizer ρ a := by
  intro g hg
  exact h (show (⟨ρ g, ⟨g, rfl⟩⟩ : ρ.range) ∈
    MulAction.stabilizer ρ.range x from hg)

/-- A simple group-algebra module has irreducible faithful linear image. -/
private theorem ofModule_image_irreducible
    {k G W : Type*} [Field k] [Group G] [AddCommGroup W]
    [Module k W] [Module (MonoidAlgebra k G) W]
    [IsScalarTower k (MonoidAlgebra k G) W]
    [IsSimpleModule (MonoidAlgebra k G) W] :
    LinearImprimitivitySystem.IsIrreducible
      (Representation.ofModule' (k := k) (G := G) W).asGroupHom.range := by
  intro U hU
  have hstable (g : G) (x : W) (hx : x ∈ U) :
      MonoidAlgebra.of k G g • x ∈ U :=
    hU ⟨(Representation.ofModule' (k := k) (G := G) W).asGroupHom g,
      ⟨g, rfl⟩⟩ x hx
  let N : Submodule (MonoidAlgebra k G) W :=
    { toAddSubmonoid := U.toAddSubmonoid
      smul_mem' := by
        intro c x hx
        induction c using MonoidAlgebra.induction_linear with
        | zero => simp
        | add a b ha hb => exact (add_smul a b x) ▸ U.add_mem ha hb
        | single g a =>
            have hs : MonoidAlgebra.single g a = a • MonoidAlgebra.of k G g := by simp
            rw [hs, smul_assoc]
            exact U.smul_mem a (hstable g x hx) }
  rcases eq_bot_or_eq_top N with h | h
  · exact Or.inl (SetLike.coe_injective
      (congrArg (fun T : Submodule (MonoidAlgebra k G) W ↦ (T : Set W)) h))
  · exact Or.inr (SetLike.coe_injective
      (congrArg (fun T : Submodule (MonoidAlgebra k G) W ↦ (T : Set W)) h))

private theorem exists_finite_simple_coordinates
    {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] [Finite V] (ρ : Representation k G V)
    [IsSemisimpleModule (MonoidAlgebra k G) ρ.asModule] :
    ∃ (n : ℕ) (S : Fin n → Submodule (MonoidAlgebra k G) ρ.asModule)
      (e : V ≃ₗ[k] ∀ j, S j),
      (∀ j, IsSimpleModule (MonoidAlgebra k G) (S j)) ∧
      ∀ g v j, e (ρ g v) j =
        Representation.ofModule' (k := k) (G := G) (S j) g (e v j) := by
  let : Finite ρ.asModule := Finite.of_equiv V ρ.asModuleEquiv.symm.toEquiv
  obtain ⟨n, S, eR, hs⟩ :=
    IsSemisimpleModule.exists_linearEquiv_fin_dfinsupp (MonoidAlgebra k G) ρ.asModule
  let ePi : ρ.asModule ≃ₗ[MonoidAlgebra k G] ∀ j, S j :=
    eR.trans DFinsupp.linearEquivFunOnFintype
  let e : V ≃ₗ[k] ∀ j, S j :=
    ρ.asModuleEquiv.symm.trans (ePi.restrictScalars k)
  refine ⟨n, S, e, hs, ?_⟩
  intro g v j
  change ePi (ρ.asModuleEquiv.symm (ρ g v)) j =
    MonoidAlgebra.of k G g • ePi (ρ.asModuleEquiv.symm v) j
  rw [ρ.asModuleEquiv_symm_map_rho, map_smul]
  rfl

set_option maxHeartbeats 800000 in
-- The constituent-image and dependent Sylow transports need a larger elaboration budget.
/-- Proposition 2.3 over finite prime-field coordinate spaces. The proof
uses genuine semisimple constituents and retains projected reference
stabilizers rather than assuming projected references are regular. -/
theorem nilpotentTranslatedRegularity : NilpotentTranslatedRegularity.{uI} := by
  classical
  intro r _ d K hnil hsemi I _ p hp hinj P hregular t
  let V := Fin d → ZMod r
  let : Finite (LinearMap.GeneralLinearGroup (ZMod r) V) :=
    Finite.of_injective
      (fun g : LinearMap.GeneralLinearGroup (ZMod r) V ↦ fun v : V ↦ g • v)
      (by
        intro g h heq
        apply Units.ext
        exact LinearMap.ext (fun v ↦ congrFun heq v))
  let : Group.IsNilpotent K := hnil
  let ρ := linearSubgroupRepresentation K
  let : IsSemisimpleModule (MonoidAlgebra (ZMod r) K) ρ.asModule := hsemi
  let : Finite ρ.asModule := Finite.of_equiv V ρ.asModuleEquiv.symm.toEquiv
  have hcop : Nat.Coprime r (Nat.card K) :=
    characteristic_coprime_of_nilpotent_semisimple K hsemi
  obtain ⟨n, W, e, hsimple, hequiv⟩ := exists_finite_simple_coordinates ρ
  let : ∀ j, IsSimpleModule (MonoidAlgebra (ZMod r) K) (W j) := hsimple
  let : ∀ j, Nontrivial (W j) := fun j ↦
    IsSimpleModule.nontrivial (MonoidAlgebra (ZMod r) K) (W j)
  let localAction (j : Fin n) : K →*
      LinearMap.GeneralLinearGroup (ZMod r) (W j) :=
    (Representation.ofModule' (k := ZMod r) (G := K) (W j)).asGroupHom
  let L (j : Fin n) := (localAction j).range
  let : ∀ j, Finite (L j) := fun j ↦
    Finite.of_surjective (localAction j).rangeRestrict
      (localAction j).rangeRestrict_surjective
  let : ∀ j, Group.IsNilpotent (L j) := fun j ↦
    Group.nilpotent_of_surjective (localAction j).rangeRestrict
      (localAction j).rangeRestrict_surjective
  let localSylow (j : Fin n) : ∀ i, Sylow (p i) (L j) := fun i ↦ by
    let : Fact (p i).Prime := ⟨hp i⟩
    exact (P i).mapSurjective (localAction j).rangeRestrict_surjective
  let globalRow (i : I) : (P i) →* LinearMap.GeneralLinearGroup (ZMod r) V :=
    K.subtype.comp (P i : Subgroup K).subtype
  let localRow (i : I) (j : Fin n) : (P i) →*
      LinearMap.GeneralLinearGroup (ZMod r) (W j) :=
    (localAction j).comp (P i : Subgroup K).subtype
  have globalRange (i : I) :
      (globalRow i).range = (P i : Subgroup K).map K.subtype := by
    simp only [globalRow, MonoidHom.range_comp, Subgroup.range_subtype]
  have globalKernel (i : I) : (globalRow i).ker = ⊥ := by
    apply (MonoidHom.ker_eq_bot_iff (globalRow i)).mpr
    exact K.subtype_injective.comp (P i : Subgroup K).subtype_injective
  have localImage (i : I) (j : Fin n) :
      (localSylow j i : Subgroup (L j)).map (L j).subtype =
        (localRow i j).range := by
    change (((P i : Subgroup K).map (localAction j).rangeRestrict).map
      (L j).subtype) = _
    rw [Subgroup.map_map]
    change (P i : Subgroup K).map (localAction j) =
      ((localAction j).comp (P i : Subgroup K).subtype).range
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  choose a ha using hregular
  have hregularRows (i : I) : actionPointStabilizer (globalRow i) (a i) = ⊥ := by
    rw [← globalKernel i]
    apply (actionPointStabilizer_eq_ker_iff_range_stabilizer_eq_bot
      (globalRow i) (a i)).mpr
    rw [globalRange i]
    exact ha i
  have hrowEquiv : ∀ i g x j,
      e (globalRow i g • x) j = localRow i j g • e x j := by
    intro i g x j
    exact hequiv (g : K) x j
  have hlocal : ∀ j, ∃ w : W j, ∀ i,
      actionPointStabilizer (localRow i j) (w + e (t i) j) ≤
        actionPointStabilizer (localRow i j) (e (a i) j) := by
    intro j
    have hirr : LinearImprimitivitySystem.IsIrreducible (L j) :=
      ofModule_image_irreducible
    have hcopLocal : Nat.Coprime r (Nat.card (L j)) :=
      hcop.of_dvd_right (Subgroup.card_range_dvd (localAction j))
    obtain ⟨w, hw⟩ := exists_sylow_translates_preserving_references_of_irreducible
      (L j) hirr hcopLocal p hp hinj (localSylow j)
      (fun i ↦ e (a i) j) (fun i ↦ e (t i) j)
    refine ⟨w, fun i ↦ ?_⟩
    apply actionPointStabilizer_le_of_range_stabilizer_le
    have hwi := hw i
    rw [localImage i j] at hwi
    exact hwi
  obtain ⟨v, hv⟩ := exists_common_regular_translates_of_coordinate_stabilizer_containment
    (I := I) (G := fun i ↦ (P i)) (R := ZMod r) (V := V)
    (J := Fin n) (W := fun j ↦ W j)
    globalRow localRow e hrowEquiv a t hregularRows hlocal
  refine ⟨v, fun i ↦ ?_⟩
  rw [← globalRange i]
  apply (actionPointStabilizer_eq_ker_iff_range_stabilizer_eq_bot
    (globalRow i) (v + t i)).mp
  rw [hv i, globalKernel i]

end LisiSabatini
