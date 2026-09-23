module

public import LisiSabatini.RegularNormalComponentSynchronization
public import LisiSabatini.QuasiprimitiveRepresentation
public import LisiSabatini.CoprimeNormal
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.NoncommPiCoprod
public import Mathlib.Data.Nat.GCD.BigOperators

/-!
# From nilpotent translated regularity to normal components

`NilpotentTranslatedRegularity` is the finite prime-field coordinate
specialization of the paper's translated-orbit proposition. Its faithful
nilpotent group is a subgroup of the general linear group, and complete
reducibility is stated as semisimplicity of its representation module.

The bridge proved here constructs the product of the normal prime-power
components, proves that its faithful image is nilpotent and coprime to the
characteristic, applies Maschke, and identifies its Sylow factors with the
original components. The translated theorem remains an explicit premise.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped BigOperators

universe uI uG

/-- The finite prime-field form of Proposition 2.3, with complete
reducibility retained as an explicit hypothesis. Faithfulness is automatic
for the concrete subgroup of `GL(V)`. -/
def NilpotentTranslatedRegularity : Prop :=
  ∀ (r : ℕ) [Fact r.Prime] (d : ℕ)
    (K : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r))),
    Group.IsNilpotent K →
    IsSemisimpleModule (MonoidAlgebra (ZMod r) K)
      (linearSubgroupRepresentation K).asModule →
    ∀ {I : Type uI} [Fintype I] (p : I → ℕ),
      (∀ i, Nat.Prime (p i)) → Function.Injective p →
      ∀ P : ∀ i, Sylow (p i) K,
        (∀ i, ∃ w : Fin d → ZMod r,
          MulAction.stabilizer ((P i : Subgroup K).map K.subtype) w = ⊥) →
        ∀ t : I → (Fin d → ZMod r),
          ∃ v, ∀ i,
            MulAction.stabilizer ((P i : Subgroup K).map K.subtype)
              (v + t i) = ⊥

/-- A factor of a product of groups at pairwise distinct primes is a
Sylow subgroup of the product, with the expected coordinate embedding. -/
private def primeComponentSylowPi
    {I : Type uI} [Fintype I] (A : I → Type uG) [∀ i, Group (A i)]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) (hA : ∀ i, IsPGroup (p i) (A i))
    (i : I) : Sylow (p i) (∀ j, A j) := by
  classical
  let e := MonoidHom.mulSingle A i
  refine
    { toSubgroup := e.range
      isPGroup' := (hA i).of_surjective e.rangeRestrict e.rangeRestrict_surjective
      is_maximal' := ?_ }
  intro Q hQ hUQ
  apply le_antisymm ?_ hUQ
  intro x hx
  refine ⟨x i, ?_⟩
  funext j
  by_cases hji : j = i
  · subst j
    simp [e]
  · let : Fact (p i).Prime := ⟨hp i⟩
    let : Fact (p j).Prime := ⟨hp j⟩
    have hd : Disjoint (Q.map (Pi.evalMonoidHom A j)) (⊤ : Subgroup (A j)) :=
      IsPGroup.disjoint_of_ne (p i) (p j) (hinj.ne (Ne.symm hji))
        _ _ (hQ.map _) ((hA j).to_subgroup ⊤)
    have hxj : x j = 1 := Subgroup.disjoint_def.mp hd
      (show x j ∈ Q.map (Pi.evalMonoidHom A j) from ⟨x, hx, rfl⟩)
      (by trivial)
    simpa [e, hji] using hxj.symm

/-- The paper's nilpotent translated theorem supplies the normal-component
linear input used by the good-solvable reduction. There are no additional
nilpotence, semisimplicity or coprimality assumptions on the ambient group. -/
theorem regularNormalComponentSynchronization_of_nilpotentTranslatedRegularity
    (htranslated : NilpotentTranslatedRegularity.{uI}) :
    RegularNormalComponentSynchronization.{uI} := by
  classical
  intro r _ d K I _ p hp hinj hcross H hnormal hHp hregular t
  let : Finite (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)) :=
    Finite.of_injective
      (fun g : LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r) ↦
        fun v : Fin d → ZMod r ↦ g • v)
      (by
        intro g h heq
        apply Units.ext
        exact LinearMap.ext (fun v ↦ congrFun heq v))
  let A : I → Type _ := fun i ↦ H i
  let inclusion : ∀ i, A i →*
      LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r) :=
    fun i ↦ K.subtype.comp (H i).subtype
  have hcomm : Pairwise fun i j ↦ ∀ (x : A i) (y : A j),
      Commute (inclusion i x) (inclusion j y) := by
    intro i j hij x y
    let : Fact (p i).Prime := ⟨hp i⟩
    let : Fact (p j).Prime := ⟨hp j⟩
    exact (normalPSubgroups_commute_of_ne (hinj.ne hij)
      (hHp i) (hnormal i) (hHp j) (hnormal j) x.2 y.2).map K.subtype
  let f := MonoidHom.noncommPiCoprod inclusion hcomm
  let L := f.range
  let : ∀ i, Group.IsNilpotent (A i) := fun i ↦ by
    let : Fact (p i).Prime := ⟨hp i⟩
    exact (hHp i).isNilpotent
  have hnil : Group.IsNilpotent L :=
    Group.nilpotent_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcopFactors (i : I) : Nat.Coprime (Nat.card (A i)) r := by
    let : Fact (p i).Prime := ⟨hp i⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hHp i)
    rw [hn]
    simpa only [pow_one] using
      Nat.coprime_pow_primes n 1 (hp i) (Fact.out : r.Prime) (hcross i)
  have hcopPi : Nat.Coprime (Nat.card (∀ i, A i)) r := by
    rw [Nat.card_pi]
    exact Nat.coprime_prod_left_iff.mpr (fun i _ ↦ hcopFactors i)
  have hcop : Nat.Coprime r (Nat.card L) :=
    (hcopPi.of_dvd_left (Subgroup.card_range_dvd f)).symm
  have hcard : (Nat.card L : ZMod r) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact (Fact.out : r.Prime).coprime_iff_not_dvd.mp hcop
  let : NeZero (Nat.card L : ZMod r) := ⟨hcard⟩
  have hsemi : IsSemisimpleModule (MonoidAlgebra (ZMod r) L)
      (linearSubgroupRepresentation L).asModule := inferInstance
  let S : ∀ i, Sylow (p i) (∀ j, A j) :=
    primeComponentSylowPi A p hp hinj hHp
  let P : ∀ i, Sylow (p i) L := fun i ↦ by
    let : Fact (p i).Prime := ⟨hp i⟩
    exact (S i).mapSurjective f.rangeRestrict_surjective
  have hfSingle (i : I) :
      f.comp (MonoidHom.mulSingle A i) = inclusion i := by
    apply MonoidHom.ext
    intro x
    exact MonoidHom.noncommPiCoprod_mulSingle inclusion (hcomm := hcomm) i x
  have hPimage (i : I) :
      (P i : Subgroup L).map L.subtype = (H i).map K.subtype := by
    change (((S i : Subgroup (∀ j, A j)).map f.rangeRestrict).map L.subtype) = _
    rw [Subgroup.map_map]
    change (S i : Subgroup (∀ j, A j)).map f = _
    change (MonoidHom.mulSingle A i).range.map f = _
    rw [← MonoidHom.range_comp, hfSingle]
    exact MonoidHom.range_comp K.subtype (H i).subtype |>.trans
      (congrArg (fun U : Subgroup K ↦ U.map K.subtype)
        (Subgroup.range_subtype (H i)))
  have hregularP (i : I) : ∃ w : Fin d → ZMod r,
      MulAction.stabilizer ((P i : Subgroup L).map L.subtype) w = ⊥ := by
    rw [hPimage]
    exact hregular i
  obtain ⟨v, hv⟩ := htranslated r d L hnil hsemi p hp hinj P hregularP t
  refine ⟨v, fun i ↦ ?_⟩
  have hvi := hv i
  rw [hPimage i] at hvi
  exact hvi

end LisiSabatini
