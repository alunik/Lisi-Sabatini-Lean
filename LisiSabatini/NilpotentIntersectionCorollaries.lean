module

public import LisiSabatini.FittingSubgroup
public import LisiSabatini.ThreeConjugatesSynchronization

/-!
# Nilpotent-intersection corollaries

This file contains only the general implications from synchronized Sylow
intersections to Fitting-subgroup containment.  Concrete applications are
collected in `NilpotentIntersectionApplications`.

In both proofs the ambient Sylow rows are chosen from the nilpotent
subgroups before synchronization supplies the conjugator.  Thus the choice
does not depend on the eventual intersection.
-/

@[expose] public section

open scoped Pointwise

noncomputable section

namespace LisiSabatini

universe uG

/-- Every nilpotent subgroup has a conjugate whose self-intersection lies in
the Fitting subgroup. -/
def NilpotentSelfIntersectionInFitting
    (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ (H : Subgroup G), Group.IsNilpotent H →
    ∃ x : G, H ⊓ ((MulAut.conj x) • H) ≤ fittingSubgroup G

/-- Any two nilpotent subgroups admit a relative conjugate whose intersection
lies in the Fitting subgroup. -/
def MixedNilpotentIntersectionInFitting
    (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ (H K : Subgroup G), Group.IsNilpotent H → Group.IsNilpotent K →
    ∃ x : G, H ⊓ ((MulAut.conj x) • K) ≤ fittingSubgroup G

/-- Any three nilpotent subgroups admit two relative conjugates whose common
intersection lies in the Fitting subgroup. -/
def ThreeNilpotentIntersectionInFitting
    (G : Type uG) [Group G] [Finite G] : Prop :=
  ∀ (H K M : Subgroup G),
    Group.IsNilpotent H →
    Group.IsNilpotent K →
    Group.IsNilpotent M →
      ∃ x y : G,
        (H ⊓ ((MulAut.conj x) • K)) ⊓
            ((MulAut.conj y) • M) ≤
          fittingSubgroup G

/-- Strong synchronized Sylow intersections imply the nilpotent
self-intersection Fitting containment. -/
theorem nilpotentSelfIntersectionInFitting_of_strongLS
    {G : Type uG} [Group G] [Finite G]
    (hstrong : StrongLisiSabatini.{uG, 0} G) :
    NilpotentSelfIntersectionInFitting G := by
  classical
  intro H hHnil
  letI : Group.IsNilpotent H := hHnil
  let ps := (Nat.card H).primeFactors
  let S : ∀ i : ps, Sylow (i : ℕ) H := fun _ ↦ default
  have hSnormal : ∀ i : ps, (S i : Subgroup H).Normal := by
    intro i
    have hall := ((isNilpotent_of_finite_tfae (G := H)).out 0 3).mp hHnil
    exact hall (i : ℕ) ⟨Nat.prime_of_mem_primeFactors i.2⟩ (S i)
  let Pexists : ∀ i : ps, ∃ P : Sylow (i : ℕ) G,
      (S i : Subgroup H).map H.subtype ≤ (P : Subgroup G) := fun i ↦
    ((S i).isPGroup'.map H.subtype).exists_le_sylow
  let P : ∀ i : ps, Sylow (i : ℕ) G := fun i ↦ Classical.choose (Pexists i)
  have hSP : ∀ i : ps, (S i : Subgroup H).map H.subtype ≤
      (P i : Subgroup G) :=
    fun i ↦ Classical.choose_spec (Pexists i)
  obtain ⟨x, hx⟩ := hstrong (fun i : ps ↦ (i : ℕ))
    (fun i ↦ Nat.prime_of_mem_primeFactors i.2)
    (fun _ _ hij ↦ Subtype.ext hij) P
  refine ⟨x, ?_⟩
  let C : Subgroup G := (MulAut.conj x) • H
  let L : Subgroup G := H ⊓ C
  have hLH : L ≤ H := inf_le_left
  have hLC : L ≤ C := inf_le_right
  let Lin : Subgroup H := L.subgroupOf H
  letI : Group.IsNilpotent Lin := inferInstance
  let eL : Lin ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  have hLnil : Group.IsNilpotent L := nilpotent_of_mulEquiv eL
  change L ≤ fittingSubgroup G
  apply nilpotentSubgroup_le_of_sylow_map_le L (fittingSubgroup G) hLnil
  intro q Q
  have hqprime : Nat.Prime (q : ℕ) :=
    Nat.prime_of_mem_primeFactors q.2
  letI : Fact (Nat.Prime (q : ℕ)) := ⟨hqprime⟩
  have hq_dvd_H : (q : ℕ) ∣ Nat.card H :=
    (Nat.dvd_of_mem_primeFactors q.2).trans
      (Subgroup.card_dvd_of_le hLH)
  let i : ps :=
    ⟨(q : ℕ), hqprime.mem_primeFactors hq_dvd_H Nat.card_pos.ne'⟩
  have mapQ_le_S (f : L →* H) :
      (Q : Subgroup L).map f ≤ (S i : Subgroup H) := by
    letI : (S i : Subgroup H).Normal := hSnormal i
    have hQp : IsPGroup (q : ℕ) ((Q : Subgroup L).map f) :=
      Q.isPGroup'.map f
    have hsup : IsPGroup (q : ℕ)
        ((((Q : Subgroup L).map f) ⊔ (S i : Subgroup H)) : Subgroup H) :=
      hQp.to_sup_of_normal_right (S i).isPGroup'
    have heq : ((Q : Subgroup L).map f) ⊔ (S i : Subgroup H) =
        (S i : Subgroup H) :=
      (S i).is_maximal' hsup le_sup_right
    exact le_sup_left.trans_eq heq
  let incH : L →* H := Subgroup.inclusion hLH
  let econj : H ≃* C := Subgroup.equivSMul (MulAut.conj x) H
  let pull : L →* H :=
    econj.symm.toMonoidHom.comp (Subgroup.inclusion hLC)
  rintro _ ⟨y, hyQ, rfl⟩
  have hyS1 : incH y ∈ (S i : Subgroup H) :=
    mapQ_le_S incH (Subgroup.mem_map.mpr ⟨y, hyQ, rfl⟩)
  have hyP : (y : G) ∈ (P i : Subgroup G) := by
    apply hSP i
    exact Subgroup.mem_map.mpr ⟨incH y, hyS1, rfl⟩
  have hyS2 : pull y ∈ (S i : Subgroup H) :=
    mapQ_le_S pull (Subgroup.mem_map.mpr ⟨y, hyQ, rfl⟩)
  have hyInvP : ((MulAut.conj x)⁻¹ • (y : G)) ∈
      (P i : Subgroup G) := by
    have ht :=
      hSP i (Subgroup.mem_map.mpr ⟨pull y, hyS2, rfl⟩)
    simpa [pull, econj, C] using ht
  have hyConjP : (y : G) ∈
      ((x • P i : Sylow (i : ℕ) G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr hyInvP
  have hyCore : (y : G) ∈ pCore (i : ℕ) G := by
    rw [← hx i]
    exact ⟨hyP, hyConjP⟩
  exact pCore_le_fittingSubgroup hyCore

/-- Mixed two-row synchronized Sylow intersections imply the mixed
nilpotent-intersection Fitting containment. -/
theorem mixedNilpotentIntersectionInFitting_of_mixedStrongLS
    {G : Type uG} [Group G] [Finite G]
    (hmixed : HasMixedTwoSylowCoreSynchronization.{uG, 0} G) :
    MixedNilpotentIntersectionInFitting G := by
  classical
  intro H K hHnil hKnil
  letI : Group.IsNilpotent H := hHnil
  letI : Group.IsNilpotent K := hKnil
  let ps := (Nat.card H).primeFactors
  let SH : ∀ i : ps, Sylow (i : ℕ) H := fun _ ↦ default
  let SK : ∀ i : ps, Sylow (i : ℕ) K := fun _ ↦ default
  have hSHnormal : ∀ i : ps, (SH i : Subgroup H).Normal := by
    intro i
    have hall := ((isNilpotent_of_finite_tfae (G := H)).out 0 3).mp hHnil
    exact hall (i : ℕ) ⟨Nat.prime_of_mem_primeFactors i.2⟩ (SH i)
  have hSKnormal : ∀ i : ps, (SK i : Subgroup K).Normal := by
    intro i
    have hall := ((isNilpotent_of_finite_tfae (G := K)).out 0 3).mp hKnil
    exact hall (i : ℕ) ⟨Nat.prime_of_mem_primeFactors i.2⟩ (SK i)
  let PHexists : ∀ i : ps, ∃ P : Sylow (i : ℕ) G,
      (SH i : Subgroup H).map H.subtype ≤ (P : Subgroup G) := fun i ↦
    ((SH i).isPGroup'.map H.subtype).exists_le_sylow
  let PKexists : ∀ i : ps, ∃ P : Sylow (i : ℕ) G,
      (SK i : Subgroup K).map K.subtype ≤ (P : Subgroup G) := fun i ↦
    ((SK i).isPGroup'.map K.subtype).exists_le_sylow
  let PH : ∀ i : ps, Sylow (i : ℕ) G :=
    fun i ↦ Classical.choose (PHexists i)
  let PK : ∀ i : ps, Sylow (i : ℕ) G :=
    fun i ↦ Classical.choose (PKexists i)
  have hSHPH : ∀ i : ps, (SH i : Subgroup H).map H.subtype ≤
      (PH i : Subgroup G) :=
    fun i ↦ Classical.choose_spec (PHexists i)
  have hSKPK : ∀ i : ps, (SK i : Subgroup K).map K.subtype ≤
      (PK i : Subgroup G) :=
    fun i ↦ Classical.choose_spec (PKexists i)
  obtain ⟨x, hx⟩ := hmixed (fun i : ps ↦ (i : ℕ))
    (fun i ↦ Nat.prime_of_mem_primeFactors i.2)
    (fun _ _ hij ↦ Subtype.ext hij) PH PK
  refine ⟨x, ?_⟩
  let C : Subgroup G := (MulAut.conj x) • K
  let L : Subgroup G := H ⊓ C
  have hLH : L ≤ H := inf_le_left
  have hLC : L ≤ C := inf_le_right
  let Lin : Subgroup H := L.subgroupOf H
  letI : Group.IsNilpotent Lin := inferInstance
  let eL : Lin ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  have hLnil : Group.IsNilpotent L := nilpotent_of_mulEquiv eL
  change L ≤ fittingSubgroup G
  apply nilpotentSubgroup_le_of_sylow_map_le L (fittingSubgroup G) hLnil
  intro q Q
  have hqprime : Nat.Prime (q : ℕ) :=
    Nat.prime_of_mem_primeFactors q.2
  letI : Fact (Nat.Prime (q : ℕ)) := ⟨hqprime⟩
  have hq_dvd_H : (q : ℕ) ∣ Nat.card H :=
    (Nat.dvd_of_mem_primeFactors q.2).trans
      (Subgroup.card_dvd_of_le hLH)
  let i : ps :=
    ⟨(q : ℕ), hqprime.mem_primeFactors hq_dvd_H Nat.card_pos.ne'⟩
  have mapQ_le_SH (f : L →* H) :
      (Q : Subgroup L).map f ≤ (SH i : Subgroup H) := by
    letI : (SH i : Subgroup H).Normal := hSHnormal i
    have hQp : IsPGroup (q : ℕ) ((Q : Subgroup L).map f) :=
      Q.isPGroup'.map f
    have hsup : IsPGroup (q : ℕ)
        ((((Q : Subgroup L).map f) ⊔ (SH i : Subgroup H)) : Subgroup H) :=
      hQp.to_sup_of_normal_right (SH i).isPGroup'
    have heq : ((Q : Subgroup L).map f) ⊔ (SH i : Subgroup H) =
        (SH i : Subgroup H) :=
      (SH i).is_maximal' hsup le_sup_right
    exact le_sup_left.trans_eq heq
  have mapQ_le_SK (f : L →* K) :
      (Q : Subgroup L).map f ≤ (SK i : Subgroup K) := by
    letI : (SK i : Subgroup K).Normal := hSKnormal i
    have hQp : IsPGroup (q : ℕ) ((Q : Subgroup L).map f) :=
      Q.isPGroup'.map f
    have hsup : IsPGroup (q : ℕ)
        ((((Q : Subgroup L).map f) ⊔ (SK i : Subgroup K)) : Subgroup K) :=
      hQp.to_sup_of_normal_right (SK i).isPGroup'
    have heq : ((Q : Subgroup L).map f) ⊔ (SK i : Subgroup K) =
        (SK i : Subgroup K) :=
      (SK i).is_maximal' hsup le_sup_right
    exact le_sup_left.trans_eq heq
  let incH : L →* H := Subgroup.inclusion hLH
  let econj : K ≃* C := Subgroup.equivSMul (MulAut.conj x) K
  let pullK : L →* K :=
    econj.symm.toMonoidHom.comp (Subgroup.inclusion hLC)
  rintro _ ⟨y, hyQ, rfl⟩
  have hySH : incH y ∈ (SH i : Subgroup H) :=
    mapQ_le_SH incH (Subgroup.mem_map.mpr ⟨y, hyQ, rfl⟩)
  have hyPH : (y : G) ∈ (PH i : Subgroup G) := by
    apply hSHPH i
    exact Subgroup.mem_map.mpr ⟨incH y, hySH, rfl⟩
  have hySK : pullK y ∈ (SK i : Subgroup K) :=
    mapQ_le_SK pullK (Subgroup.mem_map.mpr ⟨y, hyQ, rfl⟩)
  have hyInvPK : ((MulAut.conj x)⁻¹ • (y : G)) ∈
      (PK i : Subgroup G) := by
    have ht :=
      hSKPK i (Subgroup.mem_map.mpr ⟨pullK y, hySK, rfl⟩)
    simpa [pullK, econj, C] using ht
  have hyConjPK : (y : G) ∈
      ((x • PK i : Sylow (i : ℕ) G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr hyInvPK
  have hyCore : (y : G) ∈ pCore (i : ℕ) G := by
    rw [← hx i]
    exact ⟨hyPH, hyConjPK⟩
  exact pCore_le_fittingSubgroup hyCore

/-- Mixed three-row synchronized Sylow intersections imply the
three-nilpotent-subgroup Fitting containment. -/
theorem threeNilpotentIntersectionInFitting_of_mixedThree
    {G : Type uG} [Group G] [Finite G]
    (hmixed : HasMixedThreeSylowCoreSynchronization.{uG, 0} G) :
    ThreeNilpotentIntersectionInFitting G := by
  classical
  intro H K M hHnil hKnil hMnil
  letI : Group.IsNilpotent H := hHnil
  letI : Group.IsNilpotent K := hKnil
  letI : Group.IsNilpotent M := hMnil
  let ps := (Nat.card H).primeFactors
  let SH : ∀ i : ps, Sylow (i : ℕ) H := fun _ ↦ default
  let SK : ∀ i : ps, Sylow (i : ℕ) K := fun _ ↦ default
  let SM : ∀ i : ps, Sylow (i : ℕ) M := fun _ ↦ default
  have hSHnormal : ∀ i : ps, (SH i : Subgroup H).Normal := by
    intro i
    have hall := ((isNilpotent_of_finite_tfae (G := H)).out 0 3).mp hHnil
    exact hall (i : ℕ) ⟨Nat.prime_of_mem_primeFactors i.2⟩ (SH i)
  have hSKnormal : ∀ i : ps, (SK i : Subgroup K).Normal := by
    intro i
    have hall := ((isNilpotent_of_finite_tfae (G := K)).out 0 3).mp hKnil
    exact hall (i : ℕ) ⟨Nat.prime_of_mem_primeFactors i.2⟩ (SK i)
  have hSMnormal : ∀ i : ps, (SM i : Subgroup M).Normal := by
    intro i
    have hall := ((isNilpotent_of_finite_tfae (G := M)).out 0 3).mp hMnil
    exact hall (i : ℕ) ⟨Nat.prime_of_mem_primeFactors i.2⟩ (SM i)
  let PHexists : ∀ i : ps, ∃ P : Sylow (i : ℕ) G,
      (SH i : Subgroup H).map H.subtype ≤ (P : Subgroup G) := fun i ↦
    ((SH i).isPGroup'.map H.subtype).exists_le_sylow
  let PKexists : ∀ i : ps, ∃ P : Sylow (i : ℕ) G,
      (SK i : Subgroup K).map K.subtype ≤ (P : Subgroup G) := fun i ↦
    ((SK i).isPGroup'.map K.subtype).exists_le_sylow
  let PMexists : ∀ i : ps, ∃ P : Sylow (i : ℕ) G,
      (SM i : Subgroup M).map M.subtype ≤ (P : Subgroup G) := fun i ↦
    ((SM i).isPGroup'.map M.subtype).exists_le_sylow
  let PH : ∀ i : ps, Sylow (i : ℕ) G :=
    fun i ↦ Classical.choose (PHexists i)
  let PK : ∀ i : ps, Sylow (i : ℕ) G :=
    fun i ↦ Classical.choose (PKexists i)
  let PM : ∀ i : ps, Sylow (i : ℕ) G :=
    fun i ↦ Classical.choose (PMexists i)
  have hSHPH : ∀ i : ps, (SH i : Subgroup H).map H.subtype ≤
      (PH i : Subgroup G) :=
    fun i ↦ Classical.choose_spec (PHexists i)
  have hSKPK : ∀ i : ps, (SK i : Subgroup K).map K.subtype ≤
      (PK i : Subgroup G) :=
    fun i ↦ Classical.choose_spec (PKexists i)
  have hSMPM : ∀ i : ps, (SM i : Subgroup M).map M.subtype ≤
      (PM i : Subgroup G) :=
    fun i ↦ Classical.choose_spec (PMexists i)
  obtain ⟨x, y, hxy⟩ := hmixed (fun i : ps ↦ (i : ℕ))
    (fun i ↦ Nat.prime_of_mem_primeFactors i.2)
    (fun _ _ hij ↦ Subtype.ext hij) PH PK PM
  refine ⟨x, y, ?_⟩
  let CK : Subgroup G := (MulAut.conj x) • K
  let CM : Subgroup G := (MulAut.conj y) • M
  let L : Subgroup G := (H ⊓ CK) ⊓ CM
  have hLH : L ≤ H := inf_le_left.trans inf_le_left
  have hLCK : L ≤ CK := inf_le_left.trans inf_le_right
  have hLCM : L ≤ CM := inf_le_right
  let Lin : Subgroup H := L.subgroupOf H
  letI : Group.IsNilpotent Lin := inferInstance
  let eL : Lin ≃* L := Subgroup.subgroupOfEquivOfLe hLH
  have hLnil : Group.IsNilpotent L := nilpotent_of_mulEquiv eL
  change L ≤ fittingSubgroup G
  apply nilpotentSubgroup_le_of_sylow_map_le L (fittingSubgroup G) hLnil
  intro q Q
  have hqprime : Nat.Prime (q : ℕ) :=
    Nat.prime_of_mem_primeFactors q.2
  letI : Fact (Nat.Prime (q : ℕ)) := ⟨hqprime⟩
  have hq_dvd_H : (q : ℕ) ∣ Nat.card H :=
    (Nat.dvd_of_mem_primeFactors q.2).trans
      (Subgroup.card_dvd_of_le hLH)
  let i : ps :=
    ⟨(q : ℕ), hqprime.mem_primeFactors hq_dvd_H Nat.card_pos.ne'⟩
  have mapQ_le_SH (f : L →* H) :
      (Q : Subgroup L).map f ≤ (SH i : Subgroup H) := by
    letI : (SH i : Subgroup H).Normal := hSHnormal i
    have hQp : IsPGroup (q : ℕ) ((Q : Subgroup L).map f) :=
      Q.isPGroup'.map f
    have hsup : IsPGroup (q : ℕ)
        ((((Q : Subgroup L).map f) ⊔ (SH i : Subgroup H)) : Subgroup H) :=
      hQp.to_sup_of_normal_right (SH i).isPGroup'
    have heq : ((Q : Subgroup L).map f) ⊔ (SH i : Subgroup H) =
        (SH i : Subgroup H) :=
      (SH i).is_maximal' hsup le_sup_right
    exact le_sup_left.trans_eq heq
  have mapQ_le_SK (f : L →* K) :
      (Q : Subgroup L).map f ≤ (SK i : Subgroup K) := by
    letI : (SK i : Subgroup K).Normal := hSKnormal i
    have hQp : IsPGroup (q : ℕ) ((Q : Subgroup L).map f) :=
      Q.isPGroup'.map f
    have hsup : IsPGroup (q : ℕ)
        ((((Q : Subgroup L).map f) ⊔ (SK i : Subgroup K)) : Subgroup K) :=
      hQp.to_sup_of_normal_right (SK i).isPGroup'
    have heq : ((Q : Subgroup L).map f) ⊔ (SK i : Subgroup K) =
        (SK i : Subgroup K) :=
      (SK i).is_maximal' hsup le_sup_right
    exact le_sup_left.trans_eq heq
  have mapQ_le_SM (f : L →* M) :
      (Q : Subgroup L).map f ≤ (SM i : Subgroup M) := by
    letI : (SM i : Subgroup M).Normal := hSMnormal i
    have hQp : IsPGroup (q : ℕ) ((Q : Subgroup L).map f) :=
      Q.isPGroup'.map f
    have hsup : IsPGroup (q : ℕ)
        ((((Q : Subgroup L).map f) ⊔ (SM i : Subgroup M)) : Subgroup M) :=
      hQp.to_sup_of_normal_right (SM i).isPGroup'
    have heq : ((Q : Subgroup L).map f) ⊔ (SM i : Subgroup M) =
        (SM i : Subgroup M) :=
      (SM i).is_maximal' hsup le_sup_right
    exact le_sup_left.trans_eq heq
  let incH : L →* H := Subgroup.inclusion hLH
  let econjK : K ≃* CK := Subgroup.equivSMul (MulAut.conj x) K
  let pullK : L →* K :=
    econjK.symm.toMonoidHom.comp (Subgroup.inclusion hLCK)
  let econjM : M ≃* CM := Subgroup.equivSMul (MulAut.conj y) M
  let pullM : L →* M :=
    econjM.symm.toMonoidHom.comp (Subgroup.inclusion hLCM)
  rintro _ ⟨z, hzQ, rfl⟩
  have hzSH : incH z ∈ (SH i : Subgroup H) :=
    mapQ_le_SH incH (Subgroup.mem_map.mpr ⟨z, hzQ, rfl⟩)
  have hzPH : (z : G) ∈ (PH i : Subgroup G) := by
    apply hSHPH i
    exact Subgroup.mem_map.mpr ⟨incH z, hzSH, rfl⟩
  have hzSK : pullK z ∈ (SK i : Subgroup K) :=
    mapQ_le_SK pullK (Subgroup.mem_map.mpr ⟨z, hzQ, rfl⟩)
  have hzInvPK : ((MulAut.conj x)⁻¹ • (z : G)) ∈
      (PK i : Subgroup G) := by
    have ht :=
      hSKPK i (Subgroup.mem_map.mpr ⟨pullK z, hzSK, rfl⟩)
    simpa [pullK, econjK, CK] using ht
  have hzConjPK : (z : G) ∈
      ((x • PK i : Sylow (i : ℕ) G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr hzInvPK
  have hzSM : pullM z ∈ (SM i : Subgroup M) :=
    mapQ_le_SM pullM (Subgroup.mem_map.mpr ⟨z, hzQ, rfl⟩)
  have hzInvPM : ((MulAut.conj y)⁻¹ • (z : G)) ∈
      (PM i : Subgroup G) := by
    have ht :=
      hSMPM i (Subgroup.mem_map.mpr ⟨pullM z, hzSM, rfl⟩)
    simpa [pullM, econjM, CM] using ht
  have hzConjPM : (z : G) ∈
      ((y • PM i : Sylow (i : ℕ) G) : Subgroup G) := by
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr hzInvPM
  have hzCore : (z : G) ∈ pCore (i : ℕ) G := by
    rw [← hxy i]
    exact ⟨⟨hzPH, hzConjPK⟩, hzConjPM⟩
  exact pCore_le_fittingSubgroup hzCore

end LisiSabatini
