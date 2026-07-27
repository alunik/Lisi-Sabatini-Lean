import LisiSabatini.HallBergerOmegaOne
import LisiSabatini.HobbyFrattiniTheoremCore
import LisiSabatini.FrattiniCentrality

/-!
# Elementary preliminaries in the Berger--Kovács--Newman proof

The published proof starts with

`C = C_G(Φ(G))`

and the hypothesis that `Z(Ω₁(C))` is cyclic.  This file formalizes the
first two deductions in that proof:

* `Z(C)` is cyclic;
* `Φ(G)` is cyclic;
* `Φ(C)` is cyclic and central in `C`.

These are direct inputs to the central-product decomposition of `C`.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

/-- If the center of `Ω₁(C)` is cyclic in a finite `p`-group, then the
center of `C` is cyclic.

The `p`-torsion of `Z(C)` embeds in `Z(Ω₁(C))`, hence is cyclic and has
at most `p` elements.  The finite-abelian `p`-group criterion then applies
to `Z(C)`. -/
theorem center_isCyclic_of_omegaOne_center_isCyclic
    {p : ℕ} {C : Type u} [Group C] [Finite C]
    (hp : p.Prime) (hCp : IsPGroup p C)
    (hOmegaCenter :
      IsCyclic (Subgroup.center (omegaOneSubgroup p C))) :
    IsCyclic (Subgroup.center C) := by
  let Z : Subgroup C := Subgroup.center C
  let K : Subgroup Z := (powMonoidHom p : Z →* Z).ker
  let Omega : Subgroup C := omegaOneSubgroup p C
  let ZOmega : Subgroup Omega := Subgroup.center Omega
  let f : K →* ZOmega :=
    { toFun := fun k =>
        ⟨⟨(k : Z), by
            apply Subgroup.subset_closure
            change ((k : Z) : C) ^ p = 1
            exact congrArg Subtype.val (MonoidHom.mem_ker.mp k.2)⟩, by
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          exact Subgroup.mem_center_iff.mp (k : Z).2 y⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        rfl
      map_mul' := fun _ _ => by
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ZOmega => (((z : Omega) : C))) hxy
  letI : IsCyclic ZOmega := hOmegaCenter
  have hKcyclic : IsCyclic K :=
    isCyclic_of_injective f hf
  letI : IsCyclic K := hKcyclic
  have hKpow : ∀ k : K, k ^ p = 1 := by
    intro k
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp k.2
  have hKcardDvd : Nat.card K ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hKpow
  have hKcard : Nat.card K ≤ p :=
    Nat.le_of_dvd hp.pos hKcardDvd
  exact isCyclic_of_isPGroup_of_natCard_primeKernel_le_prime
    hp (hCp.to_subgroup Z) hKcard

/-- The exact Berger--Kovács--Newman source hypothesis makes the center
of the Frattini centralizer cyclic. -/
theorem frattiniCentralizer_center_isCyclic
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter p G) :
    IsCyclic (Subgroup.center (frattiniCentralizer G)) :=
  center_isCyclic_of_omegaOne_center_isCyclic hp
    (hGp.to_subgroup (frattiniCentralizer G)) hBKN

/-- The ambient image of `Z(Φ(G))` lies in the ambient image of
`Z(C_G(Φ(G)))`. -/
theorem frattini_centerImage_le_frattiniCentralizer_centerImage
    (G : Type u) [Group G] :
    characteristicCenterImage (frattini G) ≤
      characteristicCenterImage (frattiniCentralizer G) := by
  rw [characteristicCenterImage_eq_inf_centralizer,
    characteristicCenterImage_eq_inf_centralizer]
  intro x hx
  refine ⟨hx.2, ?_⟩
  intro c hc
  change c ∈ Subgroup.centralizer (frattini G : Set G) at hc
  exact (hc x hx.1).symm

/-- Under the exact Berger--Kovács--Newman hypothesis, `Φ(G)` is cyclic.

Indeed its center embeds in the cyclic center of `C_G(Φ(G))`.  Hobby's
theorem then makes `Φ(G)` commutative, so it equals its center. -/
theorem frattini_isCyclic_of_omegaOne_frattiniCentralizer_center_isCyclic
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter p G) :
    IsCyclic (frattini G) := by
  let C : Subgroup G := frattiniCentralizer G
  have hCcenter : IsCyclic (Subgroup.center C) :=
    frattiniCentralizer_center_isCyclic hp hGp hBKN
  have hCcenterImage : IsCyclic (characteristicCenterImage C) :=
    (Subgroup.equivMapOfInjective
      (Subgroup.center C) C.subtype
      Subtype.coe_injective).isCyclic.mp hCcenter
  letI : IsCyclic (characteristicCenterImage C) := hCcenterImage
  have hPhiCenterImage :
      IsCyclic (characteristicCenterImage (frattini G)) :=
    Subgroup.isCyclic_of_le
      (frattini_centerImage_le_frattiniCentralizer_centerImage G)
  have hPhiCenter : IsCyclic (Subgroup.center (frattini G)) :=
    (Subgroup.equivMapOfInjective
      (Subgroup.center (frattini G)) (frattini G).subtype
      Subtype.coe_injective).isCyclic.mpr hPhiCenterImage
  have hPhiComm : IsMulCommutative (frattini G) :=
    frattini_isMulCommutative_of_center_isCyclic hp hGp hPhiCenter
  let groupPhi : Group (frattini G) := inferInstance
  letI : CommGroup (frattini G) :=
    { groupPhi with mul_comm := hPhiComm.1.1 }
  rw [CommGroup.center_eq_top] at hPhiCenter
  exact Subgroup.topEquiv.isCyclic.mp hPhiCenter

/-- The source proof's inclusion `Φ(G) ≤ Z(C_G(Φ(G)))`, expressed in
the ambient group. -/
theorem frattini_le_frattiniCentralizer_centerImage
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter p G) :
    frattini G ≤ characteristicCenterImage (frattiniCentralizer G) := by
  have hPhiCyclic :
      IsCyclic (frattini G) :=
    frattini_isCyclic_of_omegaOne_frattiniCentralizer_center_isCyclic
      hp hGp hBKN
  letI : IsCyclic (frattini G) := hPhiCyclic
  rw [characteristicCenterImage_eq_inf_centralizer]
  refine le_inf ?_ ?_
  · intro x hx
    change x ∈ Subgroup.centralizer (frattini G : Set G)
    intro y hy
    exact congrArg Subtype.val
      (IsCyclic.commutative.comm
        (⟨y, hy⟩ : frattini G) (⟨x, hx⟩ : frattini G))
  · intro x hx c hc
    change c ∈ Subgroup.centralizer (frattini G : Set G) at hc
    exact (hc x hx).symm

/-- The Frattini subgroup of `C_G(Φ(G))`, mapped back into `G`, lies in
`Φ(G)`. -/
theorem frattiniCentralizer_map_frattini_le_frattini
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G) :
    (frattini (frattiniCentralizer G)).map
        (frattiniCentralizer G).subtype ≤
      frattini G :=
  map_frattini_subgroup_le_frattini_of_isPGroup
    hp hGp (frattiniCentralizer G)

/-- The Frattini subgroup of `C_G(Φ(G))` is cyclic. -/
theorem frattiniCentralizer_frattini_isCyclic
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter p G) :
    IsCyclic (frattini (frattiniCentralizer G)) := by
  have hPhiCyclic :
      IsCyclic (frattini G) :=
    frattini_isCyclic_of_omegaOne_frattiniCentralizer_center_isCyclic
      hp hGp hBKN
  letI : IsCyclic (frattini G) := hPhiCyclic
  have hImageCyclic :
      IsCyclic
        ((frattini (frattiniCentralizer G)).map
          (frattiniCentralizer G).subtype) :=
    Subgroup.isCyclic_of_le
      (frattiniCentralizer_map_frattini_le_frattini hp hGp)
  exact
    (Subgroup.equivMapOfInjective
      (frattini (frattiniCentralizer G))
      (frattiniCentralizer G).subtype
      Subtype.coe_injective).isCyclic.mpr hImageCyclic

/-- The Frattini subgroup of `C_G(Φ(G))` is central there. -/
theorem frattiniCentralizer_frattini_le_center
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter p G) :
    frattini (frattiniCentralizer G) ≤
      Subgroup.center (frattiniCentralizer G) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hxPhi : (x : G) ∈ frattini G := by
    apply frattiniCentralizer_map_frattini_le_frattini hp hGp
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hxCenter :=
    frattini_le_frattiniCentralizer_centerImage hp hGp hBKN hxPhi
  rw [characteristicCenterImage_eq_inf_centralizer] at hxCenter
  exact hxCenter.2 y y.2

/-- The Frattini centralizer has nilpotency class at most two. -/
theorem frattiniCentralizer_commutator_le_center
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter p G) :
    commutator (frattiniCentralizer G) ≤
      Subgroup.center (frattiniCentralizer G) :=
  (commutator_le_frattini_of_isPGroup hp
    (hGp.to_subgroup (frattiniCentralizer G))).trans
      (frattiniCentralizer_frattini_le_center hp hGp hBKN)

/-- If the Frattini centralizer is noncommutative, its derived subgroup
has order exactly `p`.  This is fact (1) in the source proof, sharpened
from `≤ p` using noncommutativity. -/
theorem frattiniCentralizer_card_commutator
    {p : ℕ} {G : Type u} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter p G)
    (hnoncomm :
      ¬ IsMulCommutative (frattiniCentralizer G)) :
    Nat.card (commutator (frattiniCentralizer G)) = p := by
  let C : Subgroup G := frattiniCentralizer G
  have hCp : IsPGroup p C := hGp.to_subgroup C
  have hclass : commutator C ≤ Subgroup.center C :=
    frattiniCentralizer_commutator_le_center hp hGp hBKN
  have hCcenter : IsCyclic (Subgroup.center C) :=
    frattiniCentralizer_center_isCyclic hp hGp hBKN
  have hPhiCyclic : IsCyclic (frattini C) :=
    frattiniCentralizer_frattini_isCyclic hp hGp hBKN
  have hpow : ∀ c : commutator C, (c : C) ^ p = 1 :=
    commutator_pow_prime_eq_one_of_frattini_isCyclic
      hp hCp hclass hPhiCyclic
  have hcomm :
      commutator C = centerPrimeKernel p C :=
    commutator_eq_centerPrimeKernel_of_classTwo_of_center_isCyclic
      hp hCp hclass hCcenter hnoncomm hpow
  letI : Nontrivial C := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    apply hnoncomm
    exact ⟨⟨fun x y ↦ hsub.elim (x * y) (y * x)⟩⟩
  rw [hcomm]
  exact card_centerPrimeKernel_of_center_isCyclic
    hp hCp hCcenter

/-- In the `2`-group case, a noncommutative Frattini centralizer has the
exact central-commutator structure used by the affine counting argument. -/
theorem frattiniCentralizer_hasCentralCommutatorOfOrderTwo
    {G : Type u} [Group G] [Finite G]
    (hG2 : IsPGroup 2 G)
    (hBKN : HasCyclicOmegaOneFrattiniCentralizerCenter 2 G)
    (hnoncomm :
      ¬ IsMulCommutative (frattiniCentralizer G)) :
    HasCentralCommutatorOfOrderTwo (frattiniCentralizer G) where
  commutator_le_center :=
    frattiniCentralizer_commutator_le_center
      Nat.prime_two hG2 hBKN
  card_commutator :=
    frattiniCentralizer_card_commutator
      Nat.prime_two hG2 hBKN hnoncomm

end LisiSabatini
