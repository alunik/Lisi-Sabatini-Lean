module

public import LisiSabatini.TwoCoreSymplecticTypeStructure
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Active involutions in the extraspecial--cyclic central-product branch

The active-involution count does not require the plus/minus classification
of extraspecial groups.

Assume that `P'` is central of order two and that `Z(P)` is cyclic.  In a
fixed coset of `Z(P)`, choose one involution `x₀`.  Every other involution
in that coset is uniquely `x₀ z`, where `z ∈ Z(P)` and `z² = 1`.
The kernel of squaring on the cyclic center has order two, because the
central commutator subgroup already has order two.  Hence every central
coset contains at most two involutions.

A fixed-point-free center excludes the identity coset from the active
spectrum.  Summing the fiber bound therefore gives

`# active involutions ≤ 2 * (|P / Z(P)| - 1)`.

This is the elementary active-count input for the
extraspecial--cyclic central-product branch.  It leaves only the
representation-size comparison between `|P/Z(P)|` and the odd
characteristic module.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

/-- The central involutions, represented as the kernel of the squaring
map on the center. -/
abbrev centerSquareKernel
    (P : Type*) [Group P] :=
  (powMonoidHom 2 :
    Subgroup.center P →* Subgroup.center P).ker

/-- A cyclic center containing a subgroup of order two has exactly two
elements killed by squaring. -/
theorem natCard_centerSquareKernel_eq_two
    {P : Type*} [Group P] [Finite P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hcyclic : IsCyclic (Subgroup.center P)) :
    Nat.card (centerSquareKernel P) = 2 := by
  letI : IsCyclic (Subgroup.center P) := hcyclic
  rw [IsCyclic.card_powMonoidHom_ker]
  apply Nat.gcd_eq_right_iff_dvd.mpr
  rw [← hcomm.card_commutator]
  exact Subgroup.card_dvd_of_le hcomm.commutator_le_center

/-- In one coset of a cyclic center, there are at most two active
involutions. -/
theorem centralCoset_activeInvolution_ncard_le_two
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hcyclic : IsCyclic (Subgroup.center P))
    (c : P ⧸ Subgroup.center P) :
    {x : P | x ∈ activePrimeOrderElements 2 P ∧
      QuotientGroup.mk' (Subgroup.center P) x = c}.ncard ≤ 2 := by
  classical
  let S : Set P :=
    {x : P | x ∈ activePrimeOrderElements 2 P ∧
      QuotientGroup.mk' (Subgroup.center P) x = c}
  by_cases hS : S.Nonempty
  · let x₀ : S := ⟨Classical.choose hS, Classical.choose_spec hS⟩
    let f : S → centerSquareKernel P := fun x ↦
      ⟨⟨x₀.1⁻¹ * x.1, by
        rw [← QuotientGroup.eq_one_iff]
        change
          (QuotientGroup.mk' (Subgroup.center P) x₀.1)⁻¹ *
              QuotientGroup.mk' (Subgroup.center P) x.1 = 1
        rw [x₀.2.2, x.2.2, inv_mul_cancel]⟩,
        by
          apply MonoidHom.mem_ker.mpr
          let z : Subgroup.center P :=
            ⟨x₀.1⁻¹ * x.1, by
              rw [← QuotientGroup.eq_one_iff]
              change
                (QuotientGroup.mk'
                    (Subgroup.center P) x₀.1)⁻¹ *
                    QuotientGroup.mk'
                      (Subgroup.center P) x.1 = 1
              rw [x₀.2.2, x.2.2, inv_mul_cancel]⟩
          have hx₀pow : x₀.1 ^ 2 = 1 := by
            have hx₀Order :=
              (mem_activePrimeOrderElements 2 P x₀.1).mp x₀.2.1 |>.1
            rw [← hx₀Order]
            exact pow_orderOf_eq_one x₀.1
          have hxpow : x.1 ^ 2 = 1 := by
            have hxOrder :=
              (mem_activePrimeOrderElements 2 P x.1).mp x.2.1 |>.1
            rw [← hxOrder]
            exact pow_orderOf_eq_one x.1
          have hcommute : Commute x₀.1 z.1 :=
            Subgroup.mem_center_iff.mp z.2 x₀.1
          have hx_eq : x.1 = x₀.1 * z.1 := by
            dsimp only [z]
            group
          apply Subtype.ext
          have hmul := hcommute.mul_pow 2
          rw [← hx_eq, hxpow, hx₀pow, one_mul] at hmul
          exact hmul.symm⟩
    have hf : Function.Injective f := by
      intro x y hxy
      apply Subtype.ext
      have hval :=
        congrArg (fun z : centerSquareKernel P ↦ z.1.1) hxy
      dsimp only [f] at hval
      exact mul_left_cancel hval
    calc
      S.ncard = Nat.card S := Nat.card_coe_set_eq S
      _ ≤ Nat.card (centerSquareKernel P) :=
        Nat.card_le_card_of_injective f hf
      _ = 2 :=
        natCard_centerSquareKernel_eq_two hcomm hcyclic
  · change S.ncard ≤ 2
    rw [Set.not_nonempty_iff_eq_empty.mp hS]
    simp

/-- The active involutions occupy at most two points over each
nonidentity central coset. -/
theorem
    card_activePrimeOrderElements_two_le_two_mul_quotientCenter_pred
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hcyclic : IsCyclic (Subgroup.center P))
    (C : CenterFixedPointFreeAction r d P) :
    (activePrimeOrderElements 2 P).card ≤
      2 * (Nat.card (P ⧸ Subgroup.center P) - 1) := by
  classical
  let Q := P ⧸ Subgroup.center P
  let nonidentityCosets : Finset Q :=
    (Finset.univ : Finset Q).erase 1
  have hmaps :
      ∀ x ∈ activePrimeOrderElements 2 P,
        QuotientGroup.mk' (Subgroup.center P) x ∈
          nonidentityCosets := by
    intro x hx
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ _⟩
    intro hxOne
    have hxCenter :
        x ∈ Subgroup.center P := by
      change (x : P ⧸ Subgroup.center P) = 1 at hxOne
      rw [QuotientGroup.eq_one_iff] at hxOne
      exact hxOne
    have hxActive :
        x ∈ nonzeroFixingElements P :=
      (mem_activePrimeOrderElements 2 P x).mp hx |>.2
    exact C.active_not_mem_center x hxActive hxCenter
  have hfiber :
      ∀ c ∈ nonidentityCosets,
        ((activePrimeOrderElements 2 P).filter fun x ↦
          QuotientGroup.mk' (Subgroup.center P) x = c).card ≤ 2 := by
    intro c _hc
    simpa [← Set.ncard_coe_finset] using
      centralCoset_activeInvolution_ncard_le_two
        P hcomm hcyclic c
  have hcount :=
    Finset.card_le_card_mul_of_fiber_card_le
      (activePrimeOrderElements 2 P)
      (QuotientGroup.mk' (Subgroup.center P))
      nonidentityCosets 2 hmaps hfiber
  have hcardCosets :
      nonidentityCosets.card =
        Nat.card Q - 1 := by
    simp [nonidentityCosets, Nat.card_eq_fintype_card]
  rw [hcardCosets] at hcount
  simpa [Nat.mul_comm] using hcount

/-- Hall's cyclic-characteristic-abelian condition supplies the cyclic
center needed by the preceding elementary count. -/
theorem
    card_activePrimeOrderElements_two_le_two_mul_quotientCenter_pred_of_hall
    {r d : ℕ} [Fact r.Prime]
    (P : Subgroup
      (LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)))
    [Fintype P]
    (hcomm : HasCentralCommutatorOfOrderTwo P)
    (hhall : HasCyclicCharacteristicAbelianSubgroups P)
    (C : CenterFixedPointFreeAction r d P) :
    (activePrimeOrderElements 2 P).card ≤
      2 * (Nat.card (P ⧸ Subgroup.center P) - 1) :=
  card_activePrimeOrderElements_two_le_two_mul_quotientCenter_pred
    P hcomm hhall.center_isCyclic C

end LisiSabatini
