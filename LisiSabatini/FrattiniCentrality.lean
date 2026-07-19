import LisiSabatini.HallFrattiniReduction
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# From central prime powers to central Frattini subgroup

This file supplies the reverse direction needed after
`HallFrattiniReduction`: in a finite `p`-group, if the derived subgroup and
all `p`-th powers are central, then the Frattini subgroup is central.

The proof is a kernel-checked version of the Burnside-basis argument.  First
we prove that a finite commutative group of exponent `p` has trivial
Frattini subgroup.  A nonzero element is separated by a linear functional
to `ZMod p`; the kernel of the resulting group homomorphism is a maximal
subgroup avoiding that element.  We then quotient by the normal closure of
the `p`-th powers together with the derived subgroup.  The quotient is
elementary abelian, so functoriality of the Frattini subgroup places the
ambient Frattini subgroup inside that central normal subgroup.

Combining this with cyclic-Frattini comparability proves that a finite
class-two `p`-group with cyclic Frattini subgroup has central Frattini
subgroup.  Under Hall's hypothesis it therefore suffices to establish that
the Frattini subgroup is abelian.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

open Subgroup

/-! ## Elementary-abelian groups have trivial Frattini subgroup -/

/-- A finite commutative group of prime exponent has trivial Frattini
subgroup.

This is the elementary-abelian endpoint of the Burnside-basis argument. -/
theorem frattini_eq_bot_of_commutative_of_exponent_prime
    {p : ℕ} {G : Type*} [CommGroup G] [Finite G]
    (hp : p.Prime) (hpow : ∀ g : G, g ^ p = 1) :
    frattini G = ⊥ := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Field (ZMod p) := inferInstance
  letI : Module (ZMod p) (Additive G) :=
    AddCommGroup.zmodModule fun x => by
      apply Additive.toMul.injective
      simpa using hpow (Additive.toMul x)
  letI hfree : Module.Free (ZMod p) (Additive G) :=
    Module.Free.of_divisionRing (ZMod p) (Additive G)
  letI hproj : Module.Projective (ZMod p) (Additive G) :=
    @Module.Projective.of_free (ZMod p) _ (Additive G) _ _ hfree
  apply le_antisymm
  · intro z hz
    rw [Subgroup.mem_bot]
    by_contra hz1
    have hv : Additive.ofMul z ≠ (0 : Additive G) := by
      simpa using hz1
    obtain ⟨f, hf⟩ :=
      @Module.Projective.exists_dual_eq_one (Additive G) _
        (ZMod p) _ _ hproj _ hv
    let phi : G →* Multiplicative (ZMod p) :=
      { toFun := fun g =>
          Multiplicative.ofAdd (f.toFun (Additive.ofMul g))
        map_one' := by simp
        map_mul' := by intro a b; simp }
    have hsurj : Function.Surjective phi := by
      intro a
      refine
        ⟨Additive.toMul
          ((Multiplicative.toAdd a) • Additive.ofMul z), ?_⟩
      apply Multiplicative.toAdd.injective
      change f.toFun ((Multiplicative.toAdd a) • Additive.ofMul z) =
        Multiplicative.toAdd a
      calc
        f.toFun ((Multiplicative.toAdd a) • Additive.ofMul z) =
            (Multiplicative.toAdd a) • f.toFun (Additive.ofMul z) :=
          f.map_smul _ _
        _ = (Multiplicative.toAdd a) • (1 : ZMod p) := by
          exact congrArg
            (fun t : ZMod p => (Multiplicative.toAdd a) • t) hf
        _ = Multiplicative.toAdd a := by rw [smul_eq_mul, mul_one]
    have hkerCoatom : IsCoatom phi.ker := by
      constructor
      · intro htop
        have hzker : z ∈ phi.ker := by
          rw [htop]
          exact Subgroup.mem_top z
        have hzphi := MonoidHom.mem_ker.mp hzker
        change Multiplicative.ofAdd
          (f.toFun (Additive.ofMul z)) = 1 at hzphi
        simp [hf] at hzphi
      · intro H hlt
        obtain ⟨y, hyH, hyker⟩ := SetLike.exists_of_lt hlt
        have hphiy : phi y ≠ 1 := by
          simpa [MonoidHom.mem_ker] using hyker
        rw [Subgroup.eq_top_iff']
        intro g
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
          (mem_zpowers_of_prime_card
            (G := Multiplicative (ZMod p)) (p := p)
            (by simp) hphiy (g' := phi g))
        have hdiff : g * (y ^ n)⁻¹ ∈ phi.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow,
            hn, mul_inv_cancel]
        have hdiffH : g * (y ^ n)⁻¹ ∈ H := hlt.le hdiff
        have hynH : y ^ n ∈ H := H.zpow_mem hyH n
        simpa using H.mul_mem hdiffH hynH
    have hzker : z ∈ phi.ker := frattini_le_coatom hkerCoatom hz
    have hzphi := MonoidHom.mem_ker.mp hzker
    change Multiplicative.ofAdd
      (f.toFun (Additive.ofMul z)) = 1 at hzphi
    simp [hf] at hzphi
  · exact bot_le

/-! ## The prime-power normal closure -/

/-- The normal closure of all ambient `p`-th powers. -/
def primePowerNormalClosure
    (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  Subgroup.normalClosure (Set.range fun x : G => x ^ p)

instance primePowerNormalClosure_normal
    (p : ℕ) (G : Type*) [Group G] :
    (primePowerNormalClosure p G).Normal :=
  Subgroup.normalClosure_normal

/-- **Burnside/Frattini centrality bridge.**

If a finite `p`-group has central derived subgroup and central `p`-th
powers, then its Frattini subgroup is central. -/
theorem frattini_le_center_of_classTwo_of_pow_mem_center
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hclass : commutator G ≤ Subgroup.center G)
    (hpowerCenter : ∀ x : G, x ^ p ∈ Subgroup.center G) :
    frattini G ≤ Subgroup.center G := by
  let Ppow := primePowerNormalClosure p G
  let K : Subgroup G := commutator G ⊔ Ppow
  letI : K.Normal := inferInstance
  have hPpowCenter : Ppow ≤ Subgroup.center G := by
    apply Subgroup.normalClosure_le_normal
    rintro z ⟨x, rfl⟩
    exact hpowerCenter x
  have hKcenter : K ≤ Subgroup.center G :=
    sup_le hclass hPpowCenter
  have hPpowPhi : Ppow ≤ frattini G := by
    apply Subgroup.normalClosure_le_normal
    rintro z ⟨x, rfl⟩
    exact pow_prime_mem_frattini_of_isPGroup hp hGp x
  have hKPhi : K ≤ frattini G :=
    sup_le (commutator_le_frattini_of_isPGroup hp hGp) hPpowPhi
  let Q := G ⧸ K
  have hQpow : ∀ q : Q, q ^ p = 1 := by
    intro q
    refine Quotient.inductionOn' q fun x => ?_
    change (QuotientGroup.mk' K x) ^ p = 1
    rw [← map_pow, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    have hxP : x ^ p ∈ Ppow :=
      Subgroup.subset_normalClosure ⟨x, rfl⟩
    exact (show Ppow ≤ K from le_sup_right) hxP
  have hQcomm : Std.Commutative (· * · : Q → Q → Q) :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
      le_sup_left
  let groupQ : Group Q := inferInstance
  letI : CommGroup Q :=
    { groupQ with
      mul_comm := hQcomm.comm }
  have hQphi : frattini Q = ⊥ :=
    frattini_eq_bot_of_commutative_of_exponent_prime hp hQpow
  have hPhiK : frattini G ≤ K := by
    have hmap := frattini_le_comap_frattini_of_surjective
      (φ := QuotientGroup.mk' K) Quotient.mk''_surjective
    rw [hQphi] at hmap
    rw [← QuotientGroup.ker_mk' K]
    intro x hx
    exact hmap hx
  exact hPhiK.trans hKcenter

/-! ## Cyclic and Hall endpoints -/

/-- A finite class-two `p`-group with cyclic Frattini subgroup has central
Frattini subgroup. -/
theorem frattini_le_center_of_classTwo_of_frattini_isCyclic
    {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hGp : IsPGroup p G)
    (hclass : commutator G ≤ Subgroup.center G)
    (hPhiCyclic : IsCyclic (frattini G)) :
    frattini G ≤ Subgroup.center G := by
  apply frattini_le_center_of_classTwo_of_pow_mem_center
    hp hGp hclass
  exact pow_mem_center_of_frattini_isCyclic
    hp hGp hclass hPhiCyclic

namespace IsHallClassTwoIntermediate

variable {p : ℕ} {P : Type*} [Group P] [Finite P]

/-- A cyclic Frattini subgroup is central in a Hall class-two
intermediate. -/
theorem frattini_le_center_of_frattini_isCyclic
    (h : IsHallClassTwoIntermediate p P)
    (hPhiCyclic : IsCyclic (frattini P)) :
    frattini P ≤ Subgroup.center P :=
  frattini_le_center_of_classTwo_of_frattini_isCyclic
    h.prime h.pGroup h.commutator_le_center hPhiCyclic

/-- Thus the sharpened Hall residual `IsMulCommutative (frattini P)` also
supplies the originally requested central-Frattini conclusion. -/
theorem frattini_le_center_of_frattini_isMulCommutative
    (h : IsHallClassTwoIntermediate p P)
    (hPhiComm : IsMulCommutative (frattini P)) :
    frattini P ≤ Subgroup.center P := by
  letI : IsMulCommutative (frattini P) := hPhiComm
  have hPhiCyclic : IsCyclic (frattini P) :=
    h.hall.isCyclic (frattini P)
  exact h.frattini_le_center_of_frattini_isCyclic hPhiCyclic

end IsHallClassTwoIntermediate

namespace derivedCentralizer

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- Conditional characteristic class-two core endpoint: once the Frattini
subgroup of `C_G(G')` is known abelian, it is in fact central. -/
theorem frattini_le_center_of_frattini_isMulCommutative
    (hp : p.Prime) (hpOdd : Odd p) (hGp : IsPGroup p G)
    (hG : HasCyclicCharacteristicAbelianSubgroups G)
    (hnoncomm : ¬ IsMulCommutative (derivedCentralizer G))
    (hPhiComm : IsMulCommutative (frattini (derivedCentralizer G))) :
    frattini (derivedCentralizer G) ≤
      Subgroup.center (derivedCentralizer G) := by
  let hC := isHallClassTwoIntermediate hp hpOdd hGp hG hnoncomm
  exact hC.frattini_le_center_of_frattini_isMulCommutative hPhiComm

end derivedCentralizer

end LisiSabatini
