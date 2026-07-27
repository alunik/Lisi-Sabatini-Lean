import LisiSabatini.HallBergerCyclicMaximalSubgroup
import Mathlib.GroupTheory.IndexNormal

/-!
# Uniform outside-coset action in the Hall--Berger square-image branch

The cyclic-head classification is applied to every element outside
`C_G(Φ(G))`, not merely to the first representative used to construct a
seed.  This file isolates the formal group-theoretic part of that argument.

First, any outside element may replace the coset representative in a
Hall--Berger seed.  Second, if every outside element inverts the distinguished
generator of `Φ(G)`, then `C_G(Φ(G))` has index two.  These statements do not
depend on the classification itself.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u

namespace HallBergerCyclicHeadSeed

variable {G : Type u} [Group G] [Finite G]

/-- Any element outside the Frattini centralizer can serve as the coset
representative of a fixed Hall--Berger cyclic-head seed. -/
def replaceCoset
    (hG2 : IsPGroup 2 G)
    (seed : HallBergerCyclicHeadSeed G)
    (h : G)
    (hhOutside : h ∉ frattiniCentralizer G) :
    HallBergerCyclicHeadSeed G where
  rotation := seed.rotation
  coset := h
  rotation_normal := seed.rotation_normal
  rotation_order_ge_eight :=
    seed.rotation_order_ge_eight
  rotation_generates_centerImage :=
    seed.rotation_generates_centerImage
  frattini_eq_rotationSquare :=
    seed.frattini_eq_rotationSquare
  coset_not_mem_frattiniCentralizer :=
    hhOutside
  cosetSquare_mem_rotationSquare := by
    rw [← seed.frattini_eq_rotationSquare]
    exact
      pow_prime_mem_frattini_of_isPGroup
        Nat.prime_two hG2 h
  rotationSquare_not_commute := by
    intro hcommute
    apply hhOutside
    change h ∈
      Subgroup.centralizer (frattini G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyPowers :
        y ∈ Subgroup.zpowers
          (seed.rotation ^ 2) := by
      rw [← seed.frattini_eq_rotationSquare]
      exact hy
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.mp hyPowers
    rw [← hn]
    exact hcommute.zpow_left n

/-- If all elements outside `C_G(Φ(G))` invert the distinguished generator
of `Φ(G)`, then the Frattini centralizer has index two. -/
theorem frattiniCentralizer_index_eq_two_of_outside_inverts_rotationSquare
    (seed : HallBergerCyclicHeadSeed G)
    (hinvert :
      ∀ x : G, x ∉ frattiniCentralizer G →
        x * (seed.rotation ^ 2) * x⁻¹ =
          (seed.rotation ^ 2)⁻¹) :
    (frattiniCentralizer G).index = 2 := by
  classical
  let C : Subgroup G := frattiniCentralizer G
  let a : G := seed.rotation ^ 2
  let h : G := seed.coset
  have hhOutside : h ∉ C :=
    seed.coset_not_mem_frattiniCentralizer
  have hhInvert :
      h * a * h⁻¹ = a⁻¹ :=
    hinvert h hhOutside
  have hhInvertInv :
      h * a⁻¹ * h⁻¹ = a := by
    calc
      h * a⁻¹ * h⁻¹ =
          (h * a * h⁻¹)⁻¹ := by group
      _ = (a⁻¹)⁻¹ := by rw [hhInvert]
      _ = a := inv_inv a
  have hhBack :
      h⁻¹ * a * h = a⁻¹ := by
    calc
      h⁻¹ * a * h =
          h⁻¹ * (h * a⁻¹ * h⁻¹) * h := by
            rw [hhInvertInv]
      _ = a⁻¹ := by group
  have houtsideProduct :
      ∀ x : G, x ∉ C → x * h⁻¹ ∈ C := by
    intro x hxOutside
    have hxInvert :
        x * a * x⁻¹ = a⁻¹ :=
      hinvert x hxOutside
    have hxInvertInv :
        x * a⁻¹ * x⁻¹ = a := by
      calc
        x * a⁻¹ * x⁻¹ =
            (x * a * x⁻¹)⁻¹ := by group
        _ = (a⁻¹)⁻¹ := by rw [hxInvert]
        _ = a := inv_inv a
    have hproductConj :
        (x * h⁻¹) * a * (x * h⁻¹)⁻¹ = a := by
      calc
        (x * h⁻¹) * a * (x * h⁻¹)⁻¹ =
            x * (h⁻¹ * a * h) * x⁻¹ := by
              group
        _ = x * a⁻¹ * x⁻¹ := by rw [hhBack]
        _ = a := hxInvertInv
    have hcommute :
        Commute a (x * h⁻¹) := by
      change a * (x * h⁻¹) =
        (x * h⁻¹) * a
      symm
      calc
        (x * h⁻¹) * a =
            ((x * h⁻¹) * a *
              (x * h⁻¹)⁻¹) *
              (x * h⁻¹) := by
                group
        _ = a * (x * h⁻¹) := by
          rw [hproductConj]
    change x * h⁻¹ ∈
      Subgroup.centralizer (frattini G : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyPowers :
        y ∈ Subgroup.zpowers a := by
      change y ∈
        Subgroup.zpowers (seed.rotation ^ 2)
      rw [← seed.frattini_eq_rotationSquare]
      exact hy
    obtain ⟨n, hn⟩ :=
      Subgroup.mem_zpowers_iff.mp hyPowers
    rw [← hn]
    exact hcommute.zpow_left n
  apply
    (Subgroup.index_eq_two_iff_exists_notMem_and
      (H := C)).mpr
  refine ⟨h⁻¹, ?_, ?_⟩
  · simpa only [inv_mem_iff] using hhOutside
  · intro x
    by_cases hx : x ∈ C
    · exact Or.inr hx
    · exact Or.inl (houtsideProduct x hx)

/-- Once the Frattini centralizer has index two, it and any fixed outside
representative generate the ambient group. -/
theorem frattiniCentralizer_sup_zpowers_eq_top_of_index_two
    (seed : HallBergerCyclicHeadSeed G)
    (hindex : (frattiniCentralizer G).index = 2) :
    frattiniCentralizer G ⊔
        Subgroup.zpowers seed.coset =
      ⊤ := by
  let C : Subgroup G := frattiniCentralizer G
  let H : Subgroup G :=
    C ⊔ Subgroup.zpowers seed.coset
  apply top_unique
  intro x hx
  by_cases hxC : x ∈ C
  · exact
      (show C ≤ H from le_sup_left) hxC
  · have hhOutside :
        seed.coset ∉ C :=
      seed.coset_not_mem_frattiniCentralizer
    have hxCoset :
        x * seed.coset⁻¹ ∈ C := by
      rw [C.mul_mem_iff_of_index_two hindex]
      exact
        iff_of_false hxC
          (by
            simpa only [inv_mem_iff] using
              hhOutside)
    have hxLeft :
        x * seed.coset⁻¹ ∈ H :=
      (show C ≤ H from le_sup_left) hxCoset
    have hxRight :
        seed.coset ∈ H :=
      (show Subgroup.zpowers seed.coset ≤ H
        from le_sup_right)
        (Subgroup.mem_zpowers seed.coset)
    have hxMul :
        (x * seed.coset⁻¹) * seed.coset ∈ H :=
      H.mul_mem hxLeft hxRight
    simpa using hxMul

end HallBergerCyclicHeadSeed

end LisiSabatini
