import LisiSabatini.TwoCoreSymplecticTypeHeadRotation

/-!
# Transporting Hall--Berger maximal-class heads

The structural assembly frequently identifies a two-generator head
subgroup with the ambient group, or replaces one concrete copy by an
isomorphic copy.  This file records that the three proof-relevant head
presentations transport across a multiplicative equivalence.
-/

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe u v

namespace IsSemidihedralPresentation

/-- A semidihedral normal-form presentation transports across a group
isomorphism. -/
def ofMulEquiv
    {P : Type u} {Q : Type v}
    [Group P] [Group Q]
    {k : ℕ}
    (h : IsSemidihedralPresentation P k)
    (e : P ≃* Q) :
    IsSemidihedralPresentation Q k where
  normalForm :=
    h.normalForm.trans e.toEquiv
  one_eq_rotation_zero := by
    change e (h.normalForm (.inl 0)) = 1
    rw [h.one_eq_rotation_zero, map_one]
  rotation_mul_rotation := by
    intro i j
    change
      e (h.normalForm (.inl i)) *
          e (h.normalForm (.inl j)) =
        e (h.normalForm (.inl (i + j)))
    rw [← map_mul,
      h.rotation_mul_rotation]
  rotation_mul_coset := by
    intro i j
    change
      e (h.normalForm (.inl i)) *
          e (h.normalForm (.inr j)) =
        e
          (h.normalForm
            (.inr
              (j + semidihedralTwist k * i)))
    rw [← map_mul,
      h.rotation_mul_coset]
  coset_mul_rotation := by
    intro i j
    change
      e (h.normalForm (.inr i)) *
          e (h.normalForm (.inl j)) =
        e (h.normalForm (.inr (i + j)))
    rw [← map_mul,
      h.coset_mul_rotation]
  coset_mul_coset := by
    intro i j
    change
      e (h.normalForm (.inr i)) *
          e (h.normalForm (.inr j)) =
        e
          (h.normalForm
            (.inl
              (j + semidihedralTwist k * i)))
    rw [← map_mul,
      h.coset_mul_coset]

end IsSemidihedralPresentation

namespace BergerMaximalClassHead

/-- A maximal-class Hall--Berger head transports across a group
isomorphism. -/
def ofMulEquiv
    {H : Type u} {K : Type v}
    [Group H] [Finite H]
    [Group K] [Finite K]
    (head : BergerMaximalClassHead H)
    (e : H ≃* K) :
    BergerMaximalClassHead K :=
  match head with
  | .dihedral k hk equiv =>
      .dihedral k hk (e.symm.trans equiv)
  | .semidihedral k hk presentation =>
      .semidihedral k hk
        (presentation.ofMulEquiv e)
  | .generalizedQuaternion n hn equiv =>
      .generalizedQuaternion n hn
        (e.symm.trans equiv)

end BergerMaximalClassHead

end LisiSabatini
