module

public import LisiSabatini.LinearAction
public import LisiSabatini.PCore
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Coordinatized elementary-abelian normal sections

Mathlib does not currently provide a chief-series interface suitable for the
induction used in the low-chief-rank theorem.  We therefore make the local
data needed by the affine lift explicit.  In particular, no canonical scalar
action is imposed on an abstract normal subgroup: additive coordinates and
the corresponding linear conjugation action are supplied as data.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uG

variable {G : Type uG} [Group G]

/-- Mathlib's conjugation homomorphism on an explicitly normal subgroup. -/
def normalConjHom (N : Subgroup G) (hN : N.Normal) : G →* MulAut N := by
  letI : N.Normal := hN
  exact MulAut.conjNormal

/-- Conjugation by `g`, restricted to a normal subgroup.  This compatibility
spelling evaluates `MulAut.conjNormal`. -/
abbrev normalConj (N : Subgroup G) (hN : N.Normal) (g : G) : MulAut N :=
  normalConjHom N hN g

@[simp]
theorem coe_normalConj (N : Subgroup G) (hN : N.Normal) (g : G) (n : N) :
    (normalConj N hN g n : G) = g * n * g⁻¹ := by
  letI : N.Normal := hN
  exact MulAut.conjNormal_apply g n

@[simp]
theorem normalConj_one (N : Subgroup G) (hN : N.Normal) (n : N) :
    normalConj N hN 1 n = n := by
  change normalConjHom N hN 1 n = n
  rw [map_one]
  rfl

@[simp]
theorem normalConj_mul (N : Subgroup G) (hN : N.Normal) (g h : G) (n : N) :
    normalConj N hN (g * h) n = normalConj N hN g (normalConj N hN h n) := by
  change normalConjHom N hN (g * h) n =
    normalConjHom N hN g (normalConjHom N hN h n)
  rw [map_mul]
  rfl

/-- A normal subgroup supplied with elementary-abelian coordinates and the
linear action obtained from conjugation in the ambient group.

The exponent field is deliberately retained even though it follows
mathematically from the coordinate equivalence.  It is the most convenient
interface for building the group-theoretic side of a normal tower, while the
coordinates are the convenient interface for the affine counting side. -/
structure ElementaryAbelianSection (G : Type uG) [Group G] where
  /-- Characteristic of the coordinate field. -/
  r : ℕ
  /-- Dimension of the coordinate space. -/
  d : ℕ
  prime : Nat.Prime r
  /-- The normal subgroup represented by this section. -/
  N : Subgroup G
  normal : N.Normal
  /-- Explicit additive coordinates on the section. -/
  coordinates : Additive N ≃+ (Fin d → ZMod r)
  /-- Every element has exponent dividing the field characteristic. -/
  exponent_eq_one : ∀ n : N, n ^ r = 1
  /-- Conjugation, transported to the coordinate space. -/
  conjugation : G →* LinearMap.GeneralLinearGroup (ZMod r) (Fin d → ZMod r)
  /-- The supplied linear action really is ambient conjugation. -/
  conjugation_apply : ∀ (g : G) (n : N),
    conjugation g • coordinates (Additive.ofMul n) =
      coordinates (Additive.ofMul (normalConj N normal g n))

namespace ElementaryAbelianSection

variable (S : ElementaryAbelianSection G)

/-- The abstract subgroup has exactly the cardinality of its coordinate
space. -/
theorem natCard_N : Nat.card S.N = S.r ^ S.d := by
  calc
    Nat.card S.N = Nat.card (Additive S.N) :=
      Nat.card_congr Additive.ofMul
    _ = Nat.card (Fin S.d → ZMod S.r) :=
      Nat.card_congr S.coordinates.toEquiv
    _ = S.r ^ S.d := by
      rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]

/-- A section of positive dimension is nontrivial. -/
theorem one_lt_natCard_N (hd : 0 < S.d) : 1 < Nat.card S.N := by
  rw [S.natCard_N]
  exact one_lt_pow₀ S.prime.one_lt hd.ne'

/-- The supplied exponent certificate makes the section an `r`-group. -/
theorem isPGroup : IsPGroup S.r S.N := by
  intro n
  refine ⟨1, ?_⟩
  simpa using S.exponent_eq_one n

/-- Additive coordinates certify that the underlying normal subgroup is
abelian, without installing a global `CommGroup` instance on its subtype. -/
theorem commute (a b : S.N) : Commute a b := by
  rw [Commute]
  apply Additive.ofMul.injective
  apply S.coordinates.injective
  simp [add_comm]

/-- The action kernel consists exactly of the ambient elements centralizing
the section pointwise, expressed in coordinates. -/
theorem mem_conjugation_ker_iff (g : G) :
    g ∈ S.conjugation.ker ↔ ∀ n : S.N, normalConj S.N S.normal g n = n := by
  constructor
  · intro hg n
    have hcompat := S.conjugation_apply g n
    rw [MonoidHom.mem_ker.mp hg, one_smul] at hcompat
    exact Additive.ofMul.injective (S.coordinates.injective hcompat.symm)
  · intro hg
    rw [MonoidHom.mem_ker]
    apply Units.ext
    apply LinearMap.ext
    intro v
    change S.conjugation g • v = v
    let n : S.N := Additive.toMul (S.coordinates.symm v)
    have hcompat := S.conjugation_apply g n
    simpa [n, hg] using hcompat

/-- Ambient form of the preceding kernel calculation: the representation
kernel is the pointwise centralizer of the normal section. -/
theorem mem_conjugation_ker_iff_mem_centralizer (g : G) :
    g ∈ S.conjugation.ker ↔
      g ∈ Subgroup.centralizer (S.N : Set G) := by
  rw [S.mem_conjugation_ker_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h n hn
    let nS : S.N := ⟨n, hn⟩
    have hc := congrArg Subtype.val (h nS)
    rw [coe_normalConj] at hc
    dsimp [nS] at hc
    calc
      n * g = (g * n * g⁻¹) * g := congrArg (· * g) hc.symm
      _ = g * n := by simp [mul_assoc]
  · intro h n
    apply Subtype.ext
    rw [coe_normalConj]
    have hc := h n n.2
    calc
      g * (n : G) * g⁻¹ = n * g * g⁻¹ := by rw [hc]
      _ = n := by simp

end ElementaryAbelianSection

end LisiSabatini
