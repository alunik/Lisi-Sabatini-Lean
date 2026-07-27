import LisiSabatini.MixedSylowIntersections
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Quadratic conjugacy-class bounds for pairs of Sylow subgroups

This file contains the classification-free counting argument behind the
two-Sylow fixed-point-ratio method.

For independently prescribed Sylow subgroups `P` and `Q`, a conjugator `x`
is bad when `P ∩ xQx⁻¹` is nontrivial.  Such an intersection contains an
element of order `p`.  Taking a union over these witnesses and grouping the
resulting transporter sets by conjugacy class gives the integer-scaled
quadratic bound

`∑ C |C_G(g_C)| |C ∩ P| |C ∩ Q|`.

A second union bound over a finite family of prime labels then produces one
conjugator which makes every prescribed intersection trivial.
-/

noncomputable section

open scoped BigOperators Pointwise

namespace LisiSabatini

universe uG uI

local instance sylowPairQuadraticDecidableProp
    (P : Prop) : Decidable P :=
  Classical.propDecidable P

local instance decidableRelIsConjSylowPairQuadratic
    (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

local instance finiteConjActSylowPairQuadratic
    (G : Type*) [Group G] [Finite G] :
    Finite (ConjAct G) :=
  Finite.of_equiv G ConjAct.toConjAct.toEquiv

variable {G : Type uG} [Group G]

/-! ## Bad conjugators and the family union bound -/

/-- Conjugators for which the prescribed two-row Sylow intersection is
nontrivial. -/
def mixedSylowPairBadConjugators
    {p : ℕ} (P Q : Sylow p G) : Set G :=
  {x | mixedSylowInter P Q x ≠ ⊥}

@[simp]
theorem mem_mixedSylowPairBadConjugators_iff
    {p : ℕ} (P Q : Sylow p G) (x : G) :
    x ∈ mixedSylowPairBadConjugators P Q ↔
      mixedSylowInter P Q x ≠ ⊥ :=
  Iff.rfl

@[simp]
theorem not_mem_mixedSylowPairBadConjugators_iff
    {p : ℕ} (P Q : Sylow p G) (x : G) :
    x ∉ mixedSylowPairBadConjugators P Q ↔
      mixedSylowInter P Q x = ⊥ := by
  simp

/-- The union of the rowwise bad loci for a finite family of prescribed
Sylow pairs. -/
def mixedSylowPairBadConjugatorUnion
    {I : Type uI} (p : I → ℕ)
    (P Q : ∀ i, Sylow (p i) G) : Set G :=
  ⋃ i, mixedSylowPairBadConjugators (P i) (Q i)

@[simp]
theorem not_mem_mixedSylowPairBadConjugatorUnion_iff
    {I : Type uI} (p : I → ℕ)
    (P Q : ∀ i, Sylow (p i) G) (x : G) :
    x ∉ mixedSylowPairBadConjugatorUnion p P Q ↔
      ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  simp [mixedSylowPairBadConjugatorUnion]

/-- If the rowwise bad loci have total cardinality smaller than the group,
one conjugator makes all the prescribed mixed intersections trivial. -/
theorem exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt
    {I : Type uI} [Fintype I] [Finite G]
    (p : I → ℕ) (P Q : ∀ i, Sylow (p i) G)
    (hcard :
      ∑ i, (mixedSylowPairBadConjugators (P i) (Q i)).ncard <
        Nat.card G) :
    ∃ x : G, ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  have hunion :
      (mixedSylowPairBadConjugatorUnion p P Q).ncard < Nat.card G := by
    refine
      (Set.ncard_iUnion_le_of_fintype
        (fun i ↦ mixedSylowPairBadConjugators (P i) (Q i))).trans_lt ?_
    simpa [mixedSylowPairBadConjugatorUnion] using hcard
  obtain ⟨x, hx⟩ :=
    (Set.ne_univ_iff_exists_notMem
      (mixedSylowPairBadConjugatorUnion p P Q)).mp (by
      intro hcover
      rw [hcover, Set.ncard_univ] at hunion
      exact (Nat.lt_irrefl _ hunion).elim)
  exact
    ⟨x,
      (not_mem_mixedSylowPairBadConjugatorUnion_iff p P Q x).1 hx⟩

/-! ## Prime-order witnesses -/

/-- A nontrivial mixed intersection of two Sylow `p`-subgroups contains
an element of order exactly `p`. -/
theorem mixedSylowInter_ne_bot_iff_exists_primeOrder_mem
    {p : ℕ} [Fact p.Prime] [Finite G]
    (P Q : Sylow p G) (x : G) :
    mixedSylowInter P Q x ≠ ⊥ ↔
      ∃ g : G,
        orderOf g = p ∧
          g ∈ (P : Subgroup G) ∧
          g ∈ ((x • Q : Sylow p G) : Subgroup G) := by
  let H := mixedSylowInter P Q x
  have hHP : H ≤ (P : Subgroup G) := by
    intro g hg
    exact hg.1
  have hHp : IsPGroup p H :=
    P.isPGroup'.to_le hHP
  constructor
  · intro hH
    have hpCard : p ∣ Nat.card H := by
      rcases hHp.card_eq_or_dvd with hcard | hpCard
      · exact (hH (H.eq_bot_of_card_eq hcard)).elim
      · exact hpCard
    obtain ⟨g, hgOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := H) p hpCard
    exact
      ⟨g.1, (Subgroup.orderOf_coe g).trans hgOrder,
        g.2.1, g.2.2⟩
  · rintro ⟨g, hgOrder, hgP, hgQ⟩
    apply Subgroup.ne_bot_iff_exists_ne_one.mpr
    let gH : H := ⟨g, ⟨hgP, hgQ⟩⟩
    refine ⟨gH, ?_⟩
    intro hgOne
    have hgOne' : g = 1 := by
      simpa [gH] using congrArg Subtype.val hgOne
    have hOrderOne : orderOf g = 1 :=
      orderOf_eq_one_iff.mpr hgOne'
    exact (Fact.out : p.Prime).ne_one (hgOrder.symm.trans hOrderOne)

/-- Conjugators witnessed to be bad by one element `g`. -/
def mixedSylowPairPrimeWitnessConjugators
    {p : ℕ} (P Q : Sylow p G) (g : G) : Set G :=
  {x |
    g ∈ (P : Subgroup G) ∧
      g ∈ ((x • Q : Sylow p G) : Subgroup G)}

/-- Membership in the actual pair-failure locus is equivalent to the
existence of a prime-order witness. -/
theorem mem_mixedSylowPairBadConjugators_iff_exists_primeOrder_witness
    {p : ℕ} [Fact p.Prime] [Finite G]
    (P Q : Sylow p G) (x : G) :
    x ∈ mixedSylowPairBadConjugators P Q ↔
      ∃ g : G,
        orderOf g = p ∧
          x ∈ mixedSylowPairPrimeWitnessConjugators P Q g := by
  rw [mem_mixedSylowPairBadConjugators_iff,
    mixedSylowInter_ne_bot_iff_exists_primeOrder_mem]
  simp only [mixedSylowPairPrimeWitnessConjugators, Set.mem_setOf_eq]

/-- The finite set of elements of order exactly `p`. -/
def primeOrderElements (p : ℕ) (G : Type uG) [Group G] [Fintype G] :
    Finset G :=
  Finset.univ.filter (fun g ↦ orderOf g = p)

@[simp]
theorem mem_primeOrderElements_iff
    {p : ℕ} [Fintype G] (g : G) :
    g ∈ primeOrderElements p G ↔ orderOf g = p := by
  simp [primeOrderElements]

/-- The actual bad set is the union of its prime-order witness sets. -/
theorem mixedSylowPairBadConjugators_eq_iUnion_primeWitness
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q : Sylow p G) :
    mixedSylowPairBadConjugators P Q =
      ⋃ g ∈ (primeOrderElements p G : Set G),
        mixedSylowPairPrimeWitnessConjugators P Q g := by
  ext x
  rw [mem_mixedSylowPairBadConjugators_iff_exists_primeOrder_witness]
  simp only [Set.mem_iUnion, Finset.mem_coe,
    mem_primeOrderElements_iff]
  constructor
  · rintro ⟨g, hgOrder, hgWitness⟩
    exact ⟨g, ⟨hgOrder, hgWitness⟩⟩
  · rintro ⟨g, hgOrder, hgWitness⟩
    exact ⟨g, hgOrder, hgWitness⟩

/-! ## Transporter cardinality -/

/-- Conjugators which move a prescribed Sylow subgroup so that it contains
the element `g`. -/
def sylowConjugatorMembershipSet {p : ℕ}
    (Q : Sylow p G) (g : G) : Set G :=
  {x | g ∈ ((x • Q : Sylow p G) : Subgroup G)}

/-- A witness in the first row contributes exactly one Sylow transporter
set. -/
theorem mixedSylowPairPrimeWitnessConjugators_eq_of_mem
    {p : ℕ} (P Q : Sylow p G) (g : G)
    (hg : g ∈ (P : Subgroup G)) :
    mixedSylowPairPrimeWitnessConjugators P Q g =
      sylowConjugatorMembershipSet Q g := by
  ext x
  simp [mixedSylowPairPrimeWitnessConjugators,
    sylowConjugatorMembershipSet, hg]

/-- An element outside the first row contributes no witnesses. -/
theorem mixedSylowPairPrimeWitnessConjugators_eq_empty_of_not_mem
    {p : ℕ} (P Q : Sylow p G) (g : G)
    (hg : g ∉ (P : Subgroup G)) :
    mixedSylowPairPrimeWitnessConjugators P Q g = ∅ := by
  ext x
  simp [mixedSylowPairPrimeWitnessConjugators, hg]

/-- Exact size of one witness set. -/
theorem ncard_mixedSylowPairPrimeWitnessConjugators
    {p : ℕ} (P Q : Sylow p G) (g : G) :
    (mixedSylowPairPrimeWitnessConjugators P Q g).ncard =
      if g ∈ (P : Subgroup G) then
        (sylowConjugatorMembershipSet Q g).ncard
      else 0 := by
  by_cases hg : g ∈ (P : Subgroup G)
  · rw [if_pos hg,
      mixedSylowPairPrimeWitnessConjugators_eq_of_mem P Q g hg]
  · rw [if_neg hg,
      mixedSylowPairPrimeWitnessConjugators_eq_empty_of_not_mem P Q g hg]
    exact Set.ncard_empty _

/-- Elementwise union bound for actual pair failure. -/
theorem ncard_mixedSylowPairBadConjugators_le_transporter_sum
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard ≤
      ∑ g ∈ primeOrderElements p G,
        (if g ∈ (P : Subgroup G) then
          (sylowConjugatorMembershipSet Q g).ncard
        else 0) := by
  rw [mixedSylowPairBadConjugators_eq_iUnion_primeWitness P Q]
  refine
    ((primeOrderElements p G).set_ncard_biUnion_le
      (mixedSylowPairPrimeWitnessConjugators P Q)).trans_eq ?_
  apply Finset.sum_congr rfl
  intro g _hg
  exact ncard_mixedSylowPairPrimeWitnessConjugators P Q g

/-- The part of the conjugacy class of `g` lying in `H`. -/
def conjugacyClassInter (H : Subgroup G) (g : G) : Set G :=
  MulAction.orbit (ConjAct G) g ∩ (H : Set G)

/-- A nonempty fiber of the orbit map `a ↦ a • b` is equivalent to the
stabilizer of `b`. -/
def smulFiberEquivStabilizer
    {A X : Type*} [Group A] [MulAction A X]
    (b c : X) (a₀ : A) (ha₀ : a₀ • b = c) :
    {a : A // a • b = c} ≃ MulAction.stabilizer A b where
  toFun a :=
    ⟨a₀⁻¹ * a.1, by
      rw [MulAction.mem_stabilizer_iff, mul_smul, a.2, ← ha₀,
        inv_smul_smul]⟩
  invFun k :=
    ⟨a₀ * k.1, by
      rw [mul_smul, MulAction.mem_stabilizer_iff.mp k.2, ha₀]⟩
  left_inv a := by
    apply Subtype.ext
    simp
  right_inv k := by
    apply Subtype.ext
    simp

/-- Every nonempty orbit-map fiber has cardinality equal to the
stabilizer. -/
theorem card_smul_fiber_eq_card_stabilizer
    {A X : Type*} [Group A] [MulAction A X]
    (b c : X) (hc : c ∈ MulAction.orbit A b) :
    Nat.card {a : A // a • b = c} =
      Nat.card (MulAction.stabilizer A b) := by
  obtain ⟨a₀, ha₀⟩ := MulAction.mem_orbit_iff.mp hc
  exact Nat.card_congr (smulFiberEquivStabilizer b c a₀ ha₀)

/-- Conjugators sending `b` into `S` are parametrized by the points of
`orbit(b) ∩ S` together with the corresponding orbit-map fibers. -/
def smulIntoSetEquivSigmaFibers
    {A X : Type*} [Group A] [MulAction A X]
    (b : X) (S : Set X) :
    {a : A // a • b ∈ S} ≃
      Σ c : ↥(MulAction.orbit A b ∩ S),
        {a : A // a • b = c.1} where
  toFun a :=
    ⟨⟨a.1 • b, MulAction.mem_orbit b a.1, a.2⟩, ⟨a.1, rfl⟩⟩
  invFun z :=
    ⟨z.2.1, z.2.2.symm ▸ z.1.2.2⟩
  left_inv a := by
    apply Subtype.ext
    rfl
  right_inv z := by
    rcases z with ⟨⟨c, hcOrbit, hcS⟩, ⟨a, ha⟩⟩
    change a • b = c at ha
    subst c
    rfl

/-- Exact finite orbit-fiber count. -/
theorem ncard_smul_into_set_eq_inter_orbit_mul_card_stabilizer
    {A X : Type*} [Group A] [MulAction A X]
    [Finite A] [Finite X]
    (b : X) (S : Set X) :
    {a : A | a • b ∈ S}.ncard =
      (MulAction.orbit A b ∩ S).ncard *
        Nat.card (MulAction.stabilizer A b) := by
  letI := Fintype.ofFinite A
  letI := Fintype.ofFinite X
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  calc
    Nat.card {a : A // a • b ∈ S} =
        Nat.card
          (Σ c : ↥(MulAction.orbit A b ∩ S),
            {a : A // a • b = c.1}) :=
      Nat.card_congr (smulIntoSetEquivSigmaFibers b S)
    _ = ∑ c : ↥(MulAction.orbit A b ∩ S),
          Nat.card {a : A // a • b = c.1} := Nat.card_sigma
    _ = ∑ _c : ↥(MulAction.orbit A b ∩ S),
          Nat.card (MulAction.stabilizer A b) := by
      apply Finset.sum_congr rfl
      intro c _hc
      exact card_smul_fiber_eq_card_stabilizer b c.1 c.2.1
    _ = Nat.card ↥(MulAction.orbit A b ∩ S) *
          Nat.card (MulAction.stabilizer A b) := by
      simp [Nat.card_eq_fintype_card]

/-- Inversion followed by the `ConjAct` type equivalence. -/
def invToConjActEquiv (G : Type*) [Group G] : G ≃ ConjAct G :=
  (Equiv.inv G).trans ConjAct.toConjAct.toEquiv

/-- The transporter set is carried by `x ↦ x⁻¹` to the ordinary
conjugation-action preimage of the Sylow subgroup. -/
theorem mem_sylowConjugatorMembershipSet_iff_invToConjAct_smul_mem
    {p : ℕ} (Q : Sylow p G) (g x : G) :
    x ∈ sylowConjugatorMembershipSet Q g ↔
      invToConjActEquiv G x • g ∈ (Q : Subgroup G) := by
  rw [show
      x ∈ sylowConjugatorMembershipSet Q g ↔
        g ∈ ((x • Q : Sylow p G) : Subgroup G) from Iff.rfl,
    Sylow.coe_subgroup_smul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  change (MulAut.conj x)⁻¹ g ∈ (Q : Subgroup G) ↔
    invToConjActEquiv G x • g ∈ (Q : Subgroup G)
  rw [← map_inv]
  change (MulAut.conj x⁻¹) g ∈ (Q : Subgroup G) ↔
    (ConjAct.toConjAct x⁻¹ : ConjAct G) • g ∈ (Q : Subgroup G)
  rw [ConjAct.toConjAct_smul_eq_mulAut_conj]

/-- Cardinality is preserved when the transporter is rewritten using
`ConjAct`. -/
theorem ncard_sylowConjugatorMembershipSet_eq_conjAct_preimage
    {p : ℕ}
    (Q : Sylow p G) (g : G) :
    (sylowConjugatorMembershipSet Q g).ncard =
      {a : ConjAct G | a • g ∈ (Q : Subgroup G)}.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  exact Nat.card_congr <|
    (invToConjActEquiv G).subtypeEquiv fun x ↦
      mem_sylowConjugatorMembershipSet_iff_invToConjAct_smul_mem Q g x

/-- The centralizer in `G` and the stabilizer for the conjugation action
have the same cardinality. -/
theorem card_centralizer_eq_card_conjAct_stabilizer (g : G) :
    Nat.card (Subgroup.centralizer {g}) =
      Nat.card (MulAction.stabilizer (ConjAct G) g) := by
  rw [Subgroup.centralizer_eq_comap_stabilizer]
  rfl

/-- Exact transporter formula:

`|{x | g ∈ xQx⁻¹}| = |C_G(g)| |g^G ∩ Q|`.
-/
theorem ncard_sylowConjugatorMembershipSet_eq_centralizer_mul_classInter
    {p : ℕ} [Finite G]
    (Q : Sylow p G) (g : G) :
    (sylowConjugatorMembershipSet Q g).ncard =
      Nat.card (Subgroup.centralizer {g}) *
        (conjugacyClassInter (Q : Subgroup G) g).ncard := by
  rw [ncard_sylowConjugatorMembershipSet_eq_conjAct_preimage]
  change {a : ConjAct G | a • g ∈ (Q : Set G)}.ncard =
    Nat.card (Subgroup.centralizer {g}) *
      (conjugacyClassInter (Q : Subgroup G) g).ncard
  rw [ncard_smul_into_set_eq_inter_orbit_mul_card_stabilizer]
  rw [← card_centralizer_eq_card_conjAct_stabilizer]
  exact Nat.mul_comm _ _

/-- The orbit definition of `conjugacyClassInter` agrees with the intrinsic
carrier of `ConjClasses.mk g`. -/
theorem conjugacyClassInter_eq_carrier_inter
    (H : Subgroup G) (g : G) :
    conjugacyClassInter H g =
      (ConjClasses.mk g).carrier ∩ (H : Set G) := by
  rw [conjugacyClassInter,
    ConjAct.orbit_eq_carrier_conjClasses]

/-- Orbit-stabilizer expressed using the actual centralizer in `G`. -/
theorem conjugacyClass_ncard_mul_card_centralizer
    [Finite G] (g : G) :
    (ConjClasses.mk g).carrier.ncard *
        Nat.card (Subgroup.centralizer {g}) =
      Nat.card G := by
  letI := Fintype.ofFinite G
  have h :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group
      (ConjAct G) g
  have hc :
      Fintype.card (Subgroup.centralizer {g}) =
        Fintype.card (MulAction.stabilizer (ConjAct G) g) := by
    simpa only [Nat.card_eq_fintype_card] using
      card_centralizer_eq_card_conjAct_stabilizer g
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hc]
  simpa only [ConjAct.card,
    ConjAct.orbit_eq_carrier_conjClasses] using h

/-- The centralizer cardinality is the group order divided by the
conjugacy-class size. -/
theorem card_centralizer_eq_card_div_conjugacyClass_ncard
    [Finite G] (g : G) :
    Nat.card (Subgroup.centralizer {g}) =
      Nat.card G / (ConjClasses.mk g).carrier.ncard := by
  apply Nat.eq_div_of_mul_eq_right
  · exact Set.ncard_ne_zero_of_mem ConjClasses.mem_carrier_mk
  · exact conjugacyClass_ncard_mul_card_centralizer g

/-! ## Quadratic class sum -/

/-- Elements of one conjugacy class which lie in a subgroup and have order
exactly `p`. -/
def primeOrderConjugacyClassRow
    (p : ℕ) (C : ConjClasses G) (H : Subgroup G) : Set G :=
  (C.carrier ∩ (H : Set G)) ∩ {g | orderOf g = p}

@[simp]
theorem mem_primeOrderConjugacyClassRow_iff
    (p : ℕ) (C : ConjClasses G) (H : Subgroup G) (g : G) :
    g ∈ primeOrderConjugacyClassRow p C H ↔
      ConjClasses.mk g = C ∧ g ∈ H ∧ orderOf g = p := by
  simp only [primeOrderConjugacyClassRow, Set.mem_inter_iff,
    ConjClasses.mem_carrier_iff_mk_eq, SetLike.mem_coe,
    Set.mem_setOf_eq]
  tauto

/-- The integer-scaled quadratic contribution of one conjugacy class. -/
def mixedSylowPairQuadraticClassTerm
    {p : ℕ} [Fintype G]
    (P Q : Sylow p G) (C : ConjClasses G) : ℕ :=
  (Nat.card G / C.carrier.ncard) *
    (primeOrderConjugacyClassRow p C (P : Subgroup G)).ncard *
    (C.carrier ∩ ((Q : Sylow p G) : Subgroup G)).ncard

/-! ## Independence of the prescribed Sylow rows -/

/-- Conjugation preserves membership in a fixed conjugacy class. -/
theorem mulAut_conj_mem_conjClass_carrier_iff
    (C : ConjClasses G) (g x : G) :
    MulAut.conj g x ∈ C.carrier ↔ x ∈ C.carrier := by
  simp only [ConjClasses.mem_carrier_iff_mk_eq]
  have hmk :
      ConjClasses.mk x = ConjClasses.mk (MulAut.conj g x) := by
    rw [ConjClasses.mk_eq_mk_iff_isConj, isConj_iff]
    exact ⟨g, rfl⟩
  rw [← hmk]

/-- If `g` carries the Sylow row `P` to `Q`, conjugation by `g` carries
membership in `P` exactly to membership in `Q`. -/
theorem mulAut_conj_mem_sylow_iff_of_smul_eq
    {p : ℕ} (P Q : Sylow p G) (g x : G)
    (hg : g • P = Q) :
    MulAut.conj g x ∈ (Q : Subgroup G) ↔ x ∈ (P : Subgroup G) := by
  subst Q
  change
    MulAut.conj g x ∈
        MulAut.conj g • ((P : Subgroup G) : Set G) ↔
      x ∈ (P : Subgroup G)
  exact Set.smul_mem_smul_set_iff

/-- Explicit conjugation equivalence between the intersections of one
conjugacy class with two conjugate Sylow rows. -/
def conjugacyClassInterSylowEquivOfSmulEq
    {p : ℕ} (P Q : Sylow p G) (C : ConjClasses G) (g : G)
    (hg : g • P = Q) :
    (C.carrier ∩ ((P : Subgroup G) : Set G) : Set G) ≃
      (C.carrier ∩ ((Q : Subgroup G) : Set G) : Set G) where
  toFun x :=
    ⟨MulAut.conj g x.1,
      (mulAut_conj_mem_conjClass_carrier_iff C g x.1).2 x.2.1,
      (mulAut_conj_mem_sylow_iff_of_smul_eq P Q g x.1 hg).2 x.2.2⟩
  invFun y :=
    ⟨(MulAut.conj g).symm y.1,
      (mulAut_conj_mem_conjClass_carrier_iff
          C g ((MulAut.conj g).symm y.1)).1 (by
            rw [(MulAut.conj g).apply_symm_apply]
            exact y.2.1),
      (mulAut_conj_mem_sylow_iff_of_smul_eq
          P Q g ((MulAut.conj g).symm y.1) hg).1 (by
            rw [(MulAut.conj g).apply_symm_apply]
            exact y.2.2)⟩
  left_inv x :=
    Subtype.ext ((MulAut.conj g).symm_apply_apply x.1)
  right_inv y :=
    Subtype.ext ((MulAut.conj g).apply_symm_apply y.1)

/-- The cardinality of the intersection of a fixed conjugacy class with a
Sylow subgroup is independent of the prescribed Sylow row. -/
theorem ncard_conjClass_inter_sylow_eq_of_smul_eq
    {p : ℕ} (P Q : Sylow p G) (C : ConjClasses G) (g : G)
    (hg : g • P = Q) :
    (C.carrier ∩ ((P : Subgroup G) : Set G)).ncard =
      (C.carrier ∩ ((Q : Subgroup G) : Set G)).ncard :=
  Set.ncard_congr'
    (conjugacyClassInterSylowEquivOfSmulEq P Q C g hg)

/-- Explicit conjugation equivalence between the order-`p` portions of one
conjugacy class in two conjugate Sylow rows. -/
def primeOrderConjugacyClassRowEquivOfSmulEq
    {p : ℕ} (P Q : Sylow p G) (C : ConjClasses G) (g : G)
    (hg : g • P = Q) :
    primeOrderConjugacyClassRow p C (P : Subgroup G) ≃
      primeOrderConjugacyClassRow p C (Q : Subgroup G) where
  toFun x :=
    ⟨MulAut.conj g x.1,
      ⟨⟨(mulAut_conj_mem_conjClass_carrier_iff C g x.1).2 x.2.1.1,
          (mulAut_conj_mem_sylow_iff_of_smul_eq P Q g x.1 hg).2
            x.2.1.2⟩,
        ((MulAut.conj g).orderOf_eq x.1).trans x.2.2⟩⟩
  invFun y :=
    ⟨(MulAut.conj g).symm y.1,
      ⟨⟨(mulAut_conj_mem_conjClass_carrier_iff
            C g ((MulAut.conj g).symm y.1)).1 (by
              rw [(MulAut.conj g).apply_symm_apply]
              exact y.2.1.1),
          (mulAut_conj_mem_sylow_iff_of_smul_eq
            P Q g ((MulAut.conj g).symm y.1) hg).1 (by
              rw [(MulAut.conj g).apply_symm_apply]
              exact y.2.1.2)⟩,
        ((MulAut.conj g).symm.orderOf_eq y.1).trans y.2.2⟩⟩
  left_inv x :=
    Subtype.ext ((MulAut.conj g).symm_apply_apply x.1)
  right_inv y :=
    Subtype.ext ((MulAut.conj g).apply_symm_apply y.1)

/-- The order-`p` class-row cardinality is independent of the prescribed
Sylow row. -/
theorem ncard_primeOrderConjugacyClassRow_eq_of_smul_eq
    {p : ℕ} (P Q : Sylow p G) (C : ConjClasses G) (g : G)
    (hg : g • P = Q) :
    (primeOrderConjugacyClassRow p C (P : Subgroup G)).ncard =
      (primeOrderConjugacyClassRow p C (Q : Subgroup G)).ncard :=
  Set.ncard_congr'
    (primeOrderConjugacyClassRowEquivOfSmulEq P Q C g hg)

/-- Every mixed quadratic class term is the corresponding same-row term
for any reference Sylow subgroup. -/
theorem mixedSylowPairQuadraticClassTerm_eq_sameRow
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q S : Sylow p G) (C : ConjClasses G) :
    mixedSylowPairQuadraticClassTerm P Q C =
      mixedSylowPairQuadraticClassTerm S S C := by
  obtain ⟨gP, hgP⟩ := MulAction.exists_smul_eq G S P
  obtain ⟨gQ, hgQ⟩ := MulAction.exists_smul_eq G S Q
  have hP :=
    ncard_primeOrderConjugacyClassRow_eq_of_smul_eq
      S P C gP hgP
  have hQ :=
    ncard_conjClass_inter_sylow_eq_of_smul_eq
      S Q C gQ hgQ
  simp only [mixedSylowPairQuadraticClassTerm]
  rw [← hP, ← hQ]

/-- The finite element fiber over a conjugacy class has the expected
first-row multiplicity. -/
theorem card_primeOrderElements_filter_sylow_filter_mk_eq
    {p : ℕ} [Fintype G]
    (P : Sylow p G) (C : ConjClasses G) :
    (((primeOrderElements p G).filter
        (fun g ↦ g ∈ (P : Subgroup G))).filter
          (fun g ↦ ConjClasses.mk g = C)).card =
      (primeOrderConjugacyClassRow p C (P : Subgroup G)).ncard := by
  rw [Set.ncard_eq_toFinset_card]
  congr 1
  ext g
  simp [primeOrderElements,
    mem_primeOrderConjugacyClassRow_iff,
    and_left_comm, and_comm]

/-- The elementwise transporter sum, regrouped by conjugacy class, is
exactly the integer-scaled quadratic class sum. -/
theorem mixedSylowPair_transporter_sum_eq_quadraticClass_sum
    {p : ℕ} [Fintype G]
    (P Q : Sylow p G) :
    (∑ g ∈ primeOrderElements p G,
        (if g ∈ (P : Subgroup G) then
          (sylowConjugatorMembershipSet Q g).ncard
        else 0)) =
      ∑ C : ConjClasses G,
        mixedSylowPairQuadraticClassTerm P Q C := by
  rw [← Finset.sum_filter]
  simp_rw [
    ncard_sylowConjugatorMembershipSet_eq_centralizer_mul_classInter,
    card_centralizer_eq_card_div_conjugacyClass_ncard,
    conjugacyClassInter_eq_carrier_inter]
  let S : Finset G :=
    (primeOrderElements p G).filter
      (fun g ↦ g ∈ (P : Subgroup G))
  let F : ConjClasses G → ℕ := fun C ↦
    (Nat.card G / C.carrier.ncard) *
      (C.carrier ∩ ((Q : Sylow p G) : Subgroup G)).ncard
  change (∑ g ∈ S, F (ConjClasses.mk g)) =
    ∑ C : ConjClasses G,
      mixedSylowPairQuadraticClassTerm P Q C
  calc
    (∑ g ∈ S, F (ConjClasses.mk g)) =
        ∑ C : ConjClasses G,
          ∑ g ∈ S with ConjClasses.mk g = C,
            F (ConjClasses.mk g) := by
      symm
      simpa only [Finset.mem_univ, if_true, Finset.filter_true] using
        (Finset.sum_fiberwise_eq_sum_filter
          S (Finset.univ : Finset (ConjClasses G))
          ConjClasses.mk (fun g ↦ F (ConjClasses.mk g)))
    _ = ∑ C : ConjClasses G,
          (S.filter (fun g ↦ ConjClasses.mk g = C)).card * F C := by
      apply Finset.sum_congr rfl
      intro C _hC
      rw [← Finset.sum_const_nat]
      intro g hg
      exact congrArg F (Finset.mem_filter.mp hg).2
    _ = ∑ C : ConjClasses G,
          mixedSylowPairQuadraticClassTerm P Q C := by
      apply Finset.sum_congr rfl
      intro C _hC
      rw [show
        (S.filter (fun g ↦ ConjClasses.mk g = C)).card =
          (primeOrderConjugacyClassRow p C
            (P : Subgroup G)).ncard by
          simpa [S] using
            card_primeOrderElements_filter_sylow_filter_mk_eq P C]
      simp only [F, mixedSylowPairQuadraticClassTerm]
      ring

/-- Standard quadratic conjugacy-class upper bound for the actual
same-prime pair-failure set. -/
theorem ncard_mixedSylowPairBadConjugators_le_quadraticClass_sum
    {p : ℕ} [Fact p.Prime] [Fintype G]
    (P Q : Sylow p G) :
    (mixedSylowPairBadConjugators P Q).ncard ≤
      ∑ C : ConjClasses G,
        mixedSylowPairQuadraticClassTerm P Q C := by
  rw [← mixedSylowPair_transporter_sum_eq_quadraticClass_sum P Q]
  exact ncard_mixedSylowPairBadConjugators_le_transporter_sum P Q

/-- A strict quadratic class-sum bound over a finite prime family produces
one common conjugator making all prescribed mixed Sylow intersections
trivial.  Injectivity of the prime labels is not needed for this purely
counting implication. -/
theorem exists_common_mixedSylowInter_bot_of_quadraticClass_sum_lt
    {I : Type uI} [Fintype I] [Fintype G]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (P Q : ∀ i, Sylow (p i) G)
    (hclass :
      (∑ i, ∑ C : ConjClasses G,
        mixedSylowPairQuadraticClassTerm (P i) (Q i) C) <
          Nat.card G) :
    ∃ x : G, ∀ i, mixedSylowInter (P i) (Q i) x = ⊥ := by
  apply exists_common_mixedSylowInter_bot_of_sum_bad_ncard_lt p P Q
  refine
    (Finset.sum_le_sum fun i _hi ↦ ?_).trans_lt hclass
  letI : Fact (p i).Prime := ⟨hp i⟩
  exact
    ncard_mixedSylowPairBadConjugators_le_quadraticClass_sum
      (P i) (Q i)

/-- Same-row specialization in the language of the original
Lisi--Sabatini intersection. -/
theorem exists_common_sylowInter_bot_of_quadraticClass_sum_lt
    {I : Type uI} [Fintype I] [Fintype G]
    (p : I → ℕ) (hp : ∀ i, Nat.Prime (p i))
    (P : ∀ i, Sylow (p i) G)
    (hclass :
      (∑ i, ∑ C : ConjClasses G,
        mixedSylowPairQuadraticClassTerm (P i) (P i) C) <
          Nat.card G) :
    ∃ x : G, ∀ i, sylowInter (P i) x = ⊥ := by
  obtain ⟨x, hx⟩ :=
    exists_common_mixedSylowInter_bot_of_quadraticClass_sum_lt
      p hp P P hclass
  exact ⟨x, fun i ↦ by simpa [mixedSylowInter, sylowInter] using hx i⟩

end LisiSabatini
