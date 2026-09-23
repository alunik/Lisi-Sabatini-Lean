module

public import LisiSabatini.SylowPairQuadraticBound
public import Mathlib.Data.Real.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Quadratic Sylow-row costs across an index-two subgroup

This file transfers the same-row quadratic conjugacy-class estimate from a
finite group to a normal subgroup of index two.  An ambient conjugacy class
has at most two conjugacy classes of the subgroup above it.  Before
normalization this loses a factor two; normalization by group order loses one
more factor two.  Thus the normalized quadratic cost loses at most a factor
four.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace LisiSabatini

universe uG

local instance quadraticIndexTwoDecidableIsConj
    (G : Type*) [Group G] :
    DecidableRel (IsConj : G → G → Prop) :=
  fun _ _ ↦ Classical.propDecidable _

local instance quadraticIndexTwoDecidableProp (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-! ## Fibers of the map on conjugacy classes -/

/-- Conjugation by an ambient element acts on the conjugacy classes of a
normal subgroup. -/
def normalConjClassTwist
    {G : Type uG} [Group G] (H : Subgroup G) [H.Normal] (g : G) :
    ConjClasses H → ConjClasses H :=
  ConjClasses.map (MulAut.conjNormal g).toMonoidHom

@[simp]
theorem normalConjClassTwist_mk
    {G : Type uG} [Group G] (H : Subgroup G) [H.Normal]
    (g : G) (x : H) :
    normalConjClassTwist H g (ConjClasses.mk x) =
      ConjClasses.mk (MulAut.conjNormal g x) :=
  rfl

/-- Forgetting to the ambient group identifies a class with each of its
normal-subgroup twists. -/
theorem map_subtype_normalConjClassTwist
    {G : Type uG} [Group G] (H : Subgroup G) [H.Normal]
    (g : G) (D : ConjClasses H) :
    ConjClasses.map H.subtype (normalConjClassTwist H g D) =
      ConjClasses.map H.subtype D := by
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep D
  rw [normalConjClassTwist_mk]
  apply ConjClasses.mk_eq_mk_iff_isConj.mpr
  exact
    (isConj_iff.mpr
      ⟨g, MulAut.conjNormal_apply g x⟩).symm

/-- If `H` has index two, the fiber of an ambient conjugacy class is
contained in a pair: one subgroup class and its twist by an element outside
`H`. -/
theorem conjClasses_map_subtype_fiber_subset_pair
    {G : Type uG} [Group G] (H : Subgroup G) [H.Normal]
    (hindex : H.index = 2) {t : G} (ht : t ∉ H)
    {C : ConjClasses G} {D₀ : ConjClasses H}
    (hD₀ : ConjClasses.map H.subtype D₀ = C) :
    {D : ConjClasses H | ConjClasses.map H.subtype D = C} ⊆
      {D₀, normalConjClassTwist H t D₀} := by
  intro D hD
  obtain ⟨x₀, hx₀⟩ := ConjClasses.exists_rep D₀
  obtain ⟨x, hx⟩ := ConjClasses.exists_rep D
  subst D₀
  subst D
  have hambient :
      IsConj (H.subtype x₀) (H.subtype x) := by
    rw [← ConjClasses.mk_eq_mk_iff_isConj]
    exact hD₀.trans hD.symm
  obtain ⟨g, hg⟩ := isConj_iff.mp hambient
  by_cases hgin : g ∈ H
  · left
    symm
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    refine ⟨⟨g, hgin⟩, Subtype.ext ?_⟩
    exact hg
  · right
    rw [Set.mem_singleton_iff]
    symm
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    rw [isConj_iff]
    have htinv : t⁻¹ ∉ H := by
      simpa only [inv_mem_iff] using ht
    have hgt : g * t⁻¹ ∈ H := by
      rw [H.mul_mem_iff_of_index_two hindex]
      exact iff_of_false hgin htinv
    refine ⟨⟨g * t⁻¹, hgt⟩, Subtype.ext ?_⟩
    change (g * t⁻¹) * (t * (x₀ : G) * t⁻¹) *
        (g * t⁻¹)⁻¹ = x
    calc
      (g * t⁻¹) * (t * (x₀ : G) * t⁻¹) *
          (g * t⁻¹)⁻¹ =
          g * (x₀ : G) * g⁻¹ := by group
      _ = x := hg

/-- Each fiber on conjugacy classes induced by the inclusion of an
index-two normal subgroup has cardinality at most two. -/
theorem ncard_conjClasses_map_subtype_fiber_le_two
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) [H.Normal] (hindex : H.index = 2)
    (C : ConjClasses G) :
    {D : ConjClasses H | ConjClasses.map H.subtype D = C}.ncard ≤ 2 := by
  classical
  by_cases hfiber :
      {D : ConjClasses H | ConjClasses.map H.subtype D = C}.Nonempty
  · obtain ⟨D₀, hD₀⟩ := hfiber
    obtain ⟨t, ht, _htcover⟩ :=
      H.index_eq_two_iff_exists_notMem_and.mp hindex
    calc
      {D : ConjClasses H |
          ConjClasses.map H.subtype D = C}.ncard ≤
          ({D₀, normalConjClassTwist H t D₀} :
            Set (ConjClasses H)).ncard :=
        Set.ncard_le_ncard
          (conjClasses_map_subtype_fiber_subset_pair
            H hindex ht hD₀)
          (Set.toFinite _)
      _ ≤ 2 := by
        calc
          ({D₀, normalConjClassTwist H t D₀} :
              Set (ConjClasses H)).ncard ≤
              ({normalConjClassTwist H t D₀} :
                Set (ConjClasses H)).ncard + 1 :=
            Set.ncard_insert_le _ _
          _ = 2 := by simp
  · simpa only [Set.not_nonempty_iff_eq_empty.mp hfiber,
      Set.ncard_empty] using (Nat.zero_le 2)

/-- An ambient class in the image of the inclusion on conjugacy classes
has a representative in the subgroup. -/
theorem carrier_inter_subgroup_nonempty_of_map_subtype_eq
    {G : Type uG} [Group G] (H : Subgroup G)
    {C : ConjClasses G} {D : ConjClasses H}
    (hD : ConjClasses.map H.subtype D = C) :
    (C.carrier ∩ (H : Set G)).Nonempty := by
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep D
  refine ⟨(x : G), ?_, x.property⟩
  rw [ConjClasses.mem_carrier_iff_mk_eq]
  exact hD

/-! ## Pointwise comparison of class rows -/

/-- Intersecting a subgroup class with the linked subgroup row cannot have
more elements than intersecting its ambient class with the ambient row. -/
theorem ncard_conjClass_inter_comap_le
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) (K : Subgroup G) (L : Subgroup H)
    (hKL : K.comap H.subtype = L) (D : ConjClasses H) :
    (D.carrier ∩ (L : Set H)).ncard ≤
      ((ConjClasses.map H.subtype D).carrier ∩
        (K : Set G)).ncard := by
  rw [← Set.ncard_image_of_injective
    (D.carrier ∩ (L : Set H)) Subtype.coe_injective]
  apply Set.ncard_le_ncard
  · rintro y ⟨x, hx, rfl⟩
    rcases hx with ⟨hxD, hxL⟩
    constructor
    · rw [ConjClasses.mem_carrier_iff_mk_eq] at hxD ⊢
      exact congrArg (ConjClasses.map H.subtype) hxD
    · change x ∈ K.comap H.subtype
      rw [hKL]
      exact hxL
  · exact Set.toFinite _

/-- The order-`p` part of a class row cannot shrink after embedding into
the ambient group. -/
theorem ncard_primeOrderConjugacyClassRow_comap_le
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) (p : ℕ) (K : Subgroup G) (L : Subgroup H)
    (hKL : K.comap H.subtype = L) (D : ConjClasses H) :
    (primeOrderConjugacyClassRow p D L).ncard ≤
      (primeOrderConjugacyClassRow p
        (ConjClasses.map H.subtype D) K).ncard := by
  rw [← Set.ncard_image_of_injective
    (primeOrderConjugacyClassRow p D L)
    Subtype.coe_injective]
  apply Set.ncard_le_ncard
  · rintro y ⟨x, hx, rfl⟩
    rw [mem_primeOrderConjugacyClassRow_iff] at hx ⊢
    refine ⟨congrArg (ConjClasses.map H.subtype) hx.1, ?_, ?_⟩
    · change x ∈ K.comap H.subtype
      rw [hKL]
      exact hx.2.1
    · simpa only [orderOf_submonoid] using hx.2.2
  · exact Set.toFinite _

/-- The centralizer of a subgroup element embeds in its ambient
centralizer. -/
theorem card_centralizer_subgroup_le
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) (x : H) :
    Nat.card (Subgroup.centralizer ({x} : Set H)) ≤
      Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) := by
  let f :
      Subgroup.centralizer ({x} : Set H) →
        Subgroup.centralizer ({(x : G)} : Set G) :=
    fun z ↦ ⟨((z : H) : G), by
      have hz := z.property
      rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
      exact congrArg Subtype.val hz⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  have hab' : ((a : H) : G) = ((b : H) : G) := by
    simpa only [f] using
      congrArg
        (fun z : Subgroup.centralizer ({(x : G)} : Set G) ↦
          (z : G)) hab
  apply Subtype.ext
  apply Subtype.ext
  exact hab'

/-- The integer centralizer factor in the quadratic class term cannot
decrease on passage from a subgroup class to its ambient class. -/
theorem card_div_conjClass_subgroup_le
    {G : Type uG} [Group G] [Finite G]
    (H : Subgroup G) (D : ConjClasses H) :
    Nat.card H / D.carrier.ncard ≤
      Nat.card G /
        (ConjClasses.map H.subtype D).carrier.ncard := by
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep D
  change Nat.card H / (ConjClasses.mk x).carrier.ncard ≤
    Nat.card G / (ConjClasses.mk (x : G)).carrier.ncard
  rw [← card_centralizer_eq_card_div_conjugacyClass_ncard,
    ← card_centralizer_eq_card_div_conjugacyClass_ncard]
  exact card_centralizer_subgroup_le H x

/-- Before normalization, a same-row quadratic term in the subgroup is
bounded by the term of its ambient conjugacy class. -/
theorem mixedSylowPairQuadraticClassTerm_subgroup_le
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) {p : ℕ} [Fintype H]
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) (D : ConjClasses H) :
    mixedSylowPairQuadraticClassTerm Q Q D ≤
      mixedSylowPairQuadraticClassTerm P P
        (ConjClasses.map H.subtype D) := by
  unfold mixedSylowPairQuadraticClassTerm
  have hcentral := card_div_conjClass_subgroup_le H D
  have hprime :=
    ncard_primeOrderConjugacyClassRow_comap_le
      H p P Q hPQ D
  have hinter :=
    ncard_conjClass_inter_comap_le H P Q hPQ D
  exact
    Nat.mul_le_mul
      (Nat.mul_le_mul hcentral hprime)
      hinter

/-! ## Fiberwise summation and normalization -/

/-- Before normalization, summing over subgroup conjugacy classes loses at
most a factor two. -/
theorem sum_mixedSylowPairQuadraticClassTerm_subgroup_le_two_mul
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] [Fintype H]
    (hindex : H.index = 2) {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) :
    (∑ D : ConjClasses H,
        mixedSylowPairQuadraticClassTerm Q Q D) ≤
      2 * ∑ C : ConjClasses G,
        mixedSylowPairQuadraticClassTerm P P C := by
  let classMap : ConjClasses H → ConjClasses G :=
    ConjClasses.map H.subtype
  let subTerm : ConjClasses H → ℕ :=
    mixedSylowPairQuadraticClassTerm Q Q
  let ambientTerm : ConjClasses G → ℕ :=
    mixedSylowPairQuadraticClassTerm P P
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (ConjClasses H))
    classMap subTerm]
  calc
    (∑ C : ConjClasses G,
        ∑ D ∈ (Finset.univ : Finset (ConjClasses H)) with
          classMap D = C, subTerm D) ≤
        ∑ C : ConjClasses G, 2 * ambientTerm C := by
      apply Finset.sum_le_sum
      intro C _hC
      have hcard :
          ((Finset.univ : Finset (ConjClasses H)).filter
            fun D ↦ classMap D = C).card ≤ 2 := by
        have hfiber :=
          ncard_conjClasses_map_subtype_fiber_le_two
            H hindex C
        simpa [classMap, Set.ncard_eq_toFinset_card'] using hfiber
      calc
        (∑ D ∈ (Finset.univ : Finset (ConjClasses H)) with
            classMap D = C, subTerm D) ≤
            ∑ _D ∈
                ((Finset.univ : Finset (ConjClasses H)).filter
                  fun D ↦ classMap D = C),
              ambientTerm C := by
          apply Finset.sum_le_sum
          intro D hD
          have hmap : classMap D = C :=
            (Finset.mem_filter.mp hD).2
          calc
            subTerm D ≤ ambientTerm (classMap D) :=
              mixedSylowPairQuadraticClassTerm_subgroup_le
                H P Q hPQ D
            _ = ambientTerm C := congrArg ambientTerm hmap
        _ =
            ((Finset.univ : Finset (ConjClasses H)).filter
              fun D ↦ classMap D = C).card * ambientTerm C := by
          rw [Finset.sum_const_nat]
          intro D _hD
          rfl
        _ ≤ 2 * ambientTerm C :=
          Nat.mul_le_mul_right (ambientTerm C) hcard
    _ = 2 * ∑ C : ConjClasses G, ambientTerm C := by
      rw [Finset.mul_sum]

/-- The ambient classes which can receive a conjugacy class from `H` are
exactly restricted here to those whose carrier meets `H`. -/
def ambientConjClassMeetsSubgroup
    {G : Type uG} [Group G]
    (H : Subgroup G) (C : ConjClasses G) : Prop :=
  (C.carrier ∩ (H : Set G)).Nonempty

/-- For a normal subgroup, an ambient class meets the subgroup exactly when
any chosen representative belongs to the subgroup. -/
@[simp]
theorem ambientConjClassMeetsSubgroup_mk_iff
    {G : Type uG} [Group G]
    (H : Subgroup G) [H.Normal] (x : G) :
    ambientConjClassMeetsSubgroup H (ConjClasses.mk x) ↔ x ∈ H := by
  constructor
  · rintro ⟨y, hyClass, hyH⟩
    rw [ConjClasses.mem_carrier_iff_mk_eq,
      ConjClasses.mk_eq_mk_iff_isConj] at hyClass
    obtain ⟨g, hg⟩ := isConj_iff.mp hyClass
    rw [← hg]
    exact Subgroup.Normal.conj_mem (inferInstance : H.Normal) y hyH g
  · intro hx
    exact
      ⟨x, ConjClasses.mem_carrier_mk, hx⟩

/-- The preceding fiberwise estimate only needs ambient conjugacy classes
whose carrier meets the subgroup.  This restricted form is important for
`A_n ≤ S_n`: for example, odd permutations contribute nothing. -/
theorem sum_mixedSylowPairQuadraticClassTerm_subgroup_le_two_mul_restricted
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] [Fintype H]
    (hindex : H.index = 2) {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) :
    (∑ D : ConjClasses H,
        mixedSylowPairQuadraticClassTerm Q Q D) ≤
      2 * ∑ C : ConjClasses G,
        if ambientConjClassMeetsSubgroup H C then
          mixedSylowPairQuadraticClassTerm P P C
        else 0 := by
  let classMap : ConjClasses H → ConjClasses G :=
    ConjClasses.map H.subtype
  let subTerm : ConjClasses H → ℕ :=
    mixedSylowPairQuadraticClassTerm Q Q
  let ambientTerm : ConjClasses G → ℕ :=
    mixedSylowPairQuadraticClassTerm P P
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (ConjClasses H))
    classMap subTerm]
  calc
    (∑ C : ConjClasses G,
        ∑ D ∈ (Finset.univ : Finset (ConjClasses H)) with
          classMap D = C, subTerm D) ≤
        ∑ C : ConjClasses G,
          2 * (if ambientConjClassMeetsSubgroup H C then
            ambientTerm C else 0) := by
      apply Finset.sum_le_sum
      intro C _hC
      by_cases hmeet : ambientConjClassMeetsSubgroup H C
      · rw [ite_eq_left hmeet]
        have hcard :
            ((Finset.univ : Finset (ConjClasses H)).filter
              fun D ↦ classMap D = C).card ≤ 2 := by
          have hfiber :=
            ncard_conjClasses_map_subtype_fiber_le_two
              H hindex C
          simpa [classMap, Set.ncard_eq_toFinset_card'] using hfiber
        calc
          (∑ D ∈ (Finset.univ : Finset (ConjClasses H)) with
              classMap D = C, subTerm D) ≤
              ∑ _D ∈
                  ((Finset.univ : Finset (ConjClasses H)).filter
                    fun D ↦ classMap D = C),
                ambientTerm C := by
            apply Finset.sum_le_sum
            intro D hD
            have hmap : classMap D = C :=
              (Finset.mem_filter.mp hD).2
            calc
              subTerm D ≤ ambientTerm (classMap D) :=
                mixedSylowPairQuadraticClassTerm_subgroup_le
                  H P Q hPQ D
              _ = ambientTerm C := congrArg ambientTerm hmap
          _ =
              ((Finset.univ : Finset (ConjClasses H)).filter
                fun D ↦ classMap D = C).card * ambientTerm C := by
            rw [Finset.sum_const_nat]
            intro D _hD
            rfl
          _ ≤ 2 * ambientTerm C :=
            Nat.mul_le_mul_right (ambientTerm C) hcard
      · rw [ite_eq_right hmeet, Nat.mul_zero]
        have hempty :
            ((Finset.univ : Finset (ConjClasses H)).filter
              fun D ↦ classMap D = C) = ∅ := by
          apply Finset.filter_eq_empty_iff.mpr
          intro D _hD hmap
          apply hmeet
          exact
            carrier_inter_subgroup_nonempty_of_map_subtype_eq
              H hmap
        change
          (∑ D ∈ ((Finset.univ : Finset (ConjClasses H)).filter
              fun D ↦ classMap D = C), subTerm D) ≤ 0
        rw [hempty]
        simp
    _ = 2 * ∑ C : ConjClasses G,
        if ambientConjClassMeetsSubgroup H C then
          ambientTerm C else 0 := by
      rw [Finset.mul_sum]

/-- The same-row quadratic class-sum normalized by the order of its ambient
group. -/
def normalizedSameRowSylowQuadraticCost
    (G : Type uG) [Group G] [Fintype G]
    {p : ℕ} (P : Sylow p G) : ℝ :=
  ((∑ C : ConjClasses G,
      mixedSylowPairQuadraticClassTerm P P C : ℕ) : ℝ) /
    (Nat.card G : ℝ)

/-- The normalized ambient same-row cost restricted to conjugacy classes
whose carrier meets `H`. -/
def normalizedSameRowSylowQuadraticCostMeetingSubgroup
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) {p : ℕ} (P : Sylow p G) : ℝ :=
  ((∑ C : ConjClasses G,
      if ambientConjClassMeetsSubgroup H C then
        mixedSylowPairQuadraticClassTerm P P C
      else 0 : ℕ) : ℝ) /
    (Nat.card G : ℝ)

/-- A linked Sylow row in an index-two normal subgroup has normalized
quadratic cost at most four times that of the ambient row. -/
theorem normalizedSameRowSylowQuadraticCost_subgroup_le_four_mul
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] [Fintype H]
    (hindex : H.index = 2) {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) :
    normalizedSameRowSylowQuadraticCost H Q ≤
      4 * normalizedSameRowSylowQuadraticCost G P := by
  let subTotal : ℕ :=
    ∑ D : ConjClasses H,
      mixedSylowPairQuadraticClassTerm Q Q D
  let ambientTotal : ℕ :=
    ∑ C : ConjClasses G,
      mixedSylowPairQuadraticClassTerm P P C
  have hsumNat : subTotal ≤ 2 * ambientTotal :=
    sum_mixedSylowPairQuadraticClassTerm_subgroup_le_two_mul
      H hindex P Q hPQ
  have hsumReal :
      (subTotal : ℝ) ≤ 2 * (ambientTotal : ℝ) := by
    exact_mod_cast hsumNat
  have hcardNat : 2 * Nat.card H = Nat.card G := by
    simpa only [hindex] using H.index_mul_card
  have hcardReal :
      2 * (Nat.card H : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast hcardNat
  have hcardPos : (0 : ℝ) < Nat.card H := by
    exact_mod_cast (Nat.card_pos (α := H))
  unfold normalizedSameRowSylowQuadraticCost
  change (subTotal : ℝ) / (Nat.card H : ℝ) ≤
    4 * ((ambientTotal : ℝ) / (Nat.card G : ℝ))
  calc
    (subTotal : ℝ) / (Nat.card H : ℝ) ≤
        (2 * (ambientTotal : ℝ)) / (Nat.card H : ℝ) :=
      div_le_div_of_nonneg_right hsumReal hcardPos.le
    _ = 4 * ((ambientTotal : ℝ) /
        (Nat.card G : ℝ)) := by
      rw [← hcardReal]
      field_simp
      ring

/-- Restricted normalized transfer: only ambient conjugacy classes meeting
the index-two subgroup are charged. -/
theorem
    normalizedSameRowSylowQuadraticCost_subgroup_le_four_mul_restricted
    {G : Type uG} [Group G] [Fintype G]
    (H : Subgroup G) [H.Normal] [Fintype H]
    (hindex : H.index = 2) {p : ℕ}
    (P : Sylow p G) (Q : Sylow p H)
    (hPQ : P.comap H.subtype = Q) :
    normalizedSameRowSylowQuadraticCost H Q ≤
      4 * normalizedSameRowSylowQuadraticCostMeetingSubgroup H P := by
  let subTotal : ℕ :=
    ∑ D : ConjClasses H,
      mixedSylowPairQuadraticClassTerm Q Q D
  let ambientTotal : ℕ :=
    ∑ C : ConjClasses G,
      if ambientConjClassMeetsSubgroup H C then
        mixedSylowPairQuadraticClassTerm P P C
      else 0
  have hsumNat : subTotal ≤ 2 * ambientTotal :=
    sum_mixedSylowPairQuadraticClassTerm_subgroup_le_two_mul_restricted
      H hindex P Q hPQ
  have hsumReal :
      (subTotal : ℝ) ≤ 2 * (ambientTotal : ℝ) := by
    exact_mod_cast hsumNat
  have hcardNat : 2 * Nat.card H = Nat.card G := by
    simpa only [hindex] using H.index_mul_card
  have hcardReal :
      2 * (Nat.card H : ℝ) = (Nat.card G : ℝ) := by
    exact_mod_cast hcardNat
  have hcardPos : (0 : ℝ) < Nat.card H := by
    exact_mod_cast (Nat.card_pos (α := H))
  unfold normalizedSameRowSylowQuadraticCost
    normalizedSameRowSylowQuadraticCostMeetingSubgroup
  change (subTotal : ℝ) / (Nat.card H : ℝ) ≤
    4 * ((ambientTotal : ℝ) / (Nat.card G : ℝ))
  calc
    (subTotal : ℝ) / (Nat.card H : ℝ) ≤
        (2 * (ambientTotal : ℝ)) / (Nat.card H : ℝ) :=
      div_le_div_of_nonneg_right hsumReal hcardPos.le
    _ = 4 * ((ambientTotal : ℝ) /
        (Nat.card G : ℝ)) := by
      rw [← hcardReal]
      field_simp
      ring

/-! ## Alternating groups -/

/-- The uniform factor-four transfer from a linked Sylow row of `S_n` to
its intersection row in `A_n`, valid for every `n ≥ 2`. -/
theorem alternatingLinkedRowQuadraticTransfer
    {n p : ℕ} (hn : 2 ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n)))
    (Q : Sylow p (alternatingGroup (Fin n)))
    (hPQ :
      P.comap (alternatingGroup (Fin n)).subtype = Q) :
    normalizedSameRowSylowQuadraticCost
        (alternatingGroup (Fin n)) Q ≤
      4 * normalizedSameRowSylowQuadraticCost
        (Equiv.Perm (Fin n)) P := by
  let : Nontrivial (Fin n) :=
    Fin.nontrivial_iff_two_le.mpr hn
  exact
    normalizedSameRowSylowQuadraticCost_subgroup_le_four_mul
      (alternatingGroup (Fin n))
      alternatingGroup.index_eq_two P Q hPQ

/-- Restricted form of the alternating/symmetric transfer.  It charges only
the symmetric conjugacy classes which consist of even permutations. -/
theorem alternatingLinkedRowQuadraticTransfer_restricted
    {n p : ℕ} (hn : 2 ≤ n)
    (P : Sylow p (Equiv.Perm (Fin n)))
    (Q : Sylow p (alternatingGroup (Fin n)))
    (hPQ :
      P.comap (alternatingGroup (Fin n)).subtype = Q) :
    normalizedSameRowSylowQuadraticCost
        (alternatingGroup (Fin n)) Q ≤
      4 *
        normalizedSameRowSylowQuadraticCostMeetingSubgroup
          (alternatingGroup (Fin n)) P := by
  let : Nontrivial (Fin n) :=
    Fin.nontrivial_iff_two_le.mpr hn
  exact
    normalizedSameRowSylowQuadraticCost_subgroup_le_four_mul_restricted
      (alternatingGroup (Fin n))
      alternatingGroup.index_eq_two P Q hPQ

end LisiSabatini
