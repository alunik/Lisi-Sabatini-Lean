module

public import LisiSabatini.NilpotentTranslatedRegularityPalette
public import LisiSabatini.ImprimitiveStructuralCore
public import LisiSabatini.FixedPointFreeOrbitAvoidanceCore
public import Mathlib.Algebra.Field.ZMod
public import LisiSabatini.QuasiprimitiveRepresentation
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# The abelian odd Hall base of translated regularity

An abelian odd Hall subgroup of a nilpotent group is central. On a faithful
irreducible module this central subgroup acts freely away from zero. Signed
copies of one of its orbits give the odd-characteristic palette; with at
least two odd prime components the whole vector space supplies the palette
in every characteristic. The counting budgets are proved from distinct
active prime subgroups, not supplied as assumptions.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

set_option backward.isDefEq.respectTransparency false

universe uI uV

/-- Every central subgroup of an irreducible concrete linear group acts freely
away from zero. No finiteness, semisimplicity, or coprimality is needed. -/
theorem map_centralSubgroup_fixedPointFree_of_irreducibleOn
    {r : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod r) V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hirr : IsIrreducibleLinearActionOn K)
    (A : Subgroup K) (hA : A ≤ Subgroup.center K) :
    FixedPointFreeOffZero (A.map K.subtype) := by
  rintro ⟨g, hg⟩ hgOne x hfix
  obtain ⟨a, ha, rfl⟩ := hg
  let U : Submodule (ZMod r) V :=
    LinearMap.ker ((a.1 : Module.End (ZMod r) V) - LinearMap.id)
  have memU (y : V) : y ∈ U ↔ a.1 • y = y := by
    change (((a.1 : Module.End (ZMod r) V) - LinearMap.id : Module.End (ZMod r) V) y = 0) ↔ _
    simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    rfl
  have hUinv : ∀ k : K, ∀ y ∈ U, k.1 • y ∈ U := by
    intro k y hy
    rw [memU] at hy ⊢
    have hak : Commute a k := (Subgroup.mem_center_iff.mp (hA ha) k).symm
    have hgl : Commute a.1 k.1 := hak.map K.subtype
    rw [← mul_smul, hgl.eq, mul_smul, hy]
  rcases hirr U hUinv with hbot | htop
  · have hx : x ∈ U := (memU x).mpr hfix
    simpa [hbot] using hx
  · exfalso
    apply hgOne
    apply Subtype.ext
    apply Units.ext
    apply LinearMap.ext
    intro y
    have hy : y ∈ U := by simp [htop]
    exact (memU y).mp hy


/-- Distinct odd primes dividing a positive integer occupy at most half as many slots. -/
theorem card_le_half_of_distinct_odd_prime_dvd
    {I : Type*} (s : Finset I) (p : I → ℕ) {N : ℕ}
    (hN : 0 < N)
    (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hodd : ∀ i ∈ s, p i ≠ 2)
    (hinj : Set.InjOn p s)
    (hdvd : ∀ i ∈ s, p i ∣ N) :
    s.card ≤ N / 2 := by
  classical
  have hhalfInj : Set.InjOn (fun i ↦ p i / 2) s := by
    intro i hi j hj heq
    apply hinj hi hj
    exact nat_div_two_injective_of_odd
      ((hp i hi).odd_of_ne_two (hodd i hi))
      ((hp j hj).odd_of_ne_two (hodd j hj)) heq
  have hsubset : s.image (fun i ↦ p i / 2) ⊆ Finset.Icc 1 (N / 2) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hpi : 3 ≤ p i := by
      have := (hp i hi).two_le
      have := hodd i hi
      omega
    have hle := Nat.le_of_dvd hN (hdvd i hi)
    exact Finset.mem_Icc.mpr ⟨by omega, Nat.div_le_div_right hle⟩
  calc
    s.card = (s.image (fun i ↦ p i / 2)).card :=
      (Finset.card_image_of_injOn hhalfInj).symm
    _ ≤ (Finset.Icc 1 (N / 2)).card := Finset.card_le_card hsubset
    _ = N / 2 := by simp

/-- The signed scalar palette has strict reserve even when the marked subgroup fills A. -/
theorem signed_scalar_card_reserve
    {m h N : ℕ} (hN : 0 < N) (hm : m ≤ N / 2) (hh : h ≤ N) :
    m + h < 2 * N := by omega

/-- A second odd-prime subgroup gives reserve without adjoining signs. -/
theorem unsigned_scalar_card_reserve
    {m h N : ℕ} (hN : 0 < N) (hm : m ≤ N / 2) (hh : 3 * h ≤ N) :
    m + h < N := by omega

/-- The active odd-prime subgroup count is at most half the ambient group order. -/
theorem card_le_half_of_distinct_odd_pSubgroups
    {A I : Type*} [Group A] [Finite A]
    (s : Finset I) (p : I → ℕ) (H : I → Subgroup A)
    (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hodd : ∀ i ∈ s, p i ≠ 2)
    (hinj : Set.InjOn p s)
    (hP : ∀ i ∈ s, IsPGroup (p i) (H i))
    (hne : ∀ i ∈ s, H i ≠ ⊥) :
    s.card ≤ Nat.card A / 2 := by
  apply card_le_half_of_distinct_odd_prime_dvd s p Nat.card_pos hp hodd hinj
  intro i hi
  let : Fact (p i).Prime := ⟨hp i hi⟩
  have hdvd : p i ∣ Nat.card (H i) :=
    (hP i hi).card_eq_or_dvd.resolve_left fun heq ↦
      hne i hi ((H i).eq_bot_of_card_eq heq)
  exact hdvd.trans (H i).card_subgroup_dvd_card

/-- A nontrivial odd-prime subgroup forces a distinct prime subgroup to use at most a third
of the ambient group order. Neither normality nor commutativity is needed. -/
theorem three_mul_card_le_of_distinct_odd_pSubgroups
    {A : Type*} [Group A] [Finite A]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hodd : p ≠ 2)
    (hpq : p ≠ q) (P Q : Subgroup A)
    (hP : IsPGroup p P) (hQ : IsPGroup q Q) (hne : P ≠ ⊥) :
    3 * Nat.card Q ≤ Nat.card A := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hpDvd : p ∣ Nat.card P := hP.card_eq_or_dvd.resolve_left fun heq ↦
    hne (P.eq_bot_of_card_eq heq)
  have hpLe := Nat.le_of_dvd (Nat.card_pos (α := P)) hpDvd
  have hthree : 3 ≤ Nat.card P := by have := hp.two_le; omega
  have hcop : (Nat.card P).Coprime (Nat.card Q) :=
    IsPGroup.coprime_card_of_ne p q hpq P Q hP hQ
  have hproduct : Nat.card P * Nat.card Q ∣ Nat.card A :=
    hcop.mul_dvd_of_dvd_of_dvd P.card_subgroup_dvd_card Q.card_subgroup_dvd_card
  exact (Nat.mul_le_mul_right (Nat.card Q) hthree).trans
    (Nat.le_of_dvd Nat.card_pos hproduct)

/-- The number of active odd-prime rows and one marked subgroup fit strictly inside A
as soon as there are two distinct active rows. -/
theorem unsigned_scalar_card_reserve_of_two_active_rows
    {A I : Type*} [Group A] [Finite A]
    (s : Finset I) (p : I → ℕ) (H : I → Subgroup A)
    (hp : ∀ i ∈ s, Nat.Prime (p i))
    (hodd : ∀ i ∈ s, p i ≠ 2)
    (hinj : Set.InjOn p s)
    (hP : ∀ i ∈ s, IsPGroup (p i) (H i))
    (hne : ∀ i ∈ s, H i ≠ ⊥)
    (hrows : 1 < s.card) {k : I} (hk : k ∈ s) :
    s.card + Nat.card (H k) < Nat.card A := by
  obtain ⟨j, hj, hjk⟩ := s.exists_mem_ne hrows k
  exact unsigned_scalar_card_reserve Nat.card_pos
    (card_le_half_of_distinct_odd_pSubgroups s p H hp hodd hinj hP hne)
    (three_mul_card_le_of_distinct_odd_pSubgroups
      (hp j hj) (hp k hk) (hodd j hj)
      (fun heq ↦ hjk (hinj hj hk heq)) (H j) (H k) (hP j hj) (hP k hk) (hne j hj))


/-- The center of an irreducible finite prime-field linear group is cyclic. -/
theorem center_isCyclic_of_irreducibleOn
    {r : ℕ} (hr : Nat.Prime r) {V : Type*}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hirr : IsIrreducibleLinearActionOn K) :
    IsCyclic (Subgroup.center K) := by
  classical
  have : Fact (Nat.Prime r) := ⟨hr⟩
  have : Finite K := finite_linearSubgroup_of_finite K
  let A := Subgroup.center K
  let rho : Representation (ZMod r) A V :=
    (linearSubgroupRepresentation K).comp A.subtype
  have hfaith : Function.Injective rho :=
    (linearSubgroupRepresentation_faithful K).comp A.subtype_injective
  by_cases hV : Subsingleton V
  · have : Subsingleton V := hV
    have : Subsingleton (Module.End (ZMod r) V) := inferInstance
    have : Subsingleton A := hfaith.subsingleton
    exact isCyclic_of_subsingleton
  have : Nontrivial V := not_subsingleton_iff_nontrivial.mp hV
  have hfp : FixedPointFreeOffZero (A.map K.subtype) :=
    map_centralSubgroup_fixedPointFree_of_irreducibleOn hirr A le_rfl
  have hdiv : Nat.card A ∣ Nat.card V - 1 := by
    have hd := natCard_dvd_natCard_sub_one_of_fixedPointFreeOffZero
      (A.map K.subtype) hfp
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at hd
  have hrdiv : r ∣ Nat.card V := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod r), Nat.card_zmod]
    exact dvd_pow_self r (ne_of_gt (Module.finrank_pos (R := ZMod r) (M := V)))
  have hrnotdiv : ¬ r ∣ Nat.card V - 1 := by
    intro hd
    have hp : r ∣ 1 := by
      have hsub := Nat.dvd_sub hrdiv hd
      have hpos : 0 < Nat.card V := Nat.card_pos
      have heq : Nat.card V - (Nat.card V - 1) = 1 := by omega
      rwa [heq] at hsub
    exact hr.not_dvd_one hp
  have : NeZero (Nat.card A : ZMod r) := ⟨by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact fun hd => hrnotdiv (hd.trans hdiv)⟩
  apply isCyclic_of_faithful_fixedPointFree_representation rho
  · intro a b
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp a.2 b.1).symm
  · exact hfaith
  · intro a ha x hx
    let a' : A.map K.subtype := ⟨a.1.1, ⟨a.1, a.2, rfl⟩⟩
    have ha' : a' ≠ 1 := by
      intro heq
      apply ha
      exact Subtype.ext (Subtype.ext (congrArg (fun z : A.map K.subtype => z.1) heq))
    exact hfp a' ha' x hx


/-! ## Concrete action images -/

/-- A subgroup of a central subgroup inherits the fixed-point-free
property in the ambient faithful irreducible action. -/
theorem map_subgroup_centralHall_fixedPointFree_of_irreducibleOn
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module (ZMod r) V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hirr : IsIrreducibleLinearActionOn K)
    (A : Subgroup K) (hA : A ≤ Subgroup.center K) (P : Subgroup A) :
    FixedPointFreeOffZero (P.map (K.subtype.comp A.subtype)) := by
  have hcenter : P.map A.subtype ≤ Subgroup.center K :=
    (Subgroup.map_subtype_le P).trans hA
  simpa only [Subgroup.map_map] using
    map_centralSubgroup_fixedPointFree_of_irreducibleOn hirr
      (P.map A.subtype) hcenter

/-- The faithful image of a central subgroup commutes with the faithful
image of every other subgroup. -/
theorem commute_centralHall_images
    {r : ℕ} {V : Type uV} [AddCommGroup V] [Module (ZMod r) V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (T A : Subgroup K) (hA : A ≤ Subgroup.center K) :
    ∀ g : T.map K.subtype, ∀ s : A.map K.subtype,
      Commute (g : LinearMap.GeneralLinearGroup (ZMod r) V)
        (s : LinearMap.GeneralLinearGroup (ZMod r) V) := by
  rintro ⟨g, hg⟩ ⟨s, hs⟩
  obtain ⟨g, hgT, rfl⟩ := hg
  obtain ⟨s, hsA, rfl⟩ := hs
  exact (show Commute g s from (Subgroup.mem_center_iff.mp (hA hsA) g)).map K.subtype

/-- In odd characteristic, a nonzero vector is different from its negative. -/
theorem ne_neg_of_ne_zero_of_prime_char_ne_two
    {r : ℕ} [Fact r.Prime] {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V]
    (hr : r ≠ 2) {a : V} (ha : a ≠ 0) : a ≠ -a := by
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro hzero
    have hdiv : r ∣ 2 := (ZMod.natCast_eq_zero_iff 2 r).mp hzero
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with hone | heq
    · exact (Fact.out : r.Prime).ne_one hone
    · exact hr heq
  intro heq
  have hzero : (2 : ZMod r) • a = 0 := by
    calc
      (2 : ZMod r) • a = a + a := two_smul (ZMod r) a
      _ = a + -a := congrArg (a + ·) heq
      _ = 0 := add_neg_cancel a
  have hcancel := congrArg (fun x : V ↦ (2 : ZMod r)⁻¹ • x) hzero
  rw [smul_smul, inv_mul_cancel₀ htwo, one_smul, smul_zero] at hcancel
  exact ha hcancel

/-- A reference vector can be replaced by a nonzero one without enlarging
its stabilizer. This also handles the zero reference in the scalar base. -/
theorem exists_nonzero_with_stabilizer_le
    {R : Type*} {V : Type uV}
    [Semiring R] [AddCommGroup V] [Module R V] [Nontrivial V]
    (T : Subgroup (LinearMap.GeneralLinearGroup R V)) (a : V) :
    ∃ u : V, u ≠ 0 ∧ MulAction.stabilizer T u ≤ MulAction.stabilizer T a := by
  by_cases ha : a = 0
  · obtain ⟨u, hu⟩ := exists_ne (0 : V)
    refine ⟨u, hu, ?_⟩
    intro g _hg
    rw [MulAction.mem_stabilizer_iff, ha]
    exact smul_zero g
  · exact ⟨a, ha, le_rfl⟩

/-! ## Odd-characteristic scalar base -/

/-- The central odd Hall base in odd characteristic, with its counting
budget derived from the prime-subgroup structure. The distinguished
subgroup is arbitrary: it need not have a regular vector. -/
theorem exists_regular_translates_preserving_stabilizer_of_central_oddHall_of_oddChar
    {r : ℕ} [Fact r.Prime] {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hirr : IsIrreducibleLinearActionOn K) (hr : r ≠ 2)
    (T A : Subgroup K) (hA : A ≤ Subgroup.center K)
    (hoddA : Odd (Nat.card A))
    {I : Type uI} [Finite I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hodd : ∀ i, p i ≠ 2) (hinj : Function.Injective p)
    (P : I → Subgroup A)
    (hP : ∀ i, IsPGroup (p i) (P i)) (hne : ∀ i, P i ≠ ⊥)
    (a b : V) (t : I → V) (k : I) (c : V) :
    ∃ v : V,
      MulAction.stabilizer (T.map K.subtype) (v + b) ≤
        MulAction.stabilizer (T.map K.subtype) a ∧
      (∀ i, MulAction.stabilizer
        ((P i).map (K.subtype.comp A.subtype)) (v + t i) = ⊥) ∧
      v + t k ∉ MulAction.orbit ((P k).map (K.subtype.comp A.subtype)) c := by
  classical
  let : Fintype I := Fintype.ofFinite I
  let : Finite K := finite_linearSubgroup_of_finite K
  let : Finite (A.map K.subtype) := finite_linearSubgroup_of_finite (A.map K.subtype)
  let H : I → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V) :=
    fun i ↦ (P i).map (K.subtype.comp A.subtype)
  have hAfree : FixedPointFreeOffZero (A.map K.subtype) :=
    map_centralSubgroup_fixedPointFree_of_irreducibleOn hirr A hA
  have hHfree : ∀ i, FixedPointFreeOffZero (H i) :=
    fun i ↦ map_subgroup_centralHall_fixedPointFree_of_irreducibleOn hirr A hA (P i)
  have hAcard : Nat.card (A.map K.subtype) = Nat.card A :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hHcard (i : I) : Nat.card (H i) = Nat.card (P i) :=
    Subgroup.card_map_of_injective (K.subtype_injective.comp A.subtype_injective)
  have hrows : Fintype.card I ≤ Nat.card A / 2 := by
    simpa only [Finset.card_univ] using
      card_le_half_of_distinct_odd_pSubgroups Finset.univ p P
        (fun i _ ↦ hp i) (fun i _ ↦ hodd i) hinj.injOn
        (fun i _ ↦ hP i) (fun i _ ↦ hne i)
  have hbudget : Fintype.card I + Nat.card (H k) <
      2 * Nat.card (A.map K.subtype) := by
    rw [hAcard, hHcard]
    exact signed_scalar_card_reserve Nat.card_pos hrows (P k).card_le_card_group
  obtain ⟨u, hu, hule⟩ := exists_nonzero_with_stabilizer_le (T.map K.subtype) a
  obtain ⟨v, hstab, hreg, havoid⟩ :=
    exists_regular_translates_preserving_stabilizer_of_signed_palette
      (T.map K.subtype) (A.map K.subtype) hAfree
      (hAcard.symm ▸ hoddA) (commute_centralHall_images T A hA)
      H hHfree u hu (ne_neg_of_ne_zero_of_prime_char_ne_two hr hu)
      b t k c hbudget
  exact ⟨v, hstab.le.trans hule, hreg, havoid⟩

/-! ## The unsigned base with two active odd components -/

/-- With two distinct active odd-prime components, no signed palette is
needed. This includes characteristic 2. The distinguished group is trivial
in the intended characteristic-2 application. -/
theorem exists_regular_translates_preserving_stabilizer_of_central_oddHall_of_two_oddPrimes
    {r : ℕ} [Fact r.Prime] {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hirr : IsIrreducibleLinearActionOn K)
    (T A : Subgroup K) (hT : T = ⊥) (hA : A ≤ Subgroup.center K)
    {I : Type uI} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hodd : ∀ i, p i ≠ 2) (hinj : Function.Injective p)
    (P : I → Subgroup A)
    (hP : ∀ i, IsPGroup (p i) (P i)) (hne : ∀ i, P i ≠ ⊥)
    (hrows : 2 ≤ Fintype.card I)
    (a b : V) (t : I → V) (k : I) (c : V) :
    ∃ v : V,
      MulAction.stabilizer (T.map K.subtype) (v + b) ≤
        MulAction.stabilizer (T.map K.subtype) a ∧
      (∀ i, MulAction.stabilizer
        ((P i).map (K.subtype.comp A.subtype)) (v + t i) = ⊥) ∧
      v + t k ∉ MulAction.orbit ((P k).map (K.subtype.comp A.subtype)) c := by
  classical
  let : Finite K := finite_linearSubgroup_of_finite K
  let : Finite (A.map K.subtype) := finite_linearSubgroup_of_finite (A.map K.subtype)
  let H : I → Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V) :=
    fun i ↦ (P i).map (K.subtype.comp A.subtype)
  have hAfree : FixedPointFreeOffZero (A.map K.subtype) :=
    map_centralSubgroup_fixedPointFree_of_irreducibleOn hirr A hA
  have hHfree : ∀ i, FixedPointFreeOffZero (H i) :=
    fun i ↦ map_subgroup_centralHall_fixedPointFree_of_irreducibleOn hirr A hA (P i)
  have hAcard : Nat.card (A.map K.subtype) = Nat.card A :=
    Subgroup.card_map_of_injective K.subtype_injective
  have hHcard (i : I) : Nat.card (H i) = Nat.card (P i) :=
    Subgroup.card_map_of_injective (K.subtype_injective.comp A.subtype_injective)
  obtain ⟨u, hu⟩ := exists_ne (0 : V)
  have hAspace : Nat.card A ≤ Nat.card V := by
    rw [← hAcard]
    exact Nat.card_le_card_of_injective _
      (smul_injective_of_fixedPointFreeOffZero (A.map K.subtype) hAfree hu)
  have hsmall : Fintype.card I + Nat.card (H k) < Nat.card A := by
    rw [hHcard]
    simpa only [Finset.card_univ] using
      unsigned_scalar_card_reserve_of_two_active_rows Finset.univ p P
        (fun i _ ↦ hp i) (fun i _ ↦ hodd i) hinj.injOn
        (fun i _ ↦ hP i) (fun i _ ↦ hne i)
        (by simpa only [Finset.card_univ] using (show 1 < Fintype.card I by omega))
        (Finset.mem_univ k)
  obtain ⟨v, hv, havoid⟩ := exists_palette_avoiding_points_and_orbit
    (id : V → V) Function.injective_id (H k) (fun i ↦ -t i) (t k) c
    (hsmall.trans_le hAspace)
  refine ⟨v, ?_, ?_, havoid⟩
  · intro g _hg
    have hg1 : g = 1 := by
      apply Subtype.ext
      change (g : LinearMap.GeneralLinearGroup (ZMod r) V) = 1
      have hgmem := g.property
      simpa only [hT, Subgroup.map_bot, Subgroup.mem_bot] using hgmem
    rw [MulAction.mem_stabilizer_iff, hg1, one_smul]
  · intro i
    apply stabilizer_eq_bot_of_fixedPointFreeOffZero_of_ne_zero (H i) (hHfree i)
    exact fun hzero ↦ hv i (add_eq_zero_iff_eq_neg.mp hzero)

/-! ## Uniform characteristic dispatch -/

/-- A 2-subgroup of a group of odd order is trivial. This small cardinal
argument supplies the defining-characteristic branch below. -/
theorem twoSubgroup_eq_bot_of_coprime_card_two
    {G : Type*} [Group G] [Finite G]
    (T : Subgroup G) (hT : IsPGroup 2 T)
    (hcoprime : (Nat.card G).Coprime 2) : T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hT.card_eq_or_dvd with hcard | hdiv
  · exact T.eq_bot_of_card_eq hcard
  · exact False.elim
      ((Nat.prime_two.coprime_iff_not_dvd.mp hcoprime.symm)
        (hdiv.trans T.card_subgroup_dvd_card))

/-- The full scalar base of the mixed-prime irreducible induction.

The central odd Hall group supplies all odd rows. A nontrivial
2-component or two active odd rows ensures mixed prime support. In odd
characteristic the signed orbit preserves any prescribed 2-stabilizer;
in characteristic 2, coprimality forces the 2-component to be trivial,
and the unsigned palette applies. Neither a regular vector for the
2-component nor any external counting inequality is assumed. -/
theorem exists_regular_translates_preserving_stabilizer_of_central_oddHall
    {r : ℕ} [Fact r.Prime] {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hirr : IsIrreducibleLinearActionOn K)
    (hcoprime : (Nat.card K).Coprime r)
    (T A : Subgroup K) (hT : IsPGroup 2 T)
    (hA : A ≤ Subgroup.center K) (hoddA : Odd (Nat.card A))
    {I : Type uI} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hodd : ∀ i, p i ≠ 2) (hinj : Function.Injective p)
    (P : I → Subgroup A)
    (hP : ∀ i, IsPGroup (p i) (P i)) (hne : ∀ i, P i ≠ ⊥)
    (hsupport : T ≠ ⊥ ∨ 2 ≤ Fintype.card I)
    (a b : V) (t : I → V) (k : I) (c : V) :
    ∃ v : V,
      MulAction.stabilizer (T.map K.subtype) (v + b) ≤
        MulAction.stabilizer (T.map K.subtype) a ∧
      (∀ i, MulAction.stabilizer
        ((P i).map (K.subtype.comp A.subtype)) (v + t i) = ⊥) ∧
      v + t k ∉ MulAction.orbit ((P k).map (K.subtype.comp A.subtype)) c := by
  by_cases hr : r = 2
  · have : Finite K := finite_linearSubgroup_of_finite K
    have hTbot : T = ⊥ := twoSubgroup_eq_bot_of_coprime_card_two T hT (hr ▸ hcoprime)
    have hrows : 2 ≤ Fintype.card I := hsupport.resolve_left (fun hne ↦ hne hTbot)
    exact exists_regular_translates_preserving_stabilizer_of_central_oddHall_of_two_oddPrimes
      hirr T A hTbot hA p hp hodd hinj P hP hne hrows a b t k c
  · exact exists_regular_translates_preserving_stabilizer_of_central_oddHall_of_oddChar
      hirr hr T A hA hoddA p hp hodd hinj P hP hne a b t k c

/-! ## Constructing the central odd group from the active rows -/

/-- A finite commuting family of odd prime-power subgroups generates a
subgroup of odd order. Injectivity of the multiplication map is not needed. -/
theorem odd_card_iSup_of_commuting_odd_primeSubgroups
    {G I : Type*} [Group G] [Finite G] [Finite I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime) (hodd : ∀ i, p i ≠ 2)
    (H : I → Subgroup G) (hP : ∀ i, IsPGroup (p i) (H i))
    (hcomm : Pairwise fun i j ↦ ∀ x y : G,
      x ∈ H i → y ∈ H j → Commute x y) :
    Odd (Nat.card (⨆ i, H i : Subgroup G)) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  have hoddFactor (i : I) : Odd (Nat.card (H i)) := by
    have : Fact (p i).Prime := ⟨hp i⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hP i)
    rw [hn]
    exact ((hp i).odd_of_ne_two (hodd i)).pow
  have hoddPi : Odd (Nat.card (∀ i, H i)) := by
    apply Nat.coprime_two_right.mp
    rw [Nat.card_pi]
    exact Nat.coprime_prod_left_iff.mpr
      (fun i _ ↦ (hoddFactor i).coprime_two_right)
  let f : (∀ i, H i) →* G := Subgroup.noncommPiCoprod hcomm
  have hdvd : Nat.card (⨆ i, H i : Subgroup G) ∣ Nat.card (∀ i, H i) := by
    simpa only [f, Subgroup.noncommPiCoprod_range] using Subgroup.card_range_dvd f
  exact Odd.of_dvd_nat hoddPi hdvd

/-- A direct interface for the scalar leaf: the selected odd components
are central, and the central odd group used by the proof is constructed
internally as their supremum. In a nilpotent action this applies whenever
the selected odd Sylow subgroups are abelian.

The mixed-support condition is essential in characteristic 2; a single
`C₃` acting on `F₄` has only one regular orbit. -/
theorem exists_regular_translates_preserving_stabilizer_of_central_oddComponents
    {r : ℕ} [Fact r.Prime] {V : Type uV}
    [AddCommGroup V] [Module (ZMod r) V] [Finite V] [Nontrivial V]
    {K : Subgroup (LinearMap.GeneralLinearGroup (ZMod r) V)}
    (hirr : IsIrreducibleLinearActionOn K)
    (hcoprime : (Nat.card K).Coprime r)
    (T : Subgroup K) (hT : IsPGroup 2 T)
    {I : Type uI} [Fintype I]
    (p : I → ℕ) (hp : ∀ i, (p i).Prime)
    (hodd : ∀ i, p i ≠ 2) (hinj : Function.Injective p)
    (H : I → Subgroup K)
    (hP : ∀ i, IsPGroup (p i) (H i)) (hne : ∀ i, H i ≠ ⊥)
    (hcentral : ∀ i, H i ≤ Subgroup.center K)
    (hsupport : T ≠ ⊥ ∨ 2 ≤ Fintype.card I)
    (a b : V) (t : I → V) (k : I) (c : V) :
    ∃ v : V,
      MulAction.stabilizer (T.map K.subtype) (v + b) ≤
        MulAction.stabilizer (T.map K.subtype) a ∧
      (∀ i, MulAction.stabilizer ((H i).map K.subtype) (v + t i) = ⊥) ∧
      v + t k ∉ MulAction.orbit ((H k).map K.subtype) c := by
  classical
  have : Finite K := finite_linearSubgroup_of_finite K
  let A : Subgroup K := ⨆ i, H i
  have hHA (i : I) : H i ≤ A := le_iSup H i
  have hA : A ≤ Subgroup.center K := iSup_le hcentral
  have hcomm : Pairwise fun i j ↦ ∀ x y : K,
      x ∈ H i → y ∈ H j → Commute x y := by
    intro i _j _hne x y hx _hy
    exact (Subgroup.mem_center_iff.mp (hcentral i hx) y).symm
  have hoddA : Odd (Nat.card A) :=
    odd_card_iSup_of_commuting_odd_primeSubgroups p hp hodd H hP hcomm
  let P : I → Subgroup A := fun i ↦ (H i).subgroupOf A
  have hPmap (i : I) : (P i).map A.subtype = H i :=
    Subgroup.map_subgroupOf_eq_of_le (hHA i)
  have hPgroup (i : I) : IsPGroup (p i) (P i) :=
    (hP i).comap_subtype
  have hPne (i : I) : P i ≠ ⊥ := by
    intro hbot
    have hmap := hPmap i
    rw [hbot, Subgroup.map_bot] at hmap
    exact hne i hmap.symm
  have himage (i : I) : (P i).map (K.subtype.comp A.subtype) =
      (H i).map K.subtype := by
    rw [← Subgroup.map_map, hPmap]
  obtain ⟨v, hcontain, hregular, havoid⟩ :=
    exists_regular_translates_preserving_stabilizer_of_central_oddHall
      hirr hcoprime T A hT hA hoddA p hp hodd hinj P hPgroup hPne
      hsupport a b t k c
  refine ⟨v, hcontain, ?_, ?_⟩
  · intro i
    have hi := hregular i
    rw [himage i] at hi
    exact hi
  · rw [himage k] at havoid
    exact havoid

end LisiSabatini
