module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.PGroup

/-!
# Foundations for the odd Hall p-group structure theorem

The structural theorem needed in the quasiprimitive branch says that, for an
odd prime `p`, a finite `p`-group whose characteristic abelian subgroups are
cyclic is a central product of an extraspecial group and a cyclic group.
Mathlib does not currently contain that classification (nor a definition of
extraspecial groups).  This file develops the part of the argument that can be
proved from the available characteristic-subgroup and commutator APIs.

In particular we prove that characteristicity is transitive through subgroup
inclusion, define the exact cyclic-characteristic-abelian hypothesis, obtain a
cyclic center and cyclic centers for all characteristic subgroups, and isolate
the characteristic centralizer of the derived subgroup.  Its derived subgroup
lies in the center of the original group, so it has nilpotency class at most
two and cyclic center under the Hall hypothesis.

We also introduce a project-local definition of a finite extraspecial
`p`-group by the standard equivalent conditions `G' = Z(G)` and
`|Z(G)| = p`, and record its elementary consequences.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped IsMulCommutative

variable {G : Type*} [Group G]

/-- Restriction of an automorphism to a characteristic subgroup. -/
def characteristicRestrict {H : Subgroup G} (hH : H.Characteristic)
    (e : G ≃* G) : H ≃* H where
  toFun h := ⟨e h, by
    change h.1 ∈ H.comap e.toMonoidHom
    rw [hH.fixed e]
    exact h.2⟩
  invFun h := ⟨e.symm h, by
    change h.1 ∈ H.comap e.symm.toMonoidHom
    rw [hH.fixed e.symm]
    exact h.2⟩
  left_inv h := Subtype.ext (e.symm_apply_apply h)
  right_inv h := Subtype.ext (e.apply_symm_apply h)
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))

@[simp]
theorem coe_characteristicRestrict_apply {H : Subgroup G}
    (hH : H.Characteristic) (e : G ≃* G) (h : H) :
    ((characteristicRestrict hH e h : H) : G) = e h :=
  rfl

/-- Characteristicity is transitive: if `K` is characteristic in `H` and
`H` is characteristic in `G`, then the image of `K` in `G` is
characteristic. -/
theorem characteristic_map_subtype {H : Subgroup G} [hH : H.Characteristic]
    {K : Subgroup H} (hK : K.Characteristic) :
    (K.map H.subtype).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  let eH : H ≃* H := characteristicRestrict hH e
  calc
    (K.map H.subtype).map e.toMonoidHom =
        K.map (e.toMonoidHom.comp H.subtype) :=
      Subgroup.map_map K e.toMonoidHom H.subtype
    _ = K.map (H.subtype.comp eH.toMonoidHom) := by
      rfl
    _ = (K.map eH.toMonoidHom).map H.subtype := by
      rw [Subgroup.map_map]
    _ = K.map H.subtype := by
      rw [Subgroup.characteristic_iff_map_eq.mp hK eH]

/-- In a commutative group, the subgroup of elements annihilated by the
`n`th-power map is characteristic. -/
theorem powMonoidHom_ker_characteristic
    (A : Type*) [CommGroup A] (n : ℕ) :
    ((powMonoidHom n : A →* A).ker).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro e
  ext x
  simp only [Subgroup.mem_comap, MonoidHom.mem_ker,
    powMonoidHom_apply]
  constructor
  · intro hx
    apply e.injective
    simpa using hx
  · intro hx
    rw [← map_pow, hx, map_one]

/-- The center of a subgroup, viewed inside the ambient group. -/
def characteristicCenterImage (H : Subgroup G) : Subgroup G :=
  (Subgroup.center H).map H.subtype

/-- An intrinsic description of `centerImage`: it consists of the elements
of `H` centralizing all of `H`. -/
theorem characteristicCenterImage_eq_inf_centralizer (H : Subgroup G) :
    characteristicCenterImage H =
      H ⊓ Subgroup.centralizer (H : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    refine ⟨z.2, ?_⟩
    change ∀ h ∈ (H : Set G), h * (z : G) = (z : G) * h
    intro h hh
    simpa using congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz ⟨h, hh⟩)
  · intro hx
    refine Subgroup.mem_map.mpr ⟨⟨x, hx.1⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro h
    exact Subtype.ext (hx.2 h h.2)

/-- The center image of a characteristic subgroup is characteristic in the
ambient group. -/
theorem characteristicCenterImage_characteristic
    (H : Subgroup G) [H.Characteristic] :
    (characteristicCenterImage H).Characteristic :=
  characteristic_map_subtype (H := H) Subgroup.centerCharacteristic

/-- The center image is abelian. -/
theorem characteristicCenterImage_isMulCommutative (H : Subgroup G) :
    IsMulCommutative (characteristicCenterImage H) := by
  let : IsMulCommutative (Subgroup.center H) :=
    Subgroup.center.isMulCommutative H
  exact Subgroup.map_isMulCommutative (Subgroup.center H) H.subtype

/-- The ambient center is contained in the center image of every subgroup
that contains it.  In particular this applies to characteristic centralizers. -/
theorem center_le_characteristicCenterImage_of_le {H : Subgroup G}
    (hZH : Subgroup.center G ≤ H) :
    Subgroup.center G ≤ characteristicCenterImage H := by
  rw [characteristicCenterImage_eq_inf_centralizer]
  refine le_inf hZH ?_
  exact Subgroup.center_le_centralizer (H : Set G)

/-! ### The canonical central subgroup of order `p` -/

/-- The elements of `Z(G)` whose `p`th power is one, embedded in `G`.
For a nontrivial finite `p`-group satisfying the Hall hypothesis, this is
the canonical characteristic central subgroup of order `p`. -/
def centerPrimeKernel (p : ℕ) (G : Type*) [Group G] : Subgroup G :=
  ((powMonoidHom p : Subgroup.center G →* Subgroup.center G).ker).map
    (Subgroup.center G).subtype

/-- The canonical central `p`-kernel is characteristic. -/
theorem centerPrimeKernel_characteristic (p : ℕ) (G : Type*) [Group G] :
    (centerPrimeKernel p G).Characteristic := by
  apply characteristic_map_subtype
  exact powMonoidHom_ker_characteristic (Subgroup.center G) p

/-- The canonical central `p`-kernel lies in `Z(G)`. -/
theorem centerPrimeKernel_le_center (p : ℕ) (G : Type*) [Group G] :
    centerPrimeKernel p G ≤ Subgroup.center G :=
  Subgroup.map_subtype_le _

/-- The canonical central `p`-kernel is abelian. -/
theorem centerPrimeKernel_isMulCommutative (p : ℕ) (G : Type*) [Group G] :
    IsMulCommutative (centerPrimeKernel p G) := by
  let K := (powMonoidHom p :
    Subgroup.center G →* Subgroup.center G).ker
  let : IsMulCommutative K := inferInstance
  exact Subgroup.map_isMulCommutative K (Subgroup.center G).subtype

/-- The canonical central kernel remains a `p`-group. -/
theorem centerPrimeKernel_isPGroup {p : ℕ} {G : Type*} [Group G]
    (hGp : IsPGroup p G) : IsPGroup p (centerPrimeKernel p G) := by
  let K := (powMonoidHom p :
    Subgroup.center G →* Subgroup.center G).ker
  exact ((hGp.to_subgroup (Subgroup.center G)).to_subgroup K).map
    (Subgroup.center G).subtype

/-- Every characteristic abelian subgroup of `G` is cyclic.  This is the
precise hypothesis occurring in the odd Hall `p`-group structure theorem. -/
def HasCyclicCharacteristicAbelianSubgroups (G : Type*) [Group G] : Prop :=
  ∀ H : Subgroup G, H.Characteristic → IsMulCommutative H → IsCyclic H

namespace HasCyclicCharacteristicAbelianSubgroups

variable {G : Type*} [Group G]

/-- The center is cyclic. -/
theorem center_isCyclic
    (hG : HasCyclicCharacteristicAbelianSubgroups G) :
    IsCyclic (Subgroup.center G) :=
  hG (Subgroup.center G) inferInstance inferInstance

/-- The canonical characteristic central `p`-kernel is cyclic. -/
theorem centerPrimeKernel_isCyclic
    (hG : HasCyclicCharacteristicAbelianSubgroups G) (p : ℕ) :
    IsCyclic (centerPrimeKernel p G) :=
  hG (centerPrimeKernel p G)
    (centerPrimeKernel_characteristic p G)
    (centerPrimeKernel_isMulCommutative p G)

/-- In a nontrivial finite `p`-group satisfying the Hall hypothesis, the
canonical subgroup `{z ∈ Z(G) | z ^ p = 1}` has order exactly `p`. -/
theorem card_centerPrimeKernel
    [Finite G] [Nontrivial G]
    (hG : HasCyclicCharacteristicAbelianSubgroups G)
    {p : ℕ} (hp : p.Prime) (hGp : IsPGroup p G) :
    Nat.card (centerPrimeKernel p G) = p := by
  let : Fact p.Prime := ⟨hp⟩
  let Z := Subgroup.center G
  let : Finite Z := inferInstance
  let : Nontrivial Z := hGp.center_nontrivial
  let : IsCyclic Z := hG.center_isCyclic
  let K0 := (powMonoidHom p : Z →* Z).ker
  have hp_dvd_cardZ : p ∣ Nat.card Z := by
    have hZp : IsPGroup p Z := hGp.to_subgroup (Subgroup.center G)
    obtain ⟨n, hn, hcard⟩ :=
      (hZp.nontrivial_iff_card.mp (inferInstance : Nontrivial Z))
    rw [hcard]
    exact dvd_pow_self p hn.ne'
  have hcardK0 : Nat.card K0 = (Nat.card Z).gcd p := by
    exact IsCyclic.card_powMonoidHom_ker Z p
  have hcardImage :
      Nat.card (K0.map (Subgroup.center G).subtype) = Nat.card K0 := by
    exact (Nat.card_congr
      (Subgroup.equivMapOfInjective K0 (Subgroup.center G).subtype
        Subtype.coe_injective).toEquiv).symm
  change Nat.card (K0.map (Subgroup.center G).subtype) = p
  calc
    Nat.card (K0.map (Subgroup.center G).subtype) = Nat.card K0 := hcardImage
    _ = (Nat.card Z).gcd p := hcardK0
    _ = p := Nat.gcd_eq_right_iff_dvd.mpr hp_dvd_cardZ

/-- Any characteristic abelian subgroup is cyclic, in a form convenient
when both properties are available as instances. -/
theorem isCyclic (hG : HasCyclicCharacteristicAbelianSubgroups G)
    (H : Subgroup G) [H.Characteristic] [IsMulCommutative H] : IsCyclic H :=
  hG H inferInstance inferInstance

/-- If the derived subgroup happens to be abelian (for example in class at
most two), then it is cyclic. -/
theorem commutator_isCyclic_of_isMulCommutative
    (hG : HasCyclicCharacteristicAbelianSubgroups G)
    (hcomm : IsMulCommutative (commutator G)) :
    IsCyclic (commutator G) := by
  let : IsMulCommutative (commutator G) := hcomm
  exact hG (commutator G) inferInstance inferInstance

/-- The center of every characteristic subgroup, viewed in `G`, is cyclic. -/
theorem centerImage_isCyclic
    (hG : HasCyclicCharacteristicAbelianSubgroups G)
    (H : Subgroup G) [H.Characteristic] :
    IsCyclic (characteristicCenterImage H) :=
  hG (characteristicCenterImage H)
    (characteristicCenterImage_characteristic H)
    (characteristicCenterImage_isMulCommutative H)

/-- Equivalently, the center of every characteristic subgroup is itself
cyclic. -/
theorem characteristic_center_isCyclic
    (hG : HasCyclicCharacteristicAbelianSubgroups G)
    (H : Subgroup G) [H.Characteristic] :
    IsCyclic (Subgroup.center H) := by
  exact (Subgroup.equivMapOfInjective (Subgroup.center H) H.subtype
    Subtype.coe_injective).isCyclic.mpr (hG.centerImage_isCyclic H)

end HasCyclicCharacteristicAbelianSubgroups

/-! ## The characteristic centralizer of the derived subgroup -/

/-- The characteristic centralizer `C_G(G')` used in Hall's argument. -/
def derivedCentralizer (G : Type*) [Group G] : Subgroup G :=
  Subgroup.centralizer (commutator G : Set G)

namespace derivedCentralizer

variable (G : Type*) [Group G]

/-- `C_G(G')` is characteristic. -/
instance characteristic : (derivedCentralizer G).Characteristic := by
  dsimp [derivedCentralizer]
  infer_instance

/-- The center of `G` lies in `C_G(G')`. -/
theorem center_le : Subgroup.center G ≤ derivedCentralizer G :=
  Subgroup.center_le_centralizer (commutator G : Set G)

/-- The ambient image of `Z(C_G(G'))` contains `Z(G)`. -/
theorem center_le_centerImage :
    Subgroup.center G ≤ characteristicCenterImage (derivedCentralizer G) :=
  center_le_characteristicCenterImage_of_le (center_le G)

/-- The derived subgroup of `C_G(G')`, embedded in `G`, lies in `Z(G)`.
This is the three-subgroups-lemma calculation already available in mathlib. -/
theorem map_commutator_le_center :
    (commutator (derivedCentralizer G)).map (derivedCentralizer G).subtype ≤
      Subgroup.center G := by
  rw [Subgroup.map_subtype_commutator]
  exact commutator_centralizer_commutator_le_center G

/-- Consequently `C_G(G')` has nilpotency class at most two: its derived
subgroup lies in its own center. -/
theorem commutator_le_center :
    commutator (derivedCentralizer G) ≤
      Subgroup.center (derivedCentralizer G) := by
  intro x hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  have hxG : (x : G) ∈ Subgroup.center G := by
    apply map_commutator_le_center G
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact Subgroup.mem_center_iff.mp hxG y

/-- The central quotient of `C_G(G')` is abelian. -/
theorem quotient_center_commutative :
    Std.Commutative
      (· * · : (derivedCentralizer G ⧸
        Subgroup.center (derivedCentralizer G)) → _ → _) := by
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    (commutator_le_center G)).is_comm

/-- Under Hall's cyclic-characteristic-abelian hypothesis,
`Z(C_G(G'))` is cyclic. -/
theorem center_isCyclic
    (hG : HasCyclicCharacteristicAbelianSubgroups G) :
    IsCyclic (Subgroup.center (derivedCentralizer G)) :=
  hG.characteristic_center_isCyclic (derivedCentralizer G)

/-- Under the same hypothesis the derived subgroup of `C_G(G')` is cyclic,
because it lies in its cyclic center. -/
theorem commutator_isCyclic
    (hG : HasCyclicCharacteristicAbelianSubgroups G) :
    IsCyclic (commutator (derivedCentralizer G)) := by
  let : IsCyclic (Subgroup.center (derivedCentralizer G)) := center_isCyclic G hG
  exact Subgroup.isCyclic_of_le (commutator_le_center G)

end derivedCentralizer

/-! ## Extraspecial groups -/

/-- A finite extraspecial `p`-group.  For finite `p`-groups, the conditions
`G' = Z(G)` and `|Z(G)| = p` are the standard equivalent definition (and
imply that the common subgroup also equals the Frattini subgroup). -/
structure IsExtraspecial (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop where
  prime : p.Prime
  pGroup : IsPGroup p G
  commutator_eq_center : commutator G = Subgroup.center G
  card_center : Nat.card (Subgroup.center G) = p

/-- An extraspecial group at an odd prime. -/
structure IsOddExtraspecial (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop
    extends IsExtraspecial p G where
  odd : Odd p

namespace IsExtraspecial

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- The center of an extraspecial group is cyclic. -/
theorem center_isCyclic (h : IsExtraspecial p G) :
    IsCyclic (Subgroup.center G) := by
  let : Fact p.Prime := ⟨h.prime⟩
  exact isCyclic_of_prime_card h.card_center

/-- The derived subgroup of an extraspecial group is cyclic. -/
theorem commutator_isCyclic (h : IsExtraspecial p G) :
    IsCyclic (commutator G) := by
  rw [h.commutator_eq_center]
  exact h.center_isCyclic

/-- The central quotient of an extraspecial group is abelian. -/
theorem quotient_center_commutative (h : IsExtraspecial p G) :
    Std.Commutative
      (· * · : (G ⧸ Subgroup.center G) → _ → _) := by
  exact (Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    h.commutator_eq_center.le).is_comm

/-- An extraspecial group is nonabelian. -/
theorem not_isMulCommutative (h : IsExtraspecial p G) :
    ¬ IsMulCommutative G := by
  intro hcomm
  have hbot : commutator G = ⊥ := by
    rw [commutator_eq_bot_iff_center_eq_top]
    exact @CommGroup.center_eq_top G
      { ‹Group G› with mul_comm := hcomm.1.1 }
  have hcenterBot : Subgroup.center G = ⊥ := by
    rw [← h.commutator_eq_center]
    exact hbot
  have hone : Nat.card (Subgroup.center G) = 1 := by
    rw [hcenterBot, Subgroup.card_bot]
  have : p = 1 := h.card_center.symm.trans hone
  exact h.prime.ne_one this

end IsExtraspecial

end LisiSabatini
