import Mathlib.GroupTheory.Frattini

/-!
# Frattini subgroups and quotients

The Frattini subgroup maps onto the Frattini subgroup of a quotient whenever
the kernel is contained in the source Frattini subgroup.  The result is stated
first for an arbitrary surjective homomorphism; the quotient formula is then
an immediate specialization.
-/

open Subgroup

/-- A maximal subgroup containing the kernel of a surjective homomorphism
maps to a maximal subgroup of the codomain. -/
theorem isCoatom_map_of_surjective_of_ker_le
    {G H : Type*} [Group G] [Group H]
    {phi : G →* H} (hphi : Function.Surjective phi)
    {M : Subgroup G} (hker : phi.ker ≤ M) (hM : IsCoatom M) :
    IsCoatom (M.map phi) := by
  constructor
  · intro hmap
    apply hM.ne_top
    rw [← Subgroup.comap_map_eq_self hker, hmap, Subgroup.comap_top]
  · intro K hmapK
    have hcomapK : M < K.comap phi := by
      rw [← Subgroup.comap_map_eq_self hker]
      exact (Subgroup.comap_lt_comap_of_surjective hphi).mpr hmapK
    have htop : K.comap phi = ⊤ := hM.2 _ hcomapK
    apply Subgroup.comap_injective hphi
    simpa only [Subgroup.comap_top] using htop

/-- Frattini subgroups commute with a surjective homomorphism when its kernel
is contained in the source Frattini subgroup.  No finiteness hypothesis is
needed. -/
theorem map_frattini_eq_frattini_of_surjective_of_ker_le
    {G H : Type*} [Group G] [Group H]
    {phi : G →* H} (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ frattini G) :
    (frattini G).map phi = frattini H := by
  apply le_antisymm
  · exact Subgroup.map_le_iff_le_comap.mpr
      (frattini_le_comap_frattini_of_surjective hphi)
  · intro y hy
    obtain ⟨x, rfl⟩ := hphi y
    apply Subgroup.mem_map_of_mem
    rw [frattini, Order.radical, Subgroup.mem_iInf]
    intro M
    rw [Subgroup.mem_iInf]
    intro hM
    have hkerM : phi.ker ≤ M := hker.trans (frattini_le_coatom hM)
    have hphiM : IsCoatom (M.map phi) :=
      isCoatom_map_of_surjective_of_ker_le hphi hkerM hM
    have hxmap : phi x ∈ M.map phi := frattini_le_coatom hphiM hy
    have hxcomap : x ∈ (M.map phi).comap phi := hxmap
    rwa [Subgroup.comap_map_eq_self hkerM] at hxcomap

/-- Equivalent pullback form of
`map_frattini_eq_frattini_of_surjective_of_ker_le`. -/
theorem comap_frattini_eq_frattini_of_surjective_of_ker_le
    {G H : Type*} [Group G] [Group H]
    {phi : G →* H} (hphi : Function.Surjective phi)
    (hker : phi.ker ≤ frattini G) :
    (frattini H).comap phi = frattini G := by
  rw [← map_frattini_eq_frattini_of_surjective_of_ker_le hphi hker]
  exact Subgroup.comap_map_eq_self hker

/-- Quotient formula for the Frattini subgroup.  A normal subgroup contained
in the Frattini subgroup is precisely the kernel condition required above. -/
theorem map_frattini_quotient_eq_frattini
    {G : Type*} [Group G] (C : Subgroup G) [C.Normal]
    (hC : C ≤ frattini G) :
    (frattini G).map (QuotientGroup.mk' C) = frattini (G ⧸ C) := by
  apply map_frattini_eq_frattini_of_surjective_of_ker_le
      (QuotientGroup.mk'_surjective C)
  rwa [QuotientGroup.ker_mk']

/-- Pullback form of the Frattini quotient formula. -/
theorem comap_frattini_quotient_eq_frattini
    {G : Type*} [Group G] (C : Subgroup G) [C.Normal]
    (hC : C ≤ frattini G) :
    (frattini (G ⧸ C)).comap (QuotientGroup.mk' C) = frattini G := by
  apply comap_frattini_eq_frattini_of_surjective_of_ker_le
      (QuotientGroup.mk'_surjective C)
  rwa [QuotientGroup.ker_mk']
