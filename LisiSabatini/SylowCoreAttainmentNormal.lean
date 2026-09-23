module

public import LisiSabatini.SylowCoreAttainment

/-!
# Property (*) in normal subgroups

The one-prime condition passes to normal subgroups, as in Lemma 2.1 of
the paper. An ambient witness conjugates a Sylow subgroup of the normal
subgroup through the restricted conjugation automorphism. The resulting
intersection lies in the restricted ambient core and therefore in the
normal subgroup's core.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe u

variable {G : Type u} [Group G]

/-- Restriction of the ambient prime core lies in the subgroup's prime
core. Normality of the subgroup is unnecessary for this inclusion. -/
theorem pCore_comap_subtype_le (p : ℕ) (H : Subgroup G) :
    (pCore p G).comap H.subtype ≤ pCore p H :=
  le_pCore ((pCore_isPGroup p G).comap_subtype) inferInstance

/-- The prime core of a normal subgroup is the intersection with the
ambient prime core, expressed through the subgroup inclusion. -/
theorem pCore_eq_comap_of_normal (p : ℕ) (N : Subgroup G) [N.Normal] :
    pCore p N = (pCore p G).comap N.subtype := by
  apply le_antisymm
  · rw [← Subgroup.map_le_iff_le_comap]
    exact le_pCore ((pCore_isPGroup p N).map N.subtype)
      ConjAct.normal_of_characteristic_of_normal
  · exact pCore_comap_subtype_le p N

/-- Lemma 2.1: the one-prime form of (*) passes to normal subgroups. -/
theorem SylowCoreAttainmentAt.of_normal_subgroup {p : ℕ}
    [Fact p.Prime] [Finite G] (hG : SylowCoreAttainmentAt p G)
    (N : Subgroup G) [N.Normal] : SylowCoreAttainmentAt p N := by
  classical
  apply sylowCoreAttainmentAt_iff_exists_pair.mpr
  let P : Sylow p N := Classical.choice inferInstance
  obtain ⟨U, hU⟩ := P.exists_comap_subtype_eq
  obtain ⟨x, hx⟩ := hG U
  let Q : Sylow p N := (MulAut.conjNormal x : MulAut N) • P
  refine ⟨P, Q, le_antisymm ?_ (le_inf (pCore_le_sylow P) (pCore_le_sylow Q))⟩
  intro n hn
  apply pCore_comap_subtype_le p N
  change (n : G) ∈ pCore p G
  rw [← hx]
  refine ⟨?_, ?_⟩
  · exact show n ∈ (U : Subgroup G).comap N.subtype from hU.symm ▸ hn.1
  · have hQ := hn.2
    change n ∈ (P : Subgroup N).map (MulAut.conjNormal x).toMonoidHom at hQ
    rcases hQ with ⟨a, ha, han⟩
    change (n : G) ∈ (U : Subgroup G).map (MulAut.conj x).toMonoidHom
    refine ⟨a, show a ∈ (U : Subgroup G).comap N.subtype from hU.symm ▸ ha, ?_⟩
    exact congrArg Subtype.val han

/-- Property (*) passes to every normal subgroup of a finite group. -/
theorem SylowCoreAttainment.of_normal_subgroup [Finite G]
    (hG : SylowCoreAttainment G) (N : Subgroup G) [N.Normal] :
    SylowCoreAttainment N := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  exact (hG p hp).of_normal_subgroup N

end LisiSabatini
