module

public import LisiSabatini.Strong
public import LisiSabatini.Quotient

/-!
# Individual Sylow core attainment and its quotient-closed form

`SylowCoreAttainmentAt p G` is the one-prime condition that every prescribed
Sylow `p`-subgroup has a conjugate meeting it in `O_p(G)`.
`SylowCoreAttainment G` is property (*) in the paper.  The equivalent
existential-pair formulation is proved below; no simultaneous choice of
conjugators is built into this definition.

`QuotientSylowCoreAttainment G` says that every quotient has property (*).
It is expressed using surjective homomorphisms so that its inheritance by a
quotient is simply composition.  The equivalence with quantification over
normal subgroups is explicit, and the identity quotient includes `G` itself.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

open scoped Pointwise

universe u v uI

/-- The one-prime form of property (*), for a prescribed Sylow subgroup. -/
def SylowCoreAttainmentAt (p : ℕ) (G : Type u) [Group G] : Prop :=
  ∀ P : Sylow p G, ∃ x : G, sylowInter P x = pCore p G

/-- Property (*): individual core attainment at each prime. -/
def SylowCoreAttainment (G : Type u) [Group G] : Prop :=
  ∀ p : ℕ, Nat.Prime p → SylowCoreAttainmentAt p G

/-- Every quotient, including the identity quotient, has property (*). -/
def QuotientSylowCoreAttainment (G : Type u) [Group G] [Finite G] : Prop :=
  ∀ {H : Type u} [Group H] [Finite H] (f : G →* H),
    Function.Surjective f → SylowCoreAttainment H

variable {G : Type u} [Group G] {H : Type v} [Group H]

/-- Isomorphisms carry the prime core to the prime core. -/
theorem pCore_map_mulEquiv (p : ℕ) (e : G ≃* H) :
    (pCore p G).map e.toMonoidHom = pCore p H := by
  apply le_antisymm
  · exact le_pCore ((pCore_isPGroup p G).map e.toMonoidHom)
      (Subgroup.Normal.map (pCore_normal p G) e.toMonoidHom e.surjective)
  · have hback : (pCore p H).map e.symm.toMonoidHom ≤ pCore p G :=
      le_pCore ((pCore_isPGroup p H).map e.symm.toMonoidHom)
        (Subgroup.Normal.map (pCore_normal p H)
          e.symm.toMonoidHom e.symm.surjective)
    intro y hy
    exact ⟨e.symm y, hback ⟨y, hy, rfl⟩, e.apply_symm_apply y⟩

/-- Isomorphisms preserve intersections of subgroups. -/
theorem subgroup_map_inf_mulEquiv (e : G ≃* H) (A B : Subgroup G) :
    (A ⊓ B).map e.toMonoidHom =
      A.map e.toMonoidHom ⊓ B.map e.toMonoidHom := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, ⟨x, hx.2, rfl⟩⟩
  · rintro y ⟨⟨a, ha, hay⟩, ⟨b, hb, hby⟩⟩
    have hab : a = b := e.injective (hay.trans hby.symm)
    exact ⟨a, ⟨ha, hab.symm ▸ hb⟩, hay⟩

/-- Conjugating the prescribed Sylow subgroup transports a core witness. -/
theorem sylowInter_smul_conjugate {p : ℕ} (P : Sylow p G) (x g : G) :
    sylowInter (g • P) (g * x * g⁻¹) =
      (sylowInter P x).map (MulAut.conj g).toMonoidHom := by
  simp only [sylowInter, subgroup_map_inf_mulEquiv,
    Sylow.coe_subgroup_smul, map_conj_smul]
  rfl

/-- For finite groups the prescribed-Sylow formulation is exactly the
paper's existence of two Sylow subgroups whose intersection is the core. -/
theorem sylowCoreAttainmentAt_iff_exists_pair {p : ℕ}
    [Fact p.Prime] [Finite G] :
    SylowCoreAttainmentAt p G ↔
      ∃ P Q : Sylow p G,
        (P : Subgroup G) ⊓ (Q : Subgroup G) = pCore p G := by
  classical
  constructor
  · intro h
    let P : Sylow p G := Classical.choice inferInstance
    obtain ⟨x, hx⟩ := h P
    exact ⟨P, x • P, hx⟩
  · rintro ⟨P₀, Q₀, hPQ⟩ P
    obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G P₀ Q₀
    have hbase : sylowInter P₀ x = pCore p G := by
      simpa only [sylowInter, hx] using hPQ
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P₀ P
    refine ⟨g * x * g⁻¹, ?_⟩
    rw [← hg, sylowInter_smul_conjugate, hbase, pCore_map_mulEquiv]

/-- Property (*) is unchanged by a group isomorphism. -/
theorem SylowCoreAttainment.of_mulEquiv [Finite G] [Finite H]
    (hG : SylowCoreAttainment G) (e : G ≃* H) :
    SylowCoreAttainment H := by
  intro p hp
  let : Fact p.Prime := ⟨hp⟩
  apply sylowCoreAttainmentAt_iff_exists_pair.mpr
  obtain ⟨P, Q, hPQ⟩ :=
    sylowCoreAttainmentAt_iff_exists_pair.mp (hG p hp)
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective,
    Q.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup G).map e.toMonoidHom ⊓
      (Q : Subgroup G).map e.toMonoidHom = pCore p H
  rw [← subgroup_map_inf_mulEquiv, hPQ, pCore_map_mulEquiv]

theorem sylowCoreAttainment_iff_of_mulEquiv [Finite G] [Finite H]
    (e : G ≃* H) :
    SylowCoreAttainment G ↔ SylowCoreAttainment H :=
  ⟨fun h ↦ h.of_mulEquiv e, fun h ↦ h.of_mulEquiv e.symm⟩

/-- An inclusion-minimal intersection is the core whenever the core is
individually attained. -/
theorem SylowCoreAttainmentAt.eq_pCore_of_isMinimal {p : ℕ}
    (hG : SylowCoreAttainmentAt p G) (P : Sylow p G) (x : G)
    (hmin : IsMinimalSylowInter P x) :
    sylowInter P x = pCore p G := by
  obtain ⟨y, hy⟩ := hG P
  apply le_antisymm
  · have hle : sylowInter P y ≤ sylowInter P x := by
      rw [hy]
      exact pCore_le_sylowInter P x
    simpa only [hy] using hmin y hle
  · exact pCore_le_sylowInter P x

/-- Under (*), the original and strong conclusions agree. -/
theorem SylowCoreAttainment.strongLisiSabatini_iff [Finite G]
    (hG : SylowCoreAttainment G) :
    StrongLisiSabatini.{u, uI} G ↔ HasLisiSabatini.{u, uI} G := by
  constructor
  · exact StrongLisiSabatini.hasLisiSabatini
  · intro h I _ p hp hinj P
    obtain ⟨x, hx⟩ := h p hp hinj P
    exact ⟨x, fun i ↦ (hG (p i) (hp i)).eq_pCore_of_isMinimal
      (P i) x (hx i)⟩

namespace QuotientSylowCoreAttainment

variable [Finite G]

/-- The identity quotient shows that the hereditary condition includes (*). -/
theorem self (hG : QuotientSylowCoreAttainment G) :
    SylowCoreAttainment G :=
  hG (MonoidHom.id G) (fun x ↦ ⟨x, rfl⟩)

/-- The hereditary condition is preserved by surjective homomorphisms. -/
theorem of_surjective {Q : Type u} [Group Q] [Finite Q]
    (hG : QuotientSylowCoreAttainment G)
    (f : G →* Q) (hf : Function.Surjective f) :
    QuotientSylowCoreAttainment Q := by
  intro K _ _ g hg
  exact hG (g.comp f) (hg.comp hf)

/-- The condition supplies (*) for each normal quotient. -/
theorem quotient (hG : QuotientSylowCoreAttainment G)
    (N : Subgroup G) [N.Normal] :
    SylowCoreAttainment (G ⧸ N) :=
  hG (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

/-- Every quotient again satisfies the hereditary condition. -/
theorem quotient_closed (hG : QuotientSylowCoreAttainment G)
    (N : Subgroup G) [N.Normal] :
    QuotientSylowCoreAttainment (G ⧸ N) :=
  hG.of_surjective (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)

end QuotientSylowCoreAttainment

/-- Surjective-image quantification is exactly quantification over normal
quotients; it is not a stronger hypothesis than the one in the paper. -/
theorem quotientSylowCoreAttainment_iff_normal_quotients [Finite G] :
    QuotientSylowCoreAttainment G ↔
      ∀ (N : Subgroup G) [N.Normal], SylowCoreAttainment (G ⧸ N) := by
  constructor
  · intro h N _
    exact h.quotient N
  · intro h Q _ _ f hf
    exact (h f.ker).of_mulEquiv
      (QuotientGroup.quotientKerEquivOfSurjective f hf)

end LisiSabatini
