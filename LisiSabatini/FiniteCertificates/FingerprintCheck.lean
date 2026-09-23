module

public import LisiSabatini.FiniteCertificates.TableCertificate
public import LisiSabatini.FiniteCertificates.PermutationTable

/-!
# Conservative fingerprint certificates

A finite bit mask may contain false positives. Its only required property is
that every subgroup element has a set bit. Consequently, a clear bit proves
nonmembership, and false positives can only increase the certified bad bound.
All computations use the kernel's natural-number arithmetic.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates

variable {G : Type*} [Group G] [DecidableEq G]

/-- Check that every nonidentity probe has a clear bit after conjugation. -/
def fingerprintGoodCheck (fingerprint : G → ℕ) (mask : ℕ)
    (probes : List G) (x : G) : Bool :=
  probes.all (fun y ↦ !(mask.testBit (fingerprint (x⁻¹ * y * x))))

/-- Soundness needs only one-sided coverage by the fingerprint mask. -/
theorem fingerprintGoodCheck_sound
    (s : Finset G) (fingerprint : G → ℕ) (mask : ℕ) (probes : List G)
    (hcover : ∀ y ∈ s, y ≠ 1 → y ∈ probes)
    (hmask : ∀ y ∈ s, mask.testBit (fingerprint y) = true)
    (x : G) (hx : fingerprintGoodCheck fingerprint mask probes x = true) :
    goodCheck s x = true := by
  apply decide_eq_true
  intro y hy
  by_cases hone : y = 1
  · exact Or.inl hone
  · right
    intro hmem
    have hbit := List.all_eq_true.mp hx y (hcover y hy hone)
    have htrue := hmask _ hmem
    simp only [htrue, Bool.not_true, Bool.false_eq_true] at hbit

omit [DecidableEq G] in
/-- A row written with the identity first supplies all necessary probes. -/
theorem tail_covers_nonidentity (probes : List G)
    (h : (1 :: probes).Nodup) :
    ∀ y ∈ finsetOfNodupList (1 :: probes) h, y ≠ 1 → y ∈ probes := by
  intro y hy hone
  exact (List.mem_cons.mp hy).resolve_left hone

attribute [local instance] Classical.propDecidable

/-- Every actual bad conjugator is rejected by a sound fingerprint check. -/
theorem bad_card_le_fingerprint_rejected_card
    [Finite G] {p : ℕ} [Fact p.Prime]
    (s : Finset G) (hs : subgroupCheck s = true)
    (hcard : s.card = p ^ (Nat.card G).factorization p)
    (fingerprint : G → ℕ) (mask : ℕ) (probes : List G)
    (hcover : ∀ y ∈ s, y ≠ 1 → y ∈ probes)
    (hmask : ∀ y ∈ s, mask.testBit (fingerprint y) = true)
    (C : Finset G) :
    (C.filter fun x ↦ sylowInter (checkedSylow s hs hcard) x ≠ ⊥).card ≤
      (C.filter fun x ↦ fingerprintGoodCheck fingerprint mask probes x = false).card := by
  classical
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxC, hxBad⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hxC, ?_⟩
  cases h : fingerprintGoodCheck fingerprint mask probes x
  · rfl
  · exact (hxBad (checkedSylow_good s hs hcard x
      (fingerprintGoodCheck_sound s fingerprint mask probes hcover hmask x h))).elim

/-- Filtering a directly constructed finite carrier can be counted on its list. -/
theorem filter_card_finsetOfNodupList {α : Type*}
    (l : List α) (hl : l.Nodup) (f : α → Bool) :
    ((finsetOfNodupList l hl).filter (fun x ↦ f x = true)).card = l.countP f := by
  have hfin : finsetOfNodupList l hl = l.toFinset := by
    ext x
    simp
  rw [hfin, hl.card_eq_countP]
  simp

/-- List-count form of the conservative bad-conjugator bound. -/
theorem bad_card_le_fingerprint_rejected_count
    [Finite G] {p : ℕ} [Fact p.Prime]
    (s : Finset G) (hs : subgroupCheck s = true)
    (hcard : s.card = p ^ (Nat.card G).factorization p)
    (fingerprint : G → ℕ) (mask : ℕ) (probes : List G)
    (hcover : ∀ y ∈ s, y ≠ 1 → y ∈ probes)
    (hmask : ∀ y ∈ s, mask.testBit (fingerprint y) = true)
    (l : List G) (hl : l.Nodup) :
    ((finsetOfNodupList l hl).filter fun x ↦
      sylowInter (checkedSylow s hs hcard) x ≠ ⊥).card ≤
      l.countP (fun x ↦ !(fingerprintGoodCheck fingerprint mask probes x)) := by
  apply (bad_card_le_fingerprint_rejected_card s hs hcard fingerprint mask probes
    hcover hmask (finsetOfNodupList l hl)).trans_eq
  simpa using filter_card_finsetOfNodupList l hl
    (fun x ↦ !(fingerprintGoodCheck fingerprint mask probes x))

end LisiSabatini.FiniteCertificates
