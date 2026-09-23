module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Product rows on disjoint permutation blocks

Two permutation subgroups on consecutive blocks embed as their direct product.
This supplies exact cardinalities and row enumeration from the smaller factors,
without checking the multiplication table of the full product subgroup.
-/

@[expose] public section

namespace LisiSabatini

universe uI uJ

/-- Combine permutations of two consecutive finite blocks. -/
def finBlockSumPermHom (a b : ℕ) :
    Equiv.Perm (Fin a) × Equiv.Perm (Fin b) →* Equiv.Perm (Fin (a + b)) :=
  (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).permCongrHom.toMonoidHom.comp
    (Equiv.Perm.sumCongrHom (Fin a) (Fin b))

/-- The two block permutations can be recovered from their combined action. -/
theorem finBlockSumPermHom_injective (a b : ℕ) :
    Function.Injective (finBlockSumPermHom a b) :=
  (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a + b)).permCongrHom.injective.comp
    Equiv.Perm.sumCongrHom_injective

@[simp]
theorem finBlockSumPermHom_apply_left {a b : ℕ}
    (h : Equiv.Perm (Fin a)) (k : Equiv.Perm (Fin b)) (i : Fin a) :
    finBlockSumPermHom a b (h, k) (Fin.castAdd b i) = Fin.castAdd b (h i) := by
  simp [finBlockSumPermHom, Equiv.permCongrHom_coe, Equiv.permCongr_apply]

@[simp]
theorem finBlockSumPermHom_apply_right {a b : ℕ}
    (h : Equiv.Perm (Fin a)) (k : Equiv.Perm (Fin b)) (i : Fin b) :
    finBlockSumPermHom a b (h, k) (Fin.natAdd a i) = Fin.natAdd a (k i) := by
  simp [finBlockSumPermHom, Equiv.permCongrHom_coe, Equiv.permCongr_apply]

/-- The product of two subgroup rows acts independently on the two blocks. -/
def finBlockProductHom {a b : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b))) :
    H × K →* Equiv.Perm (Fin (a + b)) :=
  (finBlockSumPermHom a b).comp (H.subtype.prodMap K.subtype)

/-- The block-product embedding is faithful. -/
theorem finBlockProductHom_injective {a b : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b))) :
    Function.Injective (finBlockProductHom H K) := by
  intro s t hst
  have h := finBlockSumPermHom_injective a b hst
  exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

/-- The permutation subgroup obtained from independent actions on two blocks. -/
def finBlockProductSubgroup {a b : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b))) :
    Subgroup (Equiv.Perm (Fin (a + b))) :=
  (finBlockProductHom H K).range

/-- Every element of the block-product subgroup is a product row. -/
theorem mem_finBlockProductSubgroup_iff {a b : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b)))
    (σ : Equiv.Perm (Fin (a + b))) :
    σ ∈ finBlockProductSubgroup H K ↔
      ∃ h : H, ∃ k : K, finBlockSumPermHom a b ((h : Equiv.Perm (Fin a)),
        (k : Equiv.Perm (Fin b))) = σ := by
  change (∃ t : H × K, finBlockProductHom H K t = σ) ↔ _
  constructor
  · rintro ⟨⟨h, k⟩, hrow⟩
    exact ⟨h, k, hrow⟩
  · rintro ⟨h, k, hrow⟩
    exact ⟨(h, k), hrow⟩

/-- Exact product cardinality, obtained by a group isomorphism. -/
theorem natCard_finBlockProductSubgroup {a b : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b))) :
    Nat.card (finBlockProductSubgroup H K) = Nat.card H * Nat.card K := by
  calc
    Nat.card (finBlockProductSubgroup H K) = Nat.card (H × K) :=
      (Nat.card_congr (MonoidHom.ofInjective (finBlockProductHom_injective H K)).toEquiv).symm
    _ = _ := Nat.card_prod _ _

/-- A product of two finite `p`-subgroup rows is again a `p`-subgroup. -/
theorem isPGroup_finBlockProductSubgroup {a b p : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b)))
    (hH : IsPGroup p H) (hK : IsPGroup p K) :
    IsPGroup p (finBlockProductSubgroup H K) := by
  obtain ⟨r, hr⟩ := hH.exists_card_dvd_pow
  obtain ⟨s, hs⟩ := hK.exists_card_dvd_pow
  apply IsPGroup.of_card_dvd_pow (n := r + s)
  rw [natCard_finBlockProductSubgroup, pow_add]
  exact Nat.mul_dvd_mul hr hs

/-- Surjective indexed rows of the factors enumerate every product row. -/
theorem mem_finBlockProductSubgroup_iff_indexed {a b : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b)))
    {I : Type uI} {J : Type uJ} (h : I → H) (k : J → K)
    (hh : Function.Surjective h) (hk : Function.Surjective k)
    (σ : Equiv.Perm (Fin (a + b))) :
    σ ∈ finBlockProductSubgroup H K ↔ ∃ i j,
      finBlockSumPermHom a b ((h i : Equiv.Perm (Fin a)), (k j : Equiv.Perm (Fin b))) = σ := by
  rw [mem_finBlockProductSubgroup_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    obtain ⟨i, rfl⟩ := hh x
    obtain ⟨j, rfl⟩ := hk y
    exact ⟨i, j, hxy⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨h i, k j, hij⟩

/-- Membership descriptions by ordinary permutation rows combine without
constructing or checking a multiplication table for the product. -/
theorem mem_finBlockProductSubgroup_iff_rows {a b : ℕ}
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b)))
    {I : Type uI} {J : Type uJ}
    (h : I → Equiv.Perm (Fin a)) (k : J → Equiv.Perm (Fin b))
    (hh : ∀ x, x ∈ H ↔ ∃ i, h i = x) (hk : ∀ y, y ∈ K ↔ ∃ j, k j = y)
    (σ : Equiv.Perm (Fin (a + b))) :
    σ ∈ finBlockProductSubgroup H K ↔ ∃ i j, finBlockSumPermHom a b (h i, k j) = σ := by
  rw [mem_finBlockProductSubgroup_iff]
  constructor
  · rintro ⟨x, y, hxy⟩
    obtain ⟨i, hi⟩ := (hh x).mp x.property
    obtain ⟨j, hj⟩ := (hk y).mp y.property
    exact ⟨i, j, by simpa only [hi, hj] using hxy⟩
  · rintro ⟨i, j, hij⟩
    exact ⟨⟨h i, (hh (h i)).mpr ⟨i, rfl⟩⟩,
      ⟨k j, (hk (k j)).mpr ⟨j, rfl⟩⟩, hij⟩

/-- A block product whose order is the full `p`-part of `(a+b)!` is Sylow. -/
def finBlockProductSylow {a b : ℕ} (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b)))
    (hcard : Nat.card H * Nat.card K = p ^ (Nat.factorial (a + b)).factorization p) :
    Sylow p (Equiv.Perm (Fin (a + b))) :=
  Sylow.ofCard (finBlockProductSubgroup H K) (by
    rw [natCard_finBlockProductSubgroup, hcard]
    congr 2
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin])

@[simp]
theorem coe_finBlockProductSylow {a b : ℕ} (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Equiv.Perm (Fin a))) (K : Subgroup (Equiv.Perm (Fin b)))
    (hcard : Nat.card H * Nat.card K = p ^ (Nat.factorial (a + b)).factorization p) :
    (finBlockProductSylow p H K hcard : Subgroup (Equiv.Perm (Fin (a + b)))) =
      finBlockProductSubgroup H K := rfl

/-- The full two-part of the degree-nine symmetric group order. -/
theorem finBlockProductTwoPartNine : 2 ^ (Nat.factorial 9).factorization 2 = 128 := by
  decide +kernel

/-- The full two-part of the degree-ten symmetric group order. -/
theorem finBlockProductTwoPartTen : 2 ^ (Nat.factorial 10).factorization 2 = 256 := by
  decide +kernel

/-- The full two-part of the degree-twelve symmetric group order. -/
theorem finBlockProductTwoPartTwelve : 2 ^ (Nat.factorial 12).factorization 2 = 1024 := by
  decide +kernel

/-- An order-128 subgroup on eight points, extended by one fixed point,
is a Sylow two-subgroup on nine points. -/
def finBlockProductSylowNine (H : Subgroup (Equiv.Perm (Fin 8)))
    (hH : Nat.card H = 128) : Sylow 2 (Equiv.Perm (Fin 9)) :=
  finBlockProductSylow 2 H (⊥ : Subgroup (Equiv.Perm (Fin 1))) (by
    simp [hH, finBlockProductTwoPartNine])

/-- An order-128 row on eight points and an order-two row on two points
supply a Sylow two-subgroup on ten points. -/
def finBlockProductSylowTen (H : Subgroup (Equiv.Perm (Fin 8)))
    (K : Subgroup (Equiv.Perm (Fin 2))) (hH : Nat.card H = 128) (hK : Nat.card K = 2) :
    Sylow 2 (Equiv.Perm (Fin 10)) :=
  finBlockProductSylow 2 H K (by
    rw [hH, hK, show 8 + 2 = 10 from rfl, finBlockProductTwoPartTen])

/-- An order-128 row on eight points and an order-eight row on four points
supply a Sylow two-subgroup on twelve points. -/
def finBlockProductSylowTwelve (H : Subgroup (Equiv.Perm (Fin 8)))
    (K : Subgroup (Equiv.Perm (Fin 4))) (hH : Nat.card H = 128) (hK : Nat.card K = 8) :
    Sylow 2 (Equiv.Perm (Fin 12)) :=
  finBlockProductSylow 2 H K (by
    rw [hH, hK, show 8 + 4 = 12 from rfl, finBlockProductTwoPartTwelve])

@[simp]
theorem coe_finBlockProductSylowNine (H : Subgroup (Equiv.Perm (Fin 8)))
    (hH : Nat.card H = 128) :
    (finBlockProductSylowNine H hH : Subgroup (Equiv.Perm (Fin 9))) =
      finBlockProductSubgroup H (⊥ : Subgroup (Equiv.Perm (Fin 1))) := rfl

@[simp]
theorem coe_finBlockProductSylowTen (H : Subgroup (Equiv.Perm (Fin 8)))
    (K : Subgroup (Equiv.Perm (Fin 2))) (hH : Nat.card H = 128) (hK : Nat.card K = 2) :
    (finBlockProductSylowTen H K hH hK : Subgroup (Equiv.Perm (Fin 10))) =
      finBlockProductSubgroup H K := rfl

@[simp]
theorem coe_finBlockProductSylowTwelve (H : Subgroup (Equiv.Perm (Fin 8)))
    (K : Subgroup (Equiv.Perm (Fin 4))) (hH : Nat.card H = 128) (hK : Nat.card K = 8) :
    (finBlockProductSylowTwelve H K hH hK : Subgroup (Equiv.Perm (Fin 12))) =
      finBlockProductSubgroup H K := rfl

/-- The degree-nine product row has exactly 128 elements. -/
theorem natCard_finBlockProductSylowNine (H : Subgroup (Equiv.Perm (Fin 8)))
    (hH : Nat.card H = 128) : Nat.card (finBlockProductSylowNine H hH) = 128 := by
  change Nat.card (finBlockProductSubgroup H (⊥ : Subgroup (Equiv.Perm (Fin 1)))) = 128
  rw [natCard_finBlockProductSubgroup, hH]
  simp

/-- The degree-ten product row has exactly 256 elements. -/
theorem natCard_finBlockProductSylowTen (H : Subgroup (Equiv.Perm (Fin 8)))
    (K : Subgroup (Equiv.Perm (Fin 2))) (hH : Nat.card H = 128) (hK : Nat.card K = 2) :
    Nat.card (finBlockProductSylowTen H K hH hK) = 256 := by
  change Nat.card (finBlockProductSubgroup H K) = 256
  rw [natCard_finBlockProductSubgroup, hH, hK]

/-- The degree-twelve product row has exactly 1024 elements. -/
theorem natCard_finBlockProductSylowTwelve (H : Subgroup (Equiv.Perm (Fin 8)))
    (K : Subgroup (Equiv.Perm (Fin 4))) (hH : Nat.card H = 128) (hK : Nat.card K = 8) :
    Nat.card (finBlockProductSylowTwelve H K hH hK) = 1024 := by
  change Nat.card (finBlockProductSubgroup H K) = 1024
  rw [natCard_finBlockProductSubgroup, hH, hK]

end LisiSabatini
