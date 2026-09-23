module

public import LisiSabatini.LinearAction
public import Mathlib.LinearAlgebra.Pi

/-!
# Assembly of translated regularity from constituent stabilizers

A vector regular for the whole representation need not have regular
projections onto its irreducible constituents. The correct local condition
is containment in the stabilizer of each projected global reference
vector. These containments assemble because the coordinate map is injective
and equivariant.

The final criterion separates pure-component constituents, where the
corresponding reference projection is retained literally, from mixed
constituents, where a distinguished component retains a stabilizer bound
and the other components attain their action kernels. The structural
mixed-constituent theorem remains an explicit hypothesis.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uJ uG uR uV uW

/-- Local stabilizer containments imply a global stabilizer containment
under an injective equivariant coordinate map. Neither semisimplicity nor
finiteness is needed for this assembly step. -/
theorem actionPointStabilizer_le_of_coordinate_stabilizer_le
    {G : Type uG} [Group G]
    {R : Type uR} [Semiring R]
    {V : Type uV} [AddCommMonoid V] [Module R V]
    {J : Type uJ} {W : J → Type uW}
    [∀ j, AddCommMonoid (W j)] [∀ j, Module R (W j)]
    (ρ : G →* LinearMap.GeneralLinearGroup R V)
    (ρlocal : ∀ j, G →* LinearMap.GeneralLinearGroup R (W j))
    (e : V → (∀ j, W j)) (hinj : Function.Injective e)
    (hequiv : ∀ g x j, e (ρ g • x) j = ρlocal j g • e x j)
    (x a : V)
    (hlocal : ∀ j,
      actionPointStabilizer (ρlocal j) (e x j) ≤
        actionPointStabilizer (ρlocal j) (e a j)) :
    actionPointStabilizer ρ x ≤ actionPointStabilizer ρ a := by
  intro g hg
  change ρ g • a = a
  apply hinj
  funext j
  rw [hequiv]
  have hgj : g ∈ actionPointStabilizer (ρlocal j) (e x j) := by
    change ρlocal j g • e x j = e x j
    rw [← hequiv]
    exact congrArg (fun v ↦ e v j) hg
  exact hlocal j hgj

/-- Given a global regular reference vector for every row, coordinatewise
containment in the projected reference stabilizers produces one common
regular translate. No projected reference vector is assumed regular. -/
theorem exists_common_regular_translates_of_coordinate_stabilizer_containment
    {I : Type uI} {G : I → Type uG} [∀ i, Group (G i)]
    {R : Type uR} [Semiring R]
    {V : Type uV} [AddCommGroup V] [Module R V]
    {J : Type uJ} {W : J → Type uW}
    [∀ j, AddCommGroup (W j)] [∀ j, Module R (W j)]
    (ρ : ∀ i, G i →* LinearMap.GeneralLinearGroup R V)
    (ρlocal : ∀ i j, G i →* LinearMap.GeneralLinearGroup R (W j))
    (e : V ≃ₗ[R] (∀ j, W j))
    (hequiv : ∀ i g x j, e (ρ i g • x) j = ρlocal i j g • e x j)
    (a t : I → V)
    (hregular : ∀ i, actionPointStabilizer (ρ i) (a i) = ⊥)
    (hlocal : ∀ j, ∃ w : W j, ∀ i,
      actionPointStabilizer (ρlocal i j) (w + e (t i) j) ≤
        actionPointStabilizer (ρlocal i j) (e (a i) j)) :
    ∃ v : V, ∀ i, actionPointStabilizer (ρ i) (v + t i) = ⊥ := by
  choose w hw using hlocal
  refine ⟨e.symm w, fun i ↦ ?_⟩
  apply le_antisymm
  · rw [← hregular i]
    apply actionPointStabilizer_le_of_coordinate_stabilizer_le
      (ρ i) (ρlocal i) e e.injective (hequiv i)
    intro j
    simpa only [map_add, LinearEquiv.apply_symm_apply, Pi.add_apply] using hw j i
  · exact bot_le

/-- A pure-component constituent preserves the appropriate projected
reference vector. The remaining rows are trivial on that constituent and
therefore impose no extra condition. -/
theorem exists_local_stabilizer_containment_of_pure_component
    {I : Type uI} {G : I → Type uG} [∀ i, Group (G i)]
    {R : Type uR} [Semiring R]
    {W : Type uW} [AddCommGroup W] [Module R W]
    (ρ : ∀ i, G i →* LinearMap.GeneralLinearGroup R W)
    (a t : I → W) (owner : I)
    (hpure : ∀ i, i ≠ owner → ρ i = 1) :
    ∃ w : W, ∀ i,
      actionPointStabilizer (ρ i) (w + t i) ≤
        actionPointStabilizer (ρ i) (a i) := by
  refine ⟨a owner - t owner, fun i ↦ ?_⟩
  by_cases hi : i = owner
  · subst i
    rw [sub_add_cancel]
  · intro g _hg
    change ρ i g • a i = a i
    rw [hpure i hi]
    exact one_smul _ _

/-- Mixed constituents need literal containment only for a distinguished
row; attaining the action kernel is sufficient for all other rows.
`special = none` allows no distinguished row. -/
theorem local_stabilizer_containment_of_kernel_rows
    {I : Type uI} {G : I → Type uG} [∀ i, Group (G i)]
    {R : Type uR} [Semiring R]
    {W : Type uW} [AddCommGroup W] [Module R W]
    (ρ : ∀ i, G i →* LinearMap.GeneralLinearGroup R W)
    (a t : I → W) (special : Option I) (w : W)
    (hspecial : ∀ i, special = some i →
      actionPointStabilizer (ρ i) (w + t i) ≤
        actionPointStabilizer (ρ i) (a i))
    (hkernel : ∀ i, special ≠ some i →
      actionPointStabilizer (ρ i) (w + t i) = (ρ i).ker) :
    ∀ i, actionPointStabilizer (ρ i) (w + t i) ≤
      actionPointStabilizer (ρ i) (a i) := by
  intro i
  by_cases hi : special = some i
  · exact hspecial i hi
  · rw [hkernel i hi]
    exact action_ker_le_pointStabilizer (ρ i) (a i)

/-- Correct reducible assembly for the nilpotent translated-regularity
argument. Pure constituents retain their owner's projected global
reference vector. Mixed constituents require kernel regularity away from
the optional distinguished row and containment for that row.

In the application rows are prime-labelled, `special` selects the row
labelled by 2, and `owner j` records a constituent supported at a single
prime. The hypothesis
`hmixed` is the unresolved structural irreducible input; this theorem
does not assert that it holds for every nilpotent representation. -/
theorem exists_common_regular_translates_of_pure_and_mixed_constituents
    {I : Type uI} {G : I → Type uG} [∀ i, Group (G i)]
    {R : Type uR} [Semiring R]
    {V : Type uV} [AddCommGroup V] [Module R V]
    {J : Type uJ} {W : J → Type uW}
    [∀ j, AddCommGroup (W j)] [∀ j, Module R (W j)]
    (ρ : ∀ i, G i →* LinearMap.GeneralLinearGroup R V)
    (ρlocal : ∀ i j, G i →* LinearMap.GeneralLinearGroup R (W j))
    (e : V ≃ₗ[R] (∀ j, W j))
    (hequiv : ∀ i g x j, e (ρ i g • x) j = ρlocal i j g • e x j)
    (a t : I → V)
    (hregular : ∀ i, actionPointStabilizer (ρ i) (a i) = ⊥)
    (owner : J → Option I) (special : Option I)
    (hpure : ∀ j i, owner j = some i → ∀ k, k ≠ i → ρlocal k j = 1)
    (hmixed : ∀ j, owner j = none → ∃ w : W j,
      (∀ i, special = some i →
        actionPointStabilizer (ρlocal i j) (w + e (t i) j) ≤
          actionPointStabilizer (ρlocal i j) (e (a i) j)) ∧
      (∀ i, special ≠ some i →
        actionPointStabilizer (ρlocal i j) (w + e (t i) j) =
          (ρlocal i j).ker)) :
    ∃ v : V, ∀ i, actionPointStabilizer (ρ i) (v + t i) = ⊥ := by
  apply exists_common_regular_translates_of_coordinate_stabilizer_containment
    ρ ρlocal e hequiv a t hregular
  intro j
  cases howner : owner j with
  | none =>
      obtain ⟨w, hspecial, hkernel⟩ := hmixed j howner
      exact ⟨w, local_stabilizer_containment_of_kernel_rows
        (fun i ↦ ρlocal i j) (fun i ↦ e (a i) j) (fun i ↦ e (t i) j)
        special w hspecial hkernel⟩
  | some i =>
      exact exists_local_stabilizer_containment_of_pure_component
        (fun k ↦ ρlocal k j) (fun k ↦ e (a k) j) (fun k ↦ e (t k) j)
        i (hpure j i howner)

end LisiSabatini
