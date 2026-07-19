# Lisi–Sabatini for soluble groups of odd order

This Lean 4/mathlib project formalises the Lisi–Sabatini conjecture for
finite **soluble groups of odd order**.  It proves the stronger synchronized
statement: for any finite family of prescribed Sylow subgroups at distinct
primes, a single conjugating element makes every intersection equal to the
corresponding normal prime core.

The public proof endpoint is
[`LisiSabatini/OddOrderProof.lean`](LisiSabatini/OddOrderProof.lean).  Its main
theorem is:

```lean
theorem strongLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    StrongLisiSabatini.{uG, uI} G
```

Here `StrongLisiSabatini G` says that, for every finite index type `I`, every
injective family of primes `p : I → ℕ`, and every prescribed family
`P : ∀ i, Sylow (p i) G`, there is one `x : G` such that

```lean
sylowInter (P i) x = pCore (p i) G
```

for every `i`.  Mathlib's conjugation action used by `sylowInter` is
`x P x⁻¹`.  Since `pCore (p i) G` lies in every such intersection, this
immediately implies the original inclusion-minimal conclusion:

```lean
theorem hasLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    HasLisiSabatini.{uG, uI} G
```

## Scope

Solubility is an explicit hypothesis.  The mathematical Feit–Thompson
theorem would remove it for groups of odd order, but Feit–Thompson has not
been imported or postulated in this development.

This repository is deliberately restricted to the transitive source
dependency closure of `OddOrderProof.lean`.  It excludes earlier bounded-rank
approaches, compatibility wrappers, experimental files, audits, and the
paper write-up.

## Proof structure

The formal proof has two main inductions.

1. `PrimewiseAffineRegularityCore.lean` proves a marked simultaneous affine
   regularity theorem for normal prime-power subgroups of an irreducible
   linear group in odd characteristic.  Quasiprimitive actions are controlled
   by a mixed fixed-space budget; imprimitive actions are handled recursively
   using a binary list-colouring argument over the unique possible active
   primitive top.
2. `OddOrderProof.lean` inducts on `Nat.card G`.  A minimal normal subgroup is
   realised as an elementary abelian chief factor, the affine theorem is
   applied to its faithful irreducible conjugation action, and the quotient
   witness is lifted to `G`.

## Building

The project is pinned to Lean and mathlib `v4.29.1`.

```text
lake exe cache get
lake build
```

To compile only the publication endpoint with warnings treated as errors:

```text
lake env lean -DwarningAsError=true LisiSabatini/OddOrderProof.lean
```

## Repository layout

- `LisiSabatini.lean` — minimal library entrypoint.
- `LisiSabatini/OddOrderProof.lean` — group-theoretic induction and public
  theorems.
- `LisiSabatini/PrimewiseAffineRegularityCore.lean` — linear induction.
- `LisiSabatini/OddOrderChiefFactorCore.lean` — minimal-normal chief-factor
  construction.
- `LisiSabatini/NormalComponentReductionCore.lean` — exact affine lifting
  interface.

All other Lean files in the repository occur in the import closure of these
modules.
