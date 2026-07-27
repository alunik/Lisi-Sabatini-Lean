# Three synchronized Sylow intersections in finite solvable groups

This Lean 4/mathlib project proves the three-conjugates conjecture for every
finite solvable group.  The formal result is stronger: the three Sylow
subgroups at each prime may be prescribed independently.

The public endpoint is
[`LisiSabatini/SolvableThreeSylowSynchronization.lean`](LisiSabatini/SolvableThreeSylowSynchronization.lean).
Its main theorem is:

```lean
theorem mixedThreeSylowCoreSynchronization_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G
```

After expanding the definition, this says that for every finite index type
`I`, every injective family of primes `p : I → ℕ`, and every three prescribed
families

```lean
P Q R : ∀ i, Sylow (p i) G
```

there are common elements `x y : G` such that, simultaneously for every
`i`,

```lean
mixedSylowTripleInter (P i) (Q i) (R i) x y =
  pCore (p i) G
```

Here

```text
mixedSylowTripleInter P Q R x y = P ∩ xQx⁻¹ ∩ yRy⁻¹.
```

Taking `P = Q = R` gives the same-row three-conjugates theorem:

```lean
theorem threeConjugatesSylowSynchronization_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    HasThreeConjugatesSylowSynchronization.{uG, uI} G
```

## Further formalized consequences

The repository also contains:

- the mixed two-row theorem for finite solvable groups of odd order;
- the original strong Lisi–Sabatini theorem for finite solvable groups of
  odd order;
- the mixed three-row theorem for solvable groups whose Sylow
  `2`-subgroups are commutative;
- the Fitting-subgroup consequence for three independently prescribed
  nilpotent subgroups:

```lean
theorem threeNilpotentIntersectionInFitting_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    ThreeNilpotentIntersectionInFitting G
```

The last statement says that for nilpotent subgroups `H`, `K`, and `M`,
there are `x y : G` with

```text
H ∩ xKx⁻¹ ∩ yMy⁻¹ ≤ F(G).
```

## Proof organization

The proof has four layers.

1. `ThreeConjugatesSynchronization.lean` defines the mixed two-row,
   mixed three-row, and same-row properties.
2. `ThreeSylowSolvableReduction.lean` reduces the solvable theorem, by
   induction through an elementary-abelian chief factor, to a simultaneous
   affine two-base statement.
3. The affine files prove the required estimates for the characteristic
   and odd-prime branches and reduce the remaining noncommuting `2`-core
   branch to a precise two-group classification.
4. `HallBergerClassificationAssembly.lean` completes that classification
   and `SolvableThreeSylowSynchronization.lean` substitutes it into the
   solvable reduction.

`NilpotentIntersectionCorollaries.lean` contains only the general
Sylow-to-Fitting implications.  Concrete odd-order and commutative-Sylow-`2`
applications are separated into `NilpotentIntersectionApplications.lean`.

## Verification

The project is pinned to Lean and mathlib `v4.29.1`.

```text
lake exe cache get
lake build
```

The publication endpoint can be checked independently with warnings treated
as errors:

```text
lake env lean -DwarningAsError=true \
  LisiSabatini/SolvableThreeSylowSynchronization.lean
```

The focused axiom audit is:

```text
lake env lean -DwarningAsError=true \
  LisiSabatini/SolvableThreeSylowSynchronizationAxiomAudit.lean
```

Every public result listed above depends only on Lean's standard logical
axioms: `propext`, `Classical.choice`, and `Quot.sound`.

## Scope

Solvability is an explicit hypothesis.  This branch contains no
almost-simple or CFSG-family development, no GAP census, and no external
classification assumption.  Proposition-valued intermediate interfaces are
inhabited by Lean proofs before they are used by the public endpoint.

The repository contains the source dependency closure of the proved
solvable and odd-order results, plus the two focused axiom-audit modules.
