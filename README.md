# Formalized Sylow-intersection results

This Lean 4/mathlib project contains two related but distinct developments.
The first concerns the original Lisi–Sabatini conjecture. The second concerns
the mixed three-intersection problem and Huang's same-row specialization; it
should not be identified with the Lisi–Sabatini conjecture.

| Problem | Formalized range | Main endpoint |
| --- | --- | --- |
| Original Lisi–Sabatini property | finite solvable groups of odd order | `hasLisiSabatini_of_solvable_of_odd` |
| Original Lisi–Sabatini property | alternating groups `A_n`, `n ≥ 40` | `hasLisiSabatini_alternatingGroup_ge_forty` |
| Mixed three-intersection synchronization | all finite solvable groups | `mixedThreeSylowCoreSynchronization_of_solvable` |
| Huang's same-row three-intersection property | all finite solvable groups | `threeConjugatesSylowSynchronization_of_solvable` |

## Three intersections in finite solvable groups

The strongest theorem in this part of the project is in
[`LisiSabatini/SolvableThreeSylowSynchronization.lean`](LisiSabatini/SolvableThreeSylowSynchronization.lean):

```lean
theorem mixedThreeSylowCoreSynchronization_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    HasMixedThreeSylowCoreSynchronization.{uG, uI} G
```

Expanding the definition, let `I` be a finite index type, let
`p : I → ℕ` be an injective family of primes, and prescribe three independent
Sylow rows

```lean
P Q R : ∀ i, Sylow (p i) G.
```

Then there are two elements `x y : G`, common to every row, such that

```text
P_i ∩ xQ_i x⁻¹ ∩ yR_i y⁻¹ = O_{p_i}(G)
```

for every `i`. Here `O_p(G)` is the largest normal `p`-subgroup of `G`,
formalized as `pCore p G`. Taking `P = Q = R` gives Huang's same-row
three-intersection property:

```lean
theorem threeConjugatesSylowSynchronization_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    HasThreeConjugatesSylowSynchronization.{uG, uI} G
```

The proof has four principal layers:

1. `ThreeConjugatesSynchronization.lean` defines the mixed two-row,
   mixed three-row, and same-row properties.
2. `ThreeSylowSolvableReduction.lean` reduces the solvable theorem through
   an elementary-abelian chief factor to simultaneous affine orbit
   avoidance.
3. The affine modules settle the characteristic and odd-prime branches and
   isolate the remaining noncommuting `2`-core branch.
4. `HallBergerClassificationAssembly.lean` supplies that final input;
   `SolvableThreeSylowSynchronization.lean` closes the unconditional
   solvable-group theorem.

The resulting nilpotent-subgroup consequence is:

```lean
theorem threeNilpotentIntersectionInFitting_of_solvable
    {G : Type uG} [Group G] [Finite G] [IsSolvable G] :
    ThreeNilpotentIntersectionInFitting G
```

Thus, for arbitrary nilpotent subgroups `H`, `K`, and `M` of a finite
solvable group, some `x,y ∈ G` satisfy

```text
H ∩ xKx⁻¹ ∩ yMy⁻¹ ≤ F(G).
```

## Original Lisi–Sabatini results

The original property asks for one conjugator that makes a prescribed
finite family of same-row Sylow intersections inclusion-minimal
simultaneously.

### Finite solvable groups of odd order

[`LisiSabatini/OddOrderProof.lean`](LisiSabatini/OddOrderProof.lean) proves
the stronger Sylow-core statement

```lean
theorem strongLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    StrongLisiSabatini.{uG, uI} G
```

and derives the original formulation:

```lean
theorem hasLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    HasLisiSabatini.{uG, uI} G
```

Solvability remains an explicit hypothesis. Feit–Thompson is neither
imported nor postulated.

### Alternating groups in degree at least 40

[`LisiSabatini/Alternating.lean`](LisiSabatini/Alternating.lean) proves:

```lean
theorem hasLisiSabatini_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasLisiSabatini (alternatingGroup (Fin n))
```

The proof constructs a quadratic conjugacy-class bound from the exact
base-`p` Sylow wreath recurrence and proves a uniform strict budget from
degree `40` onward. It uses no GAP census or project-specific axiom. See
[`ALTERNATING_GROUPS_PROOF.md`](ALTERNATING_GROUPS_PROOF.md) for the
mathematical proof structure and verification report.

## Related formalized endpoints

The repository also contains:

- mixed two-row Sylow-core synchronization for finite solvable groups of odd
  order;
- mixed intersection of two arbitrary nilpotent subgroups into the Fitting
  subgroup in finite solvable groups of odd order; and
- an independent mixed three-row theorem for finite solvable groups with
  commutative Sylow `2`-subgroups, now subsumed by the all-solvable theorem.

## Scope and trust boundary

All group-theoretic endpoints above concern finite groups. The
three-intersection theorem assumes solvability; the alternating result is a
theorem about the original Lisi–Sabatini property, not the
three-intersection property. The project does not claim either result for
all finite groups or for all almost simple groups.

There are no `sorry`, `admit`, or project-specific axioms in the public proof
chain. The focused endpoint audit reports only Lean's standard logical
principles used throughout mathlib: `propext`, `Classical.choice`, and
`Quot.sound`.

## Building and verification

The project is pinned to Lean and mathlib `v4.29.1`.

```text
lake exe cache get
LEAN_NUM_THREADS=4 lake build
```

`LEAN_NUM_THREADS=4` is the recommended setting on machines with about
16 GB of memory.  It prevents several large Lean processes from competing
for compressed memory; machines with substantially more memory may omit it
or choose a higher value.  See
[`BUILD_PERFORMANCE.md`](BUILD_PERFORMANCE.md) for the import-graph and
build-time audit.

The complete public result set and its focused axiom audit can be checked in
one warnings-fatal build:

```text
LEAN_NUM_THREADS=4 lake build --wfail \
  +LisiSabatini:olean \
  +LisiSabatini.HallBergerClassificationAssemblyAxiomAudit:olean \
  +LisiSabatini.SolvableThreeSylowSynchronizationAxiomAudit:olean
```

The library root and two audit roots above cover the alternating theorem,
every solvable-group endpoint advertised in this README, the nilpotent
consequences, every project source module, and both focused `#print axioms`
checks.  Individual endpoints can still be re-elaborated directly when
desired, for example:

```text
lake env lean -DwarningAsError=true LisiSabatini/Alternating.lean
```

## Repository guide

- `LisiSabatini.lean` — combined library entrypoint.
- `LisiSabatini/Basic.lean` and `Strong.lean` — the original
  Lisi–Sabatini definitions and strong form.
- `LisiSabatini/OddOrderProof.lean` — odd-order solvable endpoint.
- `LisiSabatini/Alternating.lean` — alternating endpoint for `n ≥ 40`.
- `ALTERNATING_GROUPS_PROOF.md` — detailed alternating proof note.
- `LisiSabatini/ThreeConjugatesSynchronization.lean` — definitions for
  the mixed and same-row three-intersection problems.
- `LisiSabatini/SolvableThreeSylowSynchronization.lean` — all-solvable
  three-intersection endpoint.
- `LisiSabatini/NilpotentIntersectionApplications.lean` — public
  Fitting-subgroup consequences.
- `LisiSabatini/SolvableThreeSylowSynchronizationAxiomAudit.lean` —
  focused public-endpoint axiom audit.
