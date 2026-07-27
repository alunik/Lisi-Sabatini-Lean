# Lisi–Sabatini: odd-order soluble and large alternating groups

This Lean 4/mathlib project formalizes two cases of the Lisi–Sabatini
conjecture:

- finite soluble groups of odd order; and
- alternating groups `A_n` in every degree `n ≥ 40`.

The alternating endpoint is:

```lean
theorem hasLisiSabatini_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasLisiSabatini (alternatingGroup (Fin n))
```

Its proof is fully checked by Lean. It constructs a quadratic
conjugacy-class bound from the exact base-`p` Sylow wreath recurrence and
proves a uniform strict budget from degree 40 onward.

The alternating endpoint uses no GAP computation, finite-census
certificate, or project-specific axiom. Its axiom audit reports only the
standard principles used throughout mathlib:
`propext`, `Classical.choice`, and `Quot.sound`.

The odd-order endpoint is:

```lean
theorem hasLisiSabatini_of_solvable_of_odd
    {G : Type uG} [Group G] [Finite G] [IsSolvable G]
    (hodd : Odd (Nat.card G)) :
    HasLisiSabatini.{uG, uI} G
```

It follows from the stronger theorem
`strongLisiSabatini_of_solvable_of_odd`.

## Alternating proof structure

For a Sylow `p`-subgroup `P ≤ S_n`, let `a(n,p,j)` be the number of
elements of `P` with cycle type `p^j 1^(n-pj)`, and set

```text
C(n,p,j) = n! / (p^j j! (n-pj)!).
```

The normalized quadratic cost in the bad-conjugator argument is

```text
sum_j a(n,p,j)^2 / C(n,p,j).
```

For `p = 2`, only even `j` contribute after restriction to `A_n`. The
formal proof:

1. constructs a concrete Sylow subgroup of `S_n` from the base-`p` digits
   of `n`;
2. proves the exact iterated-wreath recurrence for its cycle-profile
   coefficients;
3. identifies those coefficients with Sylow/conjugacy-class
   intersections;
4. transfers linked Sylow rows from `S_n` to `A_n`, losing at most a
   factor four and charging only classes that meet `A_n`; and
5. bounds the exact coefficients by a monotone negative-binomial
   envelope.

For `n ≥ 40`, the symmetric-profile budget before the factor-four transfer
is

```text
3/16 + 1/25 + 1/10000 + 1/2400 + 1/1024
  = 439667/1920000
  < 1/4.
```

Consequently, the transferred bad loci have total normalized size below
one, so a common good conjugator exists.

See [`ALTERNATING_GROUPS_PROOF.md`](ALTERNATING_GROUPS_PROOF.md) for the
mathematical details and verification report.

## Scope

For `n ≥ 40`, the alternating proof establishes the stronger conclusion
that all prescribed same-prime Sylow intersections can be made trivial
simultaneously. The exported theorem records the original
inclusion-minimal Lisi–Sabatini property.

Solubility is an explicit hypothesis in the odd-order theorem. The
mathematical Feit–Thompson theorem would remove it, but Feit–Thompson is
neither imported nor postulated here. No unrestricted strong
Lisi–Sabatini theorem for general finite groups is asserted.

## Building

The project is pinned to Lean and mathlib `v4.29.1`.

```text
lake exe cache get
lake build
```

To check the two publication endpoints with warnings treated as errors:

```text
lake env lean -DwarningAsError=true LisiSabatini/OddOrderProof.lean
lake env lean -DwarningAsError=true LisiSabatini/Alternating.lean
```

## Repository layout

- `LisiSabatini.lean` — library entrypoint.
- `LisiSabatini/Alternating.lean` — alternating theorem for `n ≥ 40`.
- `LisiSabatini/AlternatingSylowQuadraticEnvelope.lean` — uniform
  quadratic envelope.
- `LisiSabatini/AlternatingSylowQuadraticFormula.lean` — exact class-sum
  formula.
- `LisiSabatini/AlternatingSylowBasePBlocks.lean` — concrete Sylow model.
- `LisiSabatini/SylowPairQuadraticBound.lean` — generic bad-locus class
  bound.
- `LisiSabatini/OddOrderProof.lean` — odd-order group-theoretic induction
  and public theorems.
- `LisiSabatini/PrimewiseAffineRegularityCore.lean` — linear induction.
- `LisiSabatini/OddOrderChiefFactorCore.lean` — minimal-normal
  chief-factor construction.
- `LisiSabatini/NormalComponentReductionCore.lean` — affine lifting
  interface.
