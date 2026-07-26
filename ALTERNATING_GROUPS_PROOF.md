# Lisi–Sabatini for alternating groups in degree at least 40

## Result

The public Lean theorem is:

```lean
theorem hasLisiSabatini_alternatingGroup_ge_forty
    (n : ℕ) (hn : 40 ≤ n) :
    HasLisiSabatini (alternatingGroup (Fin n))
```

It proves the original inclusion-minimal Lisi–Sabatini property for the
standard alternating group `A_n` whenever `n ≥ 40`. The proof actually
produces one conjugator for which every prescribed same-prime Sylow
intersection is trivial.

## Literature context

Lisi and Sabatini prove the alternating case for all sufficiently large
degrees, with an ineffective threshold. Burness and Huang computationally
verify the simple alternating groups through degree 50 and record the
remaining alternating family as open:

- F. Lisi and L. Sabatini,
  [*Sylow subgroups for distinct primes and intersection of nilpotent
  subgroups*](https://arxiv.org/abs/2505.21222).
- T. C. Burness and H. Y. Huang,
  [*On the intersections of nilpotent subgroups in simple
  groups*](https://arxiv.org/abs/2508.03479).

This formalization supplies an effective, uniform quadratic envelope from
degree 40 onward.

## Verification status

The theorem compiles with Lean 4.29.1 and mathlib 4.29.1, including with
warnings treated as errors:

```text
lake env lean -DwarningAsError=true LisiSabatini/Alternating.lean
```

Lean reports only its standard logical dependencies:

```text
hasLisiSabatini_alternatingGroup_ge_forty:
  propext, Classical.choice, Quot.sound
```

In particular, the theorem uses no project-specific axiom.

## Exact quadratic reduction

For a finite group `G`, prescribed Sylow rows `P,Q`, and a conjugacy class
`C`, the integer quadratic term is

```text
(|G| / |C|) |C_order-p ∩ P| |C ∩ Q|.
```

`SylowPairQuadraticBound.lean` bounds the number of bad conjugators by the
sum of these terms. A second finite union bound over injectively labelled
primes gives a common conjugator whenever the sum of normalized same-row
costs is below one.

For `S_n`, an order-`p` element has cycle type `p^j 1^(n-pj)`, whose class
has cardinality

```text
C(n,p,j) = n! / (p^j j! (n-pj)!).
```

If `a(n,p,j)` counts such elements in a Sylow row, the normalized cost is

```text
Q(n,p) = sum_j a(n,p,j)^2 / C(n,p,j).
```

For `p = 2`, restriction to classes meeting `A_n` retains exactly the even
indices `j`.

## Exact Sylow profile

Let `W_k` be the standard Sylow `p`-subgroup on `p^k` letters. Its order
and prime-cycle profile satisfy

```text
|W_0| = 1
|W_(k+1)| = p |W_k|^p

A_0(X) = 1
A_(k+1)(X) =
  A_k(X)^p + (p-1)|W_k|^(p-1) X^(p^k).
```

The first term has trivial top permutation in the regular wreath product.
For a nontrivial top permutation, the product of the base components must
be one, leaving `|W_k|^(p-1)` choices.

The Lean development constructs the base-`p` block action on `n` letters,
proves that its image has the exact `p`-part of `n!`, and identifies every
profile coefficient with the corresponding Sylow/class intersection.

## Uniform envelope and budget

The coefficientwise majorant is

```text
B(p,m,j) = (p-1)^j * multichoose(m,j),
```

where `m = floor(n/p)`. Lean proves

```text
a(n,p,j) <= B(p,floor(n/p),j).
```

At consecutive `p`-block starts, every old quadratic term decreases, and
the new top terms are paid for by the former top term. For `p = 2`, the
argument advances two blocks at a time because only even indices survive
the alternating restriction.

The anchors used from degree 40 onward are:

```text
p=2, even rows:  M2(40) < 3/16
p=3:             M(39,3) < 1/25
p=5:             M(40,5) < 1/10000
p=7:             Q(n,7) <= 1/2400
p>=11:           sum_p Q(n,p) <= 1/1024.
```

Thus, for every finite injective family of primes and every `n ≥ 40`,

```text
sum_p Q_A-profile(n,p)
  < 3/16 + 1/25 + 1/10000 + 1/2400 + 1/1024
  = 439667/1920000
  < 1/4.
```

A linked Sylow row in `A_n ≤ S_n` has cost at most four times the
restricted ambient cost: a factor two from possible class splitting and a
factor two from the index in the normalization. The transferred total is
therefore strictly below one.
