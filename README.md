# Sylow synchronization in finite groups

Lean 4 formalization of results in **Sylow synchronization in finite groups:
The good case**, by Hong Yi Huang, Francesca Lisi, Aluna Rizzoli and Luca Sabatini.

| Result | Scope |
| --- | --- |
| Main solvable theorem | Every quotient of the finite solvable group satisfies property $(*)$ |
| Translated regular orbits, Proposition 2.3 | Faithful completely reducible modules of finite nilpotent groups, over arbitrary fields |
| Symmetric and alternating groups | The Lisi–Sabatini conjecture in every degree |
| Odd-order corollaries | The conjecture and nilpotent-intersection consequence, using the formalized Feit–Thompson theorem |

Property $(*)$ means that, for each prime $p$, two Sylow $p$-subgroups
intersect in $O_p(G)$. The conjecture asks for one conjugating element
making all prescribed Sylow intersections inclusion-minimal simultaneously.
For $S_8$, the formalization proves this inclusion-minimality conclusion;
it does not assert trivial Sylow 2-intersections.

Start with **[LisiSabatini.lean](LisiSabatini.lean)** and the
**[theorem map](docs/THEOREMS.md)**. The formal proofs sometimes use
different arguments from the manuscript. The external Burness–Huang result
for nonalternating finite simple groups is not part of this formalization.

## Build and check

Install [Lean through elan](https://github.com/leanprover/elan). The repository
pins Lean `v4.34.0-rc2` and mathlib; no dependency update is needed.

```sh
lake exe cache get
LEAN_NUM_THREADS=2 lake build --wfail \
  +LisiSabatini:olean +LisiSabatini.PaperAlignmentAxiomAudit:olean
python3 scripts/check_axioms.py
```

This builds the paper's core results and checks the exact 18 declarations
listed in its audit. Their transitive axioms are restricted to
`propext`, `Classical.choice` and `Quot.sound`.

The odd-order corollaries have a separate, larger dependency:

```sh
LEAN_NUM_THREADS=2 lake build \
  +LisiSabatini.FeitThompsonApplicationsAxiomAudit:olean
python3 scripts/check_axioms.py --include-feit-thompson
```

The vendored Feit–Thompson source is pinned and retains its upstream
license and provenance. Its legacy deprecation warnings are documented;
the project entrypoints are checked separately with warnings treated as
errors. See [verification](docs/VERIFICATION.md) for the complete checks,
kernel-replay scope and source records.

Nine principal statements also passed [Comparator checks](verification/comparator/README.md)
against separately stated specifications, using the same three-axiom allowlist.

The independent [Magma reproduction of Section 3](computations/section3/README.md)
checks both families for $5\le n\le40$, the nilpotent-pair assertion for
$9\le n\le40$, and the paper's numerical anchors. It runs without Lean.

## Repository contents

- [LisiSabatini/](LisiSabatini/): the theorems and their proof dependencies.
- [Certificate guide](docs/CERTIFICATES.md): finite certificates and deterministic regeneration.
- [Section 3 computations](computations/section3/README.md): standalone Magma code and exact certificates.
- [vendor/odd-order/](vendor/odd-order/): the pinned Feit–Thompson dependency, with its [license](vendor/odd-order/LICENSE).
- [scripts/check_axioms.py](scripts/check_axioms.py): exact declaration and axiom checks used in CI.

## License

The project is licensed under [Apache-2.0](LICENSE). Vendored code retains
its original license and attribution.
