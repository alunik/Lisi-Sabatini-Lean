# Lean build-performance audit

This note records the build-scope and import-graph audit performed on
28 July 2026.  The protected scope is the complete set of results advertised
in the README:

- the original Lisi--Sabatini theorem for finite solvable groups of odd
  order, including its stronger Sylow-core form;
- the original Lisi--Sabatini theorem for alternating groups in degree at
  least 40;
- mixed and same-row three-Sylow synchronization for all finite solvable
  groups; and
- the nilpotent-intersection consequences and related endpoints listed in
  the README.

## What is actually in the protected build

The combined library root reaches 214 of the repository's 216 Lean modules.
The only two modules outside that closure are deliberate `#print axioms`
entrypoints.  Both are compiled separately by the focused CI audit.
Consequently, deleting mathematical source files cannot materially shorten
the build without deleting a public result.

After the import repairs described below, a static traversal of import
headers gives this root closure:

| Kind | Modules |
| --- | ---: |
| Project modules | 214 |
| Mathlib modules | 2,527 |
| Other vendored dependency modules | 191 |
| Total package-source modules | 2,932 |

The 191 other modules comprise Aesop (86), Batteries (74), Qq (12),
Plausible (11), ProofWidgets (5), ImportGraph (2), and LeanSearchClient (1).
Prebuilt Lean toolchain modules are intentionally not counted as Lake build
jobs.

## Root cause

Four small arithmetic modules directly imported `Mathlib`, and a fifth
directly imported the `Mathlib.Tactic` umbrella.  A direct `Mathlib` import
pulls essentially the complete Mathlib source graph into that module.  More
importantly, every downstream Lean process must then deserialize that same
large environment.

There was a second high-fanout import:

```lean
import Mathlib.RepresentationTheory.Irreducible
```

in `ChiefActionCore.lean`.  That file defines and proves its elementary
irreducibility predicate directly; it only requires the basic `Submodule`
lattice instances.  The import was therefore replaced by:

```lean
import Mathlib.Algebra.Module.Submodule.Lattice
```

The general representation-theoretic import is still present later in
`NormalRestrictionSemisimple.lean`, where the protected proof genuinely
uses `MonoidHom.IsIrreducible` and the simple-module bridge.  Moving it to
the owning file shortens many intermediate environments without hiding the
real dependency.  The public general
`Representation.IsQuasiprimitive` wrapper is retained with
`Representation.IsIrreducible` written in its exactly unfolded form,
`IsSimpleOrder (Subrepresentation rho)`, so its definition remains
compatible without forcing that later API into this high-fanout core.

One project-local edge was also wider than its consumer:
`HallBergerHeadTransport.lean` imported the full distinguished-rotation
development but used only the maximal-class head structures already
exported by `TwoCoreSymplecticTypeFrontier.lean`.  Importing that frontier
directly removes the 770 KB rotation OLean from the late cyclic
Hall--Berger branch's environment.

A same-parser simulation of the old broad import gives 8,380 package-source
nodes, compared with 2,932 now: a reduction of 5,448 nodes, or 65.01%.
Lake's job count is close to, but not identical with, a source-node count;
the observed default-root graph fell from 8,462 jobs to 3,037, removing
5,425 jobs (64.11%).

The final project has no direct `import Mathlib` and no direct
`import Mathlib.Tactic`.  Full-build testing also exposed APIs and tactics
that downstream files had received accidentally from the umbrellas,
including `Fintype.exists_ne_of_one_lt_card`, `Nat.Prime`, `nlinarith`,
the prime-normalization tactic, and the representation irreducibility API.
Their dependencies are now declared at the narrowest owning layer.

## Measured evidence

Measurements were taken on an Apple-silicon machine with ten cores and
16 GB of memory, after retrieving the pinned Mathlib cache.  These are
engineering measurements, not claims about every host: filesystem cache,
memory compression, and concurrent desktop load affect wall time.

The unmodified clean build was stopped after 1,428.65 seconds
(23 minutes 48.65 seconds).  It had reached only job 8,328 of 8,462 and was
using about 14 GB of swap.  Representative arithmetic-module times printed
by Lake were:

| Module | Broad-import build time |
| --- | ---: |
| `OddRegularListColoringArithmetic` | 698 s |
| `RegularTernaryListColoringArithmetic` | 698 s |
| `TwoCoreDistinguishedJointBudgetArithmetic` | 716 s |
| `ExtraspecialArithmetic` | 700 s |
| `CyclicMaximalTwoAdicArithmetic` | 263 s |

After narrowing their imports, the same five source files all elaborated
with warnings treated as errors.  In an intentionally parallel diagnostic
run, their wall times were 22.76--23.41 seconds; `ExtraspecialArithmetic`
then took 13.96 seconds when rerun alone.  The two sets of figures are not a
controlled microbenchmark, but the order-of-magnitude difference and the
65% graph reduction identify the cause unambiguously.

A clean ten-worker build after the first five import repairs was stopped
after 623.89 seconds at job 2,926 of a then-known 3,036 jobs.  It had already
produced 106 project OLean files.  This trial still predated the
`ChiefActionCore` repair.

The final current-tree root build completed successfully at 3,037 jobs.
The exact warnings-fatal CI union completed at 3,038 jobs, covering all 216
project sources.  Both focused `#print axioms` entrypoints reported only
`propext`, `Classical.choice`, and `Quot.sound`.

The protected all-solvable Hall--Berger chain is now the clean-build
critical path.  Under the four-worker cap, its late cyclic seed and maximal
subgroup modules took 41 and 40 seconds, respectively, versus 61 and 69
seconds in the swap-bound unrestricted run.  This remaining cost is real
proof-environment work; removing that source would remove the all-solvable
result identified as protected in the README.

## Parallelism and memory

Lean's runtime honors the `LEAN_NUM_THREADS` environment variable.  On the
16 GB audit machine, unrestricted Lake used ten concurrent Lean processes;
several simultaneously resident processes required between 0.5 and 1 GB
each.  Ten workers maximized throughput but caused heavy memory compression.
Four workers kept active Lean memory predictable and were used for the
full correctness run.

Recommended stable command for a machine with about 16 GB of memory:

```text
LEAN_NUM_THREADS=4 lake build
```

On a machine with substantially more memory, omitting the variable can
increase throughput.  On a smaller machine, use two workers.

## CI

The old workflow first built the combined library and then directly
re-elaborated four already-covered endpoint files.  The new workflow uses
one warnings-fatal build with the library root and two audit roots:

```text
lake build --wfail \
  +LisiSabatini:olean \
  +LisiSabatini.HallBergerClassificationAssemblyAxiomAudit:olean \
  +LisiSabatini.SolvableThreeSylowSynchronizationAxiomAudit:olean
```

Their union covers all 216 project source modules, every public result in
the README, and both focused axiom checks.  The independent Lean checker
remains enabled; the speedup does not weaken the trust boundary.

Lake's built-in `:olean` facet still asks the compiler for `.olean`,
`.ilean`, and generated C artifacts in Lean/Lake 4.29.1.  A custom
OLean-only build system would duplicate Lake's dependency and cache logic
and was therefore rejected.

## Reproducibility

To reproduce a cold project build without discarding the downloaded
dependency cache, move the project's `.lake/build` directory aside and run
the command above.  `lake clean` also cleans dependency build products, so
it is not suitable when the purpose is to benchmark only this project's
source.

The build audit deliberately retained every protected theorem, every public
declaration, and all standard logical axiom checks.  No advertised theorem
conclusion or trust assumption was changed by the performance work.
