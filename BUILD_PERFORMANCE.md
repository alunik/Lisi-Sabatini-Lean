# Lean build-performance audit

This note records the build-scope, import-graph, and cold-build audit
performed on 28 July 2026. The protected scope is the complete set of
results advertised in the README:

- the original Lisi--Sabatini theorem for finite solvable groups of odd
  order, including its stronger Sylow-core form;
- the original Lisi--Sabatini theorem for alternating groups in degree at
  least 40;
- the stronger simultaneous trivial-intersection theorem, and hence the
  original Lisi--Sabatini theorem, for symmetric groups in degree at least
  40;
- mixed and same-row three-Sylow synchronization for all finite solvable
  groups; and
- the nilpotent-intersection consequences and related endpoints listed in
  the README.

No theorem in that scope was deleted, weakened, or replaced by an external
mathematical assumption.

## Protected build closure

The combined library root reaches 216 of the repository's 219 Lean source
files. The only three files outside that closure are deliberate
`#print axioms` entrypoints, all built separately by CI. Thus the exact CI
union covers every project source file and every advertised endpoint.

After the import repairs described below, a static traversal of import
headers gives this root closure:

| Kind | Modules |
| --- | ---: |
| Project modules | 216 |
| Mathlib modules | 2,527 |
| Other vendored dependency modules | 191 |
| Total package-source modules | 2,934 |

The 191 other modules comprise Aesop (86), Batteries (74), Qq (12),
Plausible (11), ProofWidgets (5), ImportGraph (2), and LeanSearchClient (1).
Prebuilt Lean toolchain modules are intentionally not counted as Lake build
jobs.

## First cause: unnecessarily broad imports

Four small arithmetic modules directly imported `Mathlib`, and a fifth
directly imported the `Mathlib.Tactic` umbrella. A direct `Mathlib` import
pulls essentially the complete Mathlib source graph into that module and
forces every downstream Lean process to deserialize the resulting large
environment.

There was a second high-fanout import:

```lean
import Mathlib.RepresentationTheory.Irreducible
```

in `ChiefActionCore.lean`. That file defines and proves its elementary
irreducibility predicate directly; it only requires the basic `Submodule`
lattice instances. The import was replaced by:

```lean
import Mathlib.Algebra.Module.Submodule.Lattice
```

The representation-theoretic import remains in
`NormalRestrictionSemisimple.lean`, where the proof genuinely uses it. A
project-local Hall--Berger edge was narrowed in the same way.

The repaired graph contains no direct `import Mathlib` or
`import Mathlib.Tactic`. A same-parser simulation of the old graph gives
8,380 package-source nodes, compared with 2,934 now after adding the two
symmetric-group modules. The observed default Lake graph is now 3,038 jobs;
the module-migration benchmark below used the preceding 3,037-job graph.

## Second cause: legacy OLean loading

After the import graph was narrowed, the project still used Lean's legacy
file format in all 216 source files then present. A legacy importer must load theorem
proofs and editor data together with the public declarations it needs. On
this project that repeatedly loaded hundreds of megabytes into each Lean
process and produced severe memory compression and swapping.

The 214 files in the library closure at the time of the migration, and the
two symmetric-group modules added afterward, use Lean's module system:

```lean
module

public import ...

@[expose] public section
```

Public declarations are stored separately from private proof and server
artifacts. Ordinary downstream compilation therefore loads the public
interface without loading every imported proof term.

The three axiom-audit files intentionally remain legacy files. Lean 4.29.1
rejects `#print axioms` inside a module file, and the audits are leaf targets
that no project source imports.

The migration exposed a small number of old private declarations that occur
in public types or exposed definition bodies. Those helpers were made public
without changing their statements or proofs. Five generic `mappedCore`
abbreviations then acquired branch-specific names to avoid a public namespace
collision. These are visibility and naming repairs only.

For the same 213 non-audit files below `LisiSabatini/` in the measured
migration, aggregate public OLean size changed as follows:

| Format | Public OLean size |
| --- | ---: |
| Legacy | 77.25 MiB |
| Module system | 18.23 MiB |

That is a 76.38% reduction in the data loaded by ordinary public imports.
The module build also writes 57.8 MiB of private proof artifacts, but those
artifacts are not loaded by ordinary downstream modules.

## Controlled cold-build measurements

The baseline and all module runs used:

- the same Apple-silicon host with 10 logical CPUs and 16 GB memory;
- the same mathematical source tree apart from the module migration and one
  later proof-local typeclass-search simplification;
- the pinned Lean/mathlib 4.29.1 toolchain;
- the already downloaded, pinned dependency cache;
- a freshly absent project `.lake/build` directory; and
- `LEAN_NUM_THREADS=4 lake build --wfail`.

Only project build products were removed between runs. Dependency build
products were retained, so these are cold *project* builds rather than
toolchain/bootstrap measurements. Two four-worker module runs are reported
to expose normal desktop-load variance rather than selecting only the
faster result. The second module run used the exact final source tree.

| Measurement | Legacy | Module run 1 | Exact-final module run |
| --- | ---: | ---: | ---: |
| Lake jobs | 3,037 | 3,037 | 3,037 |
| Wall time | 3,060.20 s | 347.52 s | 402.61 s |
| Wall time (minutes) | 51m 00.2s | 5m 47.5s | 6m 42.6s |
| Maximum resident set size | 2,269,790,208 B | 1,408,532,480 B | 1,418,969,088 B |

The module builds are **7.60--8.81 times faster**, wall-time reductions of
**86.84--88.64%**. Even the conservative exact-final repeat saved 44m 17.6s,
and its maximum resident set size was 37.48% below the legacy run.

Representative cold per-file changes include:

| Module | Legacy | Module |
| --- | ---: | ---: |
| `Basic` | 19 s | 4.4 s |
| `QuasiprimitiveRepresentation` | 66 s | 9.6 s |
| `NormalRestrictionSemisimple` | 81 s | 7.3--10 s |
| `SchurWeylBasis` | 102 s | 15--16 s |

The alternating quadratic envelope took 21 seconds in both module runs.
The remaining cold critical-path outliers varied with host contention:
`CliffordImprimitivity` took 30--31 seconds,
`TwoCoreSymplecticTypeHeadField` 28--44 seconds,
`TwoCoreSymplecticTypeHeadFieldAssembly` 22--24 seconds, and
`TwoCoreSymplecticTypeNonmixedAssembly` 33--43 seconds. These are now
bounded elaboration costs in the protected proof chain, not repeated
whole-library deserialization.

Within `CliffordImprimitivity`, replacing two broad order-isomorphism
`simpa` calls by typed `change` steps and the exact
`Submodule.map_eq_bot_iff`/`map_eq_top_iff` lemmas reduced isolated direct
elaboration from 34.63 to 31.20 seconds and retired about a quarter of that
run's executed instructions. The theorem statements are unchanged.

## Parallelism

The four-worker setting remains best on the 16 GB audit machine. A fresh
module build with six workers took 484.30 seconds, 39.36% longer than the
faster four-worker run and 20.29% longer than the exact-final repeat. The
late serial proof chain suffered enough CPU and memory contention to erase
the extra parallelism; for example,
`TwoCoreSymplecticTypeNonmixedAssembly` rose from 33 to 55 seconds.

Recommended command on a machine with about 16 GB memory:

```text
LEAN_NUM_THREADS=4 lake build
```

Machines with substantially different core counts and memory should
benchmark rather than assume that more workers are faster.

## Correctness and trust checks

After the symmetric-group extension, the full 3,038-job root build passed
with warnings treated as errors. The exact 3,041-job CI union also passed:

```text
LEAN_NUM_THREADS=4 lake build --wfail \
  +LisiSabatini:olean \
  +LisiSabatini.HallBergerClassificationAssemblyAxiomAudit:olean \
  +LisiSabatini.SolvableThreeSylowSynchronizationAxiomAudit:olean \
  +LisiSabatini.SymmetricAxiomAudit:olean
```

All three focused audit leaves report only:

```text
propext, Classical.choice, Quot.sound
```

A fresh module-mode consumer importing only `LisiSabatini` successfully
checked all five headline endpoints:

- `hasLisiSabatini_of_solvable_of_odd`;
- `hasLisiSabatini_alternatingGroup_ge_forty`;
- `hasLisiSabatini_symmetricGroup_ge_forty`;
- `mixedThreeSylowCoreSynchronization_of_solvable`; and
- `threeConjugatesSylowSynchronization_of_solvable`.

No external classification theorem or other new axiom was introduced by the
performance work.

## CI and reproducibility

CI first builds the warnings-fatal root-and-audits union above, then runs
Lean's independent checker in a separate dependent job using the completed
build cache. This gives elaboration and independent checking separate runner
budgets while retaining both gates. The union covers all 219 project files
without redundantly re-elaborating already-covered endpoint files.

On the audit machine, `lake env leanchecker` completed successfully in
1,529.59 seconds (25m 29.6s) with a maximum resident set size of
2,419,032,064 bytes. This independent kernel traversal is therefore kept as
a required gate, but it is not included in the project-elaboration timings
above.

To reproduce a cold project build without discarding the downloaded
dependency cache, move the project's `.lake/build` directory aside and run:

```text
/usr/bin/time -l env LEAN_NUM_THREADS=4 lake build --wfail
```

Do not use `lake clean` for this benchmark: it also cleans dependency build
products and changes the experiment.

The performance work deliberately retained every protected theorem, every
advertised result, and the standard logical axiom audits.
