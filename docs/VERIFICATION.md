# Verification

Use the pinned toolchain and dependency manifest. A first build needs network
access for the toolchain and mathlib cache. Do not run `lake update` when
reproducing this version.

## Paper results

```sh
lake exe cache get
python3 -m unittest discover -s tests -p 'test_check_axioms.py'
python3 scripts/certificates/check.py
LEAN_NUM_THREADS=2 lake build --wfail \
  +LisiSabatini:olean +LisiSabatini.PaperAlignmentAxiomAudit:olean
python3 scripts/check_axioms.py
lake env leanchecker --fresh --verbose LisiSabatini
```

The build treats project warnings as errors. The axiom checker requires
exactly the 18 declarations listed in
[PaperAlignmentAxiomAudit](../LisiSabatini/PaperAlignmentAxiomAudit.lean),
and rejects missing, duplicate or unexpected reports. Each declaration's
transitive axioms must belong to the allowlist `propext`, `Classical.choice`
and `Quot.sound`. In particular, `sorryAx` and extra mathematical axioms
are rejected.

The certificate reproduction command checks exact source bytes. Lean then
checks the finite calculations as part of the proofs; Python is not trusted
to establish any mathematical assertion.

## Odd-order corollaries

These import the formalized Feit–Thompson theorem and have a larger build
and replay closure. Build that dependency first, then check the project
entrypoints with warnings treated as errors:

```sh
LEAN_NUM_THREADS=2 lake build \
  +LisiSabatini.FeitThompsonApplicationsAxiomAudit:olean

for source in \
  LisiSabatini/FeitThompsonApplications.lean \
  LisiSabatini/FeitThompsonApplicationsAxiomAudit.lean
do
  lake env lean -j1 \
    -DwarningAsError=true \
    -DrelaxedAutoImplicit=false \
    -Dweak.linter.mathlibStandardSet=true \
    -Dweak.linter.style.header=false \
    "$source"
done

python3 scripts/check_axioms.py --include-feit-thompson
lake env leanchecker --fresh --verbose LisiSabatini.FeitThompsonApplications
```

The combined audit checks **24 declarations**: the 18 paper endpoints,
`OddOrder.feitThompson` itself and the five odd-order applications. It uses
the same three-axiom allowlist throughout.

The vendored source has legacy deprecation warnings. These are permitted
only in the dependency build; the two project entrypoints are compiled
separately under the strict settings above. The dependency's immutable
export record and file hashes are in
[vendor/odd-order/provenance](../vendor/odd-order/provenance). Check them with:

```sh
python3 vendor/odd-order/provenance/verify-source.py
```

The vendor's compatibility notes describe its preparation history. They
are not a report of this repository's current verification status.

## What kernel replay checks

`leanchecker --fresh` reconstructs a fresh environment and rechecks the safe
declarations in the imported proof closure using Lean's kernel. This is an
additional check of compiled proof objects, not a separate implementation
of type theory. It complements the exact axiom audit; neither replaces the
other.

[GitHub Actions](../.github/workflows/ci.yml) runs the paper build, certificate
reproduction, exact axiom audit and fresh kernel replay on pull requests
and pushes to `main`. The larger Feit–Thompson check is available through
the workflow's **include_feit_thompson** manual option.
CI caches only this project's build products; mathlib is fetched from its
own cache. This avoids creating a second archive of the entire dependency
tree on the hosted runner.

## Recorded verification

The [23 September 2026 record](../verification/2026-09-23/summary.json)
reports successful strict project builds, all 24 exact axiom reports, and
ordinary and fresh kernel replay of the Feit–Thompson applications. It is
a concise extract from the verification receipts, with the checked
[source hashes](../verification/2026-09-23/source-files.sha256) and log hashes.
Sources and dependency pins were unchanged throughout verification.

The core proof modules are unchanged from a successful fresh replay on
21 September. The public imports and audit list were narrowed and strictly
rebuilt; the changed odd-order wrapper received the new fresh replay.
The record distinguishes this continuity check from a new replay of the
whole core. GitHub CI additionally replays the current core entrypoint.
