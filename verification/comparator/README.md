# Comparator checks

This separate project compares the paper's proofs with independently written
formal statements. It does not change the main library's dependencies.

Both configurations passed on 23 September 2026: five core statements and
four odd-order statements. The [verification record](../2026-09-23/comparator.json)
includes tool/source hashes, exact targets, timings, and complete output logs.

The trusted [Definitions](Definitions.lean) module imports only Mathlib and
spells out Sylow intersections, prime cores, the Fitting subgroup, and the
synchronization properties. Neither challenge imports a `LisiSabatini` proof.
The corresponding solution files prove those statements by applying the
existing paper results; they do not import the challenge files.

| Configuration | Statements checked |
| --- | --- |
| [core.json](core.json) | Good solvable theorem and its nilpotent-subgroup consequence; Proposition 2.3; all alternating groups; all symmetric groups |
| [odd-order.json](odd-order.json) | Odd-order prime-core synchronization, inclusion-minimal synchronization, and the self/mixed nilpotent-intersection corollaries |

The symmetric-group statement uses inclusion-minimality, including in degree
eight. The translated-orbit statement imposes no finiteness or dimension
condition on the field or module. `EveryQuotientHasStar` uses surjective images
and prescribed Sylow subgroups; Sylow conjugacy identifies this with the
paper's existence of a pair in each normal quotient.

The `sorry` terms in the two **Challenge** files are deliberate specification
holes. They are not paper proofs. Comparator rejects `sorryAx` in the
**Solution** proof closures, whose only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`.

## Pinned tools

Use these compatible upstream versions:

- Lean: `leanprover/lean4:v4.34.0-rc2`.
- [Comparator](https://github.com/leanprover/comparator/tree/2312244ac716564a61cc0bf4e107d9abf1757a61):
  `2312244ac716564a61cc0bf4e107d9abf1757a61`.
- [lean4export](https://github.com/leanprover/lean4export/tree/cacf989bd75f608700820f6afc595f32e7a99a4d):
  `cacf989bd75f608700820f6afc595f32e7a99a4d`, fixed by Comparator's manifest.

Build the tools in their own checkout with `lake build comparator lean4export`.
Do not run `lake update` or upgrade the paper's toolchain to follow Comparator's
moving default branch.

## Private verification layout

Run from this directory:

```sh
python3 stage.py
```

When copied elsewhere, use `python3 stage.py --source /path/to/paper`.
The script copies the paper source/configuration and vendor files into
`.lake/packages/LisiSabatini`, derives a manifest with identical dependency
pins, and records the copied source hashes in
`.lake/staged-source-files.sha256`. It does not download or build anything.

The resulting layout is:

```text
verification-project/
  Definitions.lean, Challenge.lean, Solution.lean, ...
  .lake/
    build/                              # challenge/solution build products
    packages/
      mathlib/, batteries/, ...         # pinned dependencies and their builds
      LisiSabatini/
        LisiSabatini.lean, LisiSabatini/, ...
        .lake/build/                    # paper build products
        vendor/odd-order/.lake/build/   # optional Feit–Thompson build products
```

Comparator permits build writes to the verification project's `.lake` directory
and to `/dev`. Keep the trusted statement and configuration files **outside
`/dev`**, including outside `/dev/shm`. Use private dependency and build copies
under `.lake`, rather than links to shared writable caches. A `.lake` link to
its own unique private temporary directory is also suitable. Populate those
copies from matching, trusted Linux build products,
or build the staged package before the audit. The exporter and proof files must
use the same Lean version and dependency pins. A trusted Mathlib cache may be
downloaded before running Comparator.

The manifest tracks the parent paper's pins. If those pins change, run
`stage.py` again and review the generated manifest before verification.

For development, the wrappers can be compiled directly:

```sh
LEAN_NUM_THREADS=2 lake build +Challenge:olean +Solution:olean
LEAN_NUM_THREADS=2 lake build +OddOrderChallenge:olean +OddOrderSolution:olean
```

Challenge warnings about `sorry` are expected. These development builds alone
do not constitute a Comparator check.

## Running Comparator

Follow the pinned Comparator's
[sandbox instructions](https://github.com/leanprover/comparator/blob/2312244ac716564a61cc0bf4e107d9abf1757a61/README.md).
Run as an unprivileged Linux user with real Landrun and `lean4export` on `PATH`.
The documented command adds an AF_UNIX restriction needed on affected kernels:

```sh
systemd-run --property=RestrictAddressFamilies=~AF_UNIX \
  --user --pty -E PATH="$PATH" --working-directory "$(pwd)" -- \
  bash -c 'lake env /path/to/comparator core.json'
```

Repeat with `odd-order.json` for the separate Feit–Thompson check. A controlled
runner may instead impose the AF_UNIX restriction with a documented and tested
seccomp filter; record its implementation and sandbox checks with the receipt.
The upstream `fake-landrun.sh` is for development and is not a production
sandbox.

For x86-64 Linux systems without a user systemd service, the recorded check
uses [deny-af-unix.c](deny-af-unix.c). It installs a fail-closed seccomp filter
before executing Comparator, blocking Unix-domain sockets, socket pairs and
the io_uring API, and rejecting other syscall ABIs. Compile it with
`cc -O2 -Wall -Wextra -Werror deny-af-unix.c -o deny-af-unix`, then run:

```sh
/path/to/deny-af-unix lake env /path/to/comparator core.json
```

Real Landrun is still required. The run record includes smoke tests of the
filter and of write protection for the actual trusted Challenge file.

Comparator checks that the proved statements and all definitions used in them
agree with the trusted challenges, rejects unpermitted transitive axioms, and
replays the exported proof terms in Lean's kernel. The default run is not an
independent kernel implementation. An additional external kernel requires its
own explicit configuration and verification record.

Record source/tool hashes, commands, the sandbox configuration, complete logs,
and exit statuses for each run. Presence of these configuration files is not a
claim that either check has passed; the run records establish that status.
