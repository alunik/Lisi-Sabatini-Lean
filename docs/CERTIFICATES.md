# Finite certificates

The small-degree proofs use explicit finite data. Python proposes permutation
rows and witnesses; Lean checks subgroup closure, Sylow orders, separation and
finite counts with `decide +kernel`. No Python result is accepted as a proof.
All permutations use zero-based image lists and composition
`(a * b)(i) = a(b(i))`.

## Certificates used by the paper

| Case | Finite input | Lean acceptance |
|---|---|---|
| $A_8$ | Four subgroup rows of orders 64, 9, 5 and 7; one explicit even conjugator | [A8Rows](../LisiSabatini/FiniteCertificates/A8Rows.lean), [A8SylowTwoWitness](../LisiSabatini/FiniteCertificates/A8SylowTwoWitness.lean) |
| Sylow 2-row in $S_8$ | 128 binary-tree automorphisms; three generator actions and a spanning tree | [FastData](../LisiSabatini/SymmetricEightCertificates/FastData.lean), [SymmetricEightFastSubgroup](../LisiSabatini/SymmetricEightFastSubgroup.lean) |
| $S_5$, $S_6$ at 2 | Rows of orders 8 and 16, with one good conjugator each | [SylowTwoWitnesses](../LisiSabatini/SymmetricFiniteCertificates/SylowTwoWitnesses.lean) |
| $S_6$ at 3 | All 720 permutations and the nine-element Sylow row | [S6ThreeTable](../LisiSabatini/SymmetricFiniteCertificates/S6ThreeTable.lean), [S6ThreeCounts](../LisiSabatini/SymmetricFiniteCertificates/S6ThreeCounts.lean) |
| $S_9$, $S_{10}$, $S_{12}$ at 2 | Respectively 7, 6 and 41 good double-coset representatives | [S9](../LisiSabatini/SymmetricDoubleCosetCertificates/S9/Certificate.lean), [S10](../LisiSabatini/SymmetricDoubleCosetCertificates/S10/Certificate.lean), [S12](../LisiSabatini/SymmetricDoubleCosetCertificates/S12/Certificate.lean) |

For $A_8$, the kernel verifies all indexed row products, with the 64-by-64
calculation split into bounded pieces. A one-sided fingerprint test certifies
nonmembership for the explicit conjugator; a collision can only reject a
candidate. One good double coset then gives the required counting bound.

The fast 128-element row certificate checks 384 generator products and 127
spanning-tree edges. The imported [Table](../LisiSabatini/SymmetricEightCertificates/Table.lean)
also contains literal transversal data; these are preserved to reproduce that
module exactly. The $S_8$ theorem itself uses the index-two argument from $A_8$
in [SymmetricEightVerified](../LisiSabatini/SymmetricEightVerified.lean).

The $S_6$ prime-three calculation uses 30 chunks of 24 permutations and proves
an upper bound of 72 bad conjugators. The other odd-prime bounds for $S_5$ and
$S_6$ use symbolic arithmetic. The resulting total bad proportions are
$11/15$ and $139/180$.

For $S_9$, $S_{10}$ and $S_{12}$, the binary rows have orders 128, 256 and 1024.
Centralizer signatures distinguish most double cosets; explicit failed-block
witnesses distinguish the remaining pairs. The resulting total bad proportions
are $6253/6480$, $28177/28350$ and $239418491/239500800$, each less than one.
The representatives are explicit retained witnesses. Reproduction regenerates
and checks their certificates; it does not rerun the original witness search.

## Reproduction

From the repository root, with standard-library Python 3 and without `-O`:

```sh
python3 scripts/certificates/check.py
```

This command checks the [SHA-256 manifest](../data/certificates/manifest.json)
and reproduces all **201 generated Lean modules**, comparing their exact bytes
without modifying the source tree. A failed comparison exits with an error.
The Lean build described in the [README](../README.md) is the separate proof
acceptance step.

Individual checks are:

```sh
python3 LisiSabatini/FiniteCertificates/generate_a8.py --check
python3 LisiSabatini/FiniteCertificates/generate_a8_rows.py --check
python3 LisiSabatini/FiniteCertificates/generate_a8_fingerprints.py --check
python3 LisiSabatini/SymmetricEightCertificates/generate.py --check
python3 LisiSabatini/SymmetricEightCertificates/generate_fast.py --check
python3 LisiSabatini/SymmetricFiniteCertificates/generate.py --check
python3 scripts/certificates/generate_double_cosets.py --check
```

Omitting `--check` writes the deterministic output. The last generator also
accepts `--output-root DIRECTORY` for a separate staging directory and
`--degree 9`, `--degree 10` or `--degree 12` for a single degree.

The inputs consist of the A8 subgroup rows, the P128 table and fast-closure
data, and three small double-coset witness files in
[data/certificates](../data/certificates). The manifest records their hashes
alongside those of the generators and generated Lean modules. The A8 row data
are generated from the displayed subgroup generators; the double-coset files
contain only the degree, subgroup order, representatives and separation data.
