# Section 3: recorded Magma verification

The [standalone computation](../../computations/section3/README.md) passed on
23 September 2026 with Magma **2.29-5**, on macOS (arm64), using one process.
The full run took **0.150 seconds CPU / 0.218 seconds wall time**, including
the independent comparison with actual Sylow and conjugacy-class data.

- [Complete Magma output](macos/magma.log)
- [Receipt, exact bounds and source SHA-256 hashes](macos/receipt.json)

The checked manuscript snapshot is Overleaf Git commit
`e7896fe09f180baba9298732eb9c92be0464b64c`. The receipt hashes every executable
source file and the explicit witness data; no Lean build or research data
outside this repository is needed.

## Coverage

| Check | Coverage | Result |
| --- | --- | --- |
| Lisi–Sabatini for $S_n$ | Every $5\le n\le40$, 36 groups | PASS |
| Lisi–Sabatini for $A_n$ | Every $5\le n\le40$, 36 groups | PASS |
| Every pair of nilpotent subgroups | Both families, every $9\le n\le40$, 64 groups | PASS |
| Numerical anchor inequalities | Four $M(n,p)$ values and $M_{\mathrm{ev}}(40)$ | PASS |
| Final rational budgets | Symmetric and alternating | PASS |
| Formula comparison with actual groups | Every prime in degrees 5 through 12, 32 cases | PASS |

The $S_8$ conclusion is inclusion-minimality, with minimum binary intersection
order **2**. The finite checks do not establish the paper's infinite
monotonicity lemmas or prime-tail argument.

The optional wrapper was also checked against truncated output, an omitted
degree, a runtime error, and a non-strict bound; it rejected all four. Replacing
the first $S_9$ witness by the identity in a temporary copy caused Magma's
intersection assertion to fail and the wrapper to exit with status 1.

To repeat the run from the repository root:

```sh
python3 computations/section3/verify.py --output /path/to/new-receipt
```

This records exact computer-algebra computations, separately from the
repository's Lean certificates and kernel-verification records.
