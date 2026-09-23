#!/usr/bin/env python3
"""Generate proposed S5/S6 finite certificates, checked entirely by Lean.

Python supplies literal permutations and candidate cardinalities. The emitted
Lean proofs reconstruct subgroup closure, Sylow orders, full sample coverage,
and the counts using kernel reduction. No generated datum is trusted as proof.
"""

from __future__ import annotations

import argparse
import tempfile
from fractions import Fraction
from itertools import permutations
from math import factorial
from pathlib import Path


def compose(a: tuple[int, ...], b: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a[i] for i in b)


def inverse(a: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a.index(i) for i in range(len(a)))


def cycle(n: int, entries: list[int]) -> tuple[int, ...]:
    a = list(range(n))
    for i, j in zip(entries, entries[1:] + entries[:1]):
        a[i] = j
    return tuple(a)


def closure(n: int, generators: list[tuple[int, ...]]) -> set[tuple[int, ...]]:
    identity = tuple(range(n))
    found = {identity}
    queue = [identity]
    for g in queue:
        for h in generators:
            x = compose(g, h)
            if x not in found:
                found.add(x)
                queue.append(x)
    return found


def good(row: set[tuple[int, ...]], x: tuple[int, ...]) -> bool:
    identity = tuple(range(len(x)))
    xi = inverse(x)
    return all(y == identity or compose(compose(xi, y), x) not in row for y in row)


def vector(a: tuple[int, ...]) -> str:
    return "![" + ", ".join(map(str, a)) + "]"


def list_expr(names: list[str], indent: int = 2) -> str:
    chunks = [", ".join(names[i:i + 10]) for i in range(0, len(names), 10)]
    return "[" + (",\n" + " " * indent).join(chunks) + "]"


def header(imports: list[str], namespace: str, title: str) -> list[str]:
    return [
        "module", "", *["public import " + name for name in imports], "",
        "/-!", "# " + title, "",
        "Generated deterministically by `SymmetricFiniteCertificates/generate.py`.",
        "Every acceptance theorem is checked by the Lean kernel.", "-/", "",
        "@[expose] public section", "", "namespace " + namespace, "",
        "set_option maxRecDepth 100000", "",
    ]


def emit(lines: list[str], path: Path) -> None:
    scoped = []
    for line in lines:
        if line.startswith(("theorem ", "private theorem ")):
            scoped.extend([
                "set_option maxHeartbeats 0 in",
                "-- Kernel reduction checks explicit permutation tables and finite count chunks.",
            ])
        scoped.append(line)
    path.write_text("\n".join(scoped))


def generate(n: int, directory: Path, three_only: bool = False) -> dict[str, object]:
    group = list(permutations(range(n)))
    ranks = {g: i for i, g in enumerate(group)}
    p2gens = [cycle(n, [0, 1]), compose(cycle(n, [0, 2]), cycle(n, [1, 3]))]
    if n == 6:
        p2gens.append(cycle(n, [4, 5]))
    p3gens = [cycle(n, [0, 1, 2])]
    if n == 6:
        p3gens.append(cycle(n, [3, 4, 5]))
    rows = {2: closure(n, p2gens), 3: closure(n, p3gens),
            5: closure(n, [cycle(n, [0, 1, 2, 3, 4])])}
    for p, row in rows.items():
        ppart, remaining = 1, factorial(n)
        while remaining % p == 0:
            ppart *= p
            remaining //= p
        assert len(row) == ppart
    bad = {p: sum(not good(row, x) for x in group) for p, row in rows.items()}
    assert sum(bad.values()) < factorial(n), (n, bad)
    if n == 5:
        assert bad[2] == 56
    if n == 6:
        assert bad == {2: 464, 3: 72, 5: 20}, bad

    prefix = f"S{n}Three" if three_only else f"S{n}"
    if three_only:
        rows = {3: rows[3]}
    ns = f"LisiSabatini.SymmetricFiniteCertificates.{prefix}"
    lines = header([
        "LisiSabatini.FiniteCertificates.PermutationTable",
        "LisiSabatini.SymmetricFiniteCertificates.ListTable",
        "Mathlib.Tactic.NormNum",
    ], ns, f"Literal full-group and Sylow tables for S{n}")
    lines += ["open LisiSabatini.FiniteCertificates", "", f"abbrev G := Equiv.Perm (Fin {n})", ""]
    if 5 in rows:
        lines += ["local instance : Fact (Nat.Prime 5) := ⟨by decide⟩", ""]
    for rank, g in enumerate(group):
        lines += [f"def e{rank} : G where", f"  toFun := {vector(g)}",
                  f"  invFun := {vector(inverse(g))}",
                  "  left_inv := by decide +kernel", "  right_inv := by decide +kernel", ""]
    chunks = [group[i:i + 24] for i in range(0, len(group), 24)]
    for i, chunk in enumerate(chunks):
        lines += [f"def chunk{i:02d} : List G :=",
                  "  " + list_expr([f"e{ranks[g]}" for g in chunk], 3), ""]
    lines += ["def elements : List G :=",
              "  " + " ++\n  ".join(f"chunk{i:02d}" for i in range(len(chunks))), "",
              "theorem elements_isChain :",
              "    elements.IsChain (fun a b ↦ permutationCode a < permutationCode b) := by",
              "  decide +kernel", "",
              "theorem elements_nodup : elements.Nodup :=",
              "  nodup_of_code_isChain permutationCode elements_isChain", "",
              "def sample : Finset G := finsetOfNodupList elements elements_nodup", "",
              f"theorem sample_card : sample.card = {factorial(n)} := by",
              "  change elements.length = _", "  decide +kernel", "",
              f"theorem group_card : Nat.card G = {factorial(n)} := by",
              "  simp only [G, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]",
              "  norm_num [Nat.factorial]", "",
              "theorem sample_eq_univ : sample = Finset.univ := by",
              "  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ sample)",
              "  rw [sample_card, Finset.card_univ, ← Nat.card_eq_fintype_card, group_card]", ""]
    for p, row in rows.items():
        names = [f"e{ranks[g]}" for g in sorted(row)]
        rowlines = [", ".join(names[i:i + 10]) for i in range(0, len(names), 10)]
        lines += [f"def row{p}Elements : List G :=",
                  "  [" + ",\n   ".join(rowlines) + "]", "",
                  f"def row{p} : Finset G := row{p}Elements.toFinset", "",
                  f"theorem row{p}_mem (x : G) : x ∈ row{p} ↔ x ∈ row{p}Elements := by",
                  f"  simp only [row{p}, List.mem_toFinset]", "",
                  f"theorem row{p}_list_closed : listSubgroupCheck row{p}Elements = true := by",
                  "  decide +kernel", "",
                  f"theorem row{p}_subgroup : subgroupCheck row{p} = true := by",
                  f"  exact listSubgroupCheck_sound row{p} row{p}Elements row{p}_mem row{p}_list_closed", "",
                  f"theorem row{p}_card : row{p}.card = {p} ^ (Nat.card G).factorization {p} := by",
                  "  rw [group_card]", "  decide +kernel", "",
                  f"noncomputable def sylow{p} : Sylow {p} G :=",
                  f"  checkedSylow row{p} row{p}_subgroup row{p}_card", ""]
    lines += ["end " + ns, ""]
    emit(lines, directory / f"{prefix}Table.lean")

    lines = header([f"LisiSabatini.SymmetricFiniteCertificates.{prefix}Table",
                    "LisiSabatini.SymmetricFiniteCertificates.ListTable"], ns,
                   f"Kernel-checked bad-conjugator counts in S{n}")
    lines += ["open LisiSabatini.FiniteCertificates", ""]
    for p, row in rows.items():
        counts = [sum(not good(row, x) for x in chunk) for chunk in chunks]
        for i, count in enumerate(counts):
            lines += [f"private theorem row{p}_bad_chunk{i:02d} :",
                      f"    listUncheckedCount row{p}Elements chunk{i:02d} = {count} := by",
                      "  decide +kernel", ""]
        lines += [f"theorem row{p}_unchecked_count :",
                  f"    listUncheckedCount row{p}Elements elements = {bad[p]} := by",
                  "  simp only [elements, listUncheckedCount_append,",
                  "    " + ",\n    ".join(f"row{p}_bad_chunk{i:02d}" for i in range(len(chunks))) + "]",
                  "", f"theorem sylow{p}_bad_card :",
                  f"    (sampleBadConjugators Finset.univ sylow{p}).card ≤ {bad[p]} := by",
                  "  rw [← sample_eq_univ]",
                  f"  exact (bad_card_le_listUncheckedCount row{p} row{p}Elements row{p}_mem",
                  f"    row{p}_subgroup row{p}_card elements elements_nodup).trans",
                  f"      (by rw [row{p}_unchecked_count])", ""]
    lines += ["end " + ns, ""]
    emit(lines, directory / f"{prefix}Counts.lean")
    return {"degree": n, "order": len(group), "row_orders": {p: len(r) for p, r in rows.items()},
            "bad_counts": bad, "total_bad_fraction": str(Fraction(sum(bad.values()), len(group)))}


def generate_witnesses(directory: Path) -> None:
    lines = header(["LisiSabatini.FiniteCertificates.TableCertificate",
                    "Mathlib.Tactic.NormNum"], "LisiSabatini.SymmetricFiniteCertificates",
                   "Small explicit Sylow-two witnesses for S5 and S6")
    lines += ["open LisiSabatini.FiniteCertificates", ""]
    for n in [5, 6]:
        gens = [cycle(n, [0, 1]), compose(cycle(n, [0, 2]), cycle(n, [1, 3]))]
        if n == 6:
            gens.append(cycle(n, [4, 5]))
        row = closure(n, gens)
        witness = next(x for x in permutations(range(n)) if good(row, x))
        lines += [f"namespace S{n}Tiny", "", f"abbrev G := Equiv.Perm (Fin {n})", ""]
        for i, g in enumerate(sorted(row)):
            lines += [f"def e{i} : G where", f"  toFun := {vector(g)}",
                      f"  invFun := {vector(inverse(g))}",
                      "  left_inv := by decide +kernel", "  right_inv := by decide +kernel", ""]
        lines += ["def row2 : Finset G :=",
                  "  {" + ", ".join(f"e{i}" for i in range(len(row))) + "}", "",
                  "theorem row2_subgroup : subgroupCheck row2 = true := by",
                  "  decide +kernel", "",
                  f"theorem row2_card : row2.card = {len(row)} := by",
                  "  decide +kernel", "",
                  f"theorem group_card : Nat.card G = {factorial(n)} := by",
                  "  simp only [G, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]",
                  "  norm_num [Nat.factorial]", "",
                  "theorem row2_card_factorization : row2.card = 2 ^ (Nat.card G).factorization 2 := by",
                  "  rw [row2_card, group_card]", "  decide +kernel", "",
                  "noncomputable def sylow2 : Sylow 2 G :=",
                  "  checkedSylow row2 row2_subgroup row2_card_factorization", "",
                  f"theorem card_sylow2 : Nat.card sylow2 = {len(row)} := by",
                  "  exact (card_checkedSubgroup row2 row2_subgroup).trans row2_card", "",
                  "def witness : G where", f"  toFun := {vector(witness)}",
                  f"  invFun := {vector(inverse(witness))}",
                  "  left_inv := by decide +kernel", "  right_inv := by decide +kernel", "",
                  "theorem witness_good : goodCheck row2 witness = true := by",
                  "  decide +kernel", "",
                  "theorem sylow2_inter_witness_eq_bot : sylowInter sylow2 witness = ⊥ := by",
                  "  exact checkedSylow_good row2 row2_subgroup row2_card_factorization witness witness_good",
                  "", f"end S{n}Tiny", ""]
        print({"degree": n, "row_order": len(row), "witness": witness})
    lines += ["end LisiSabatini.SymmetricFiniteCertificates", ""]
    (directory / "SylowTwoWitnesses.lean").write_text("\n".join(lines))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="compare all three live generated modules without modifying them")
    args = parser.parse_args()
    directory = Path(__file__).resolve().parent
    with tempfile.TemporaryDirectory(prefix="lisi-small-certificates-") as temporary:
        output = Path(temporary) if args.check else directory
        generate_witnesses(output)
        print(generate(6, output, three_only=True))
        names = ["SylowTwoWitnesses.lean", "S6ThreeTable.lean", "S6ThreeCounts.lean"]
        if args.check:
            mismatches = [name for name in names
                          if not (directory / name).exists()
                          or (directory / name).read_bytes() != (output / name).read_bytes()]
            if mismatches:
                raise SystemExit("Generated source mismatch: " + ", ".join(mismatches))
        print("PASS: 3 live S5/S6 certificate modules")


if __name__ == "__main__":
    main()
