#!/usr/bin/env python3
"""Generate the P128 table used by the symmetric-group certificates.

The carrier consists of all binary-tree automorphisms on eight leaves. The
transversal consists of lexicographically first representatives of sets r P.
No generated Python assertion is used as a Lean proof.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NS = "LisiSabatini.SymmetricEightCertificates"


def mul(a, b):
    return tuple(a[b[i]] for i in range(8))


def inv(a):
    return tuple(a.index(i) for i in range(8))


def tree(a):
    return all(a[i] // 2 == a[i + 1] // 2 for i in (0, 2, 4, 6)) and all(
        a[i] // 4 == a[i + 2] // 4 for i in (0, 4))


def document():
    all_perms = list(itertools.permutations(range(8)))
    row = [g for g in all_perms if tree(g)]
    assert len(row) == 128 and row[0] == tuple(range(8))
    lookup = {g: i for i, g in enumerate(row)}
    inverse_indices = [lookup[inv(g)] for g in row]
    products = [lookup[mul(g, h)] for g in row for h in row]
    remaining = set(all_perms)
    reps = []
    for g in all_perms:
        if g in remaining:
            reps.append(g)
            remaining.difference_update(mul(g, h) for h in row)
    assert len(reps) == 315 and not remaining
    assert all(not tree(mul(inv(g), h)) for i, g in enumerate(reps)
               for h in reps[i + 1:])
    witnesses = []
    sizes = []
    for g in reps:
        intersection = [(i, lookup[mul(mul(inv(g), h), g)])
                        for i, h in enumerate(row)
                        if mul(mul(inv(g), h), g) in lookup]
        assert len(intersection) >= 2
        witnesses.append(next((a, b) for a, b in intersection if a != 0))
        sizes.append(len(intersection))
    chosen = sizes.index(2)
    return {"format": "s8-right-cosets-v1", "multiplication": "(a*b)(i)=a(b(i))",
            "row": row, "inverse_indices": inverse_indices, "product_indices": products,
            "representatives": reps, "witnesses": witnesses, "intersection_sizes": sizes,
            "chosen_representative": chosen, "chosen_witness": witnesses[chosen][0]}


def arr(values, width=16, prefix="#["):
    values = list(map(str, values))
    return prefix + ",\n   ".join(
        ", ".join(values[i:i + width]) for i in range(0, len(values), width)) + "]"


def header(imports, *, unbounded=True):
    return ["module", "", *["public import " + x for x in imports], "",
            "/-! Generated candidate data with kernel-checked acceptance proofs. -/", "",
            "@[expose] public section", "", "namespace " + NS, "",
            "open LisiSabatini.FiniteCertificates", "",
            "set_option maxRecDepth 100000",
            *(["set_option maxHeartbeats 0"] if unbounded else []), ""]


def finish(lines):
    return "\n".join(lines + ["end " + NS, ""])


def table(data):
    lines = header(["LisiSabatini.FiniteCertificates.IndexedTable"], unbounded=False)
    lines += ["abbrev G := Equiv.Perm (Fin 8)", "",
              "local instance : DecidableEq G := permutationCodeDecidableEq_fin8", "",
              "/-- A necessary condition for membership in the tree automorphism group. -/",
              "def treeCheck (g : G) : Bool :=",
              "  decide ((g 0).val / 2 = (g 1).val / 2 ∧",
              "    (g 2).val / 2 = (g 3).val / 2 ∧",
              "    (g 4).val / 2 = (g 5).val / 2 ∧",
              "    (g 6).val / 2 = (g 7).val / 2 ∧",
              "    (g 0).val / 4 = (g 2).val / 4 ∧",
              "    (g 4).val / 4 = (g 6).val / 4)", ""]
    for prefix, items in [("p", data["row"]), ("r", data["representatives"])]:
        for i, g in enumerate(items):
            lines += [f"def {prefix}{i} : G where",
                      "  toFun := " + arr(g, prefix="!["),
                      "  invFun := " + arr(inv(g), prefix="!["),
                      "  left_inv := by decide +kernel",
                      "  right_inv := by decide +kernel", ""]
    lines += ["def rowElements : List G :=",
              "  " + arr(["p" + str(i) for i in range(128)], prefix="["), "",
              "def rowArray : Array G := rowElements.toArray", "",
              "def rowAt (i : Fin 128) : G :=",
              "  rowArray[i.val]'(by change i.val < 128; exact i.isLt)", "",
              "theorem rowElements_nodup : rowElements.Nodup :=",
              "  nodup_of_code_isChain permutationCode (by decide +kernel)", "",
              "def row : Finset G := finsetOfNodupList rowElements rowElements_nodup", "",
              "theorem row_card : row.card = 128 := rfl", "",
              "theorem mem_row_iff (g : G) : g ∈ row ↔ ∃ i : Fin 128, rowAt i = g := by",
              "  change g ∈ rowElements ↔ ∃ i : Fin rowElements.length, rowElements[i] = g",
              "  exact List.mem_iff_get", "",
              "theorem rowAt_mem (i : Fin 128) : rowAt i ∈ row :=",
              "  (mem_row_iff _).mpr ⟨i, rfl⟩", "",
              "def representatives : Array G :=",
              "  " + arr(["r" + str(i) for i in range(315)]), "",
              "def repAt (i : Fin 315) : G :=",
              "  representatives[i.val]'(by change i.val < 315; exact i.isLt)", ""]
    for name, values, size, codomain in [
            ("inverseIndex", data["inverse_indices"], 128, 128),
            ("productIndex", data["product_indices"], 16384, 128),
            ("witnessA", [a for a, _ in data["witnesses"]], 315, 128),
            ("witnessB", [b for _, b in data["witnesses"]], 315, 128)]:
        if name == "productIndex":
            for shard_i in range(16):
                lines += [f"def productIndexBlock{shard_i:02d} : Array (Fin 128) :=",
                          "  " + arr(values[shard_i * 1024:(shard_i + 1) * 1024]), ""]
            lines += ["def productIndexBlocks : Fin 16 → Array (Fin 128) :=",
                      "  " + arr([f"productIndexBlock{i:02d}" for i in range(16)], width=4, prefix="!["), "",
                      "theorem productIndexBlocks_size (s : Fin 16) :",
                      "    (productIndexBlocks s).size = 1024 := by",
                      "  fin_cases s <;> rfl", "",
                      "def productIndex (i j : Fin 128) : Fin 128 :=",
                      "  (productIndexBlocks ⟨i.val / 8, by omega⟩)[(i.val % 8) * 128 + j.val]'(by",
                      "    rw [productIndexBlocks_size]",
                      "    have hj := j.isLt; have hi := Nat.mod_lt i.val (by decide : 0 < 8)",
                      "    omega)", ""]
        else:
            lines += [f"def {name}Data : Array (Fin {codomain}) :=", "  " + arr(values), "",
                      f"def {name} (i : Fin {size}) : Fin {codomain} :=",
                      f"  {name}Data[i.val]'(by change i.val < {size}; exact i.isLt)", ""]
    lines += [f"def chosenRep : Fin 315 := {data['chosen_representative']}", "",
              f"def chosenWitness : Fin 128 := {data['chosen_witness']}", "",
              "/-- Eight-row closure check, leaving the table data shared by all shards. -/",
              "def closureCheck (s : Fin 16) : Bool :=",
              "  decide (∀ k : Fin 8, let i : Fin 128 := ⟨s.val * 8 + k.val, by omega⟩;",
              "    rowAt (inverseIndex i) = (rowAt i)⁻¹ ∧",
              "    ∀ j : Fin 128, rowAt (productIndex i j) = rowAt i * rowAt j)", "",
              "/-- Fifteen rows of pairwise distinctness tests for the right cosets. -/",
              "def separationCheck (s : Fin 21) : Bool :=",
              "  decide (∀ k : Fin 15, let i : Fin 315 := ⟨s.val * 15 + k.val, by omega⟩;",
              "    ∀ j : Fin 315, i < j → treeCheck ((repAt i)⁻¹ * repAt j) = false)", ""]
    return finish(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = document()
    outputs = {"Data.json": json.dumps(data, indent=2) + "\n", "Table.lean": table(data)}
    for path, content in outputs.items():
        destination = ROOT / path
        if args.check:
            assert destination.read_text() == content, path
        else:
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content)
    print(json.dumps({"files": len(outputs),
                      "group_order": 40320, "row_order": 128,
                      "right_cosets": 315, "pair_tests": 315 * 314 // 2,
                      "chosen_representative": data["chosen_representative"],
                      "chosen_intersection_size": 2,
                      "data_sha256": hashlib.sha256(outputs["Data.json"].encode()).hexdigest()},
                     sort_keys=True))


if __name__ == "__main__":
    main()
