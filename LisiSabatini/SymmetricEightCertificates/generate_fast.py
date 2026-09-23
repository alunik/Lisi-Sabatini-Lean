#!/usr/bin/env python3
"""Propose a 511-product generator-and-spanning-tree certificate for P8.

Read the frozen sorted subgroup row from Data.json. Emit only new Fast* files;
the original multiplication-table certificates are never modified. Python is
a certificate generator, not a trusted verifier: all acceptance proofs use
Lean's kernel reduction.
"""

from __future__ import annotations

import argparse
from collections import deque
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
NS = "LisiSabatini.SymmetricEightCertificates.FastData"
MODULE = "LisiSabatini.SymmetricEightCertificates"


def mul(a, b):
    return tuple(a[b[i]] for i in range(8))


def document():
    source = ROOT / "Data.json"
    rows = [tuple(x) for x in json.loads(source.read_text())["row"]]
    lookup = {g: i for i, g in enumerate(rows)}
    generators = [(1, 0, 2, 3, 4, 5, 6, 7),
                  (2, 3, 0, 1, 4, 5, 6, 7),
                  (4, 5, 6, 7, 0, 1, 2, 3)]
    assert rows[0] == tuple(range(8)) and len(lookup) == 128
    assert all(mul(g, g) == rows[0] for g in generators)
    actions = [[lookup[mul(g, h)] for h in rows] for g in generators]
    order, parents, edge_generators = [0], [0], [0]
    positions = {0: 0}
    queue = deque([0])
    while queue:
        parent = queue.popleft()
        for j, action in enumerate(actions):
            child = action[order[parent]]
            if child not in positions:
                positions[child] = len(order)
                queue.append(len(order))
                order.append(child)
                parents.append(parent)
                edge_generators.append(j)
    assert len(order) == 128
    inverse = [positions[i] for i in range(128)]
    for k in range(1, 128):
        assert parents[k] < k
        assert rows[order[k]] == mul(generators[edge_generators[k]], rows[order[parents[k]]])
    return {"format": "s8-generator-spanning-v1", "source_data_sha256": hashlib.sha256(
                source.read_bytes()).hexdigest(), "generators": generators,
            "generator_row_indices": [lookup[g] for g in generators],
            "action_indices": actions, "bfs_order": order, "bfs_inverse": inverse,
            "bfs_parents": parents, "bfs_generators": edge_generators,
            "product_checks": 3 * 128 + 127}


def array(values, prefix="#["):
    values = list(map(str, values))
    return prefix + ",\n   ".join(
        ", ".join(values[i:i + 16]) for i in range(0, len(values), 16)) + "]"


def header(imports, *, install_decidable_eq=False):
    lines = ["module", "", *["public import " + x for x in imports], "",
            "/-! Generated generator-closure and spanning-tree certificate data. -/", "",
            "@[expose] public section", "", "namespace " + NS, "",
            "open LisiSabatini.FiniteCertificates", "",
            "set_option maxRecDepth 100000", ""]
    if install_decidable_eq:
        lines += [
            "/- Install before defining the Boolean checks: the decider is captured there. -/",
            "local instance : DecidableEq G := permutationCodeDecidableEq_fin8", ""]
    return lines


def kernel_lemma(lines):
    return ["set_option maxHeartbeats 0 in",
            "/- This certificate proof unfolds finite checks; scope its elaboration budget here. -/",
            *lines]


def finish(lines):
    return "\n".join(lines + ["end " + NS, ""])


def data_lean(data):
    lines = header([MODULE + ".Table"], install_decidable_eq=True)
    lines += ["/-- The involutions `(01)`, `(02)(13)`, and `(04)(15)(26)(37)`. -/",
              "def genAt : Fin 3 → G :=",
              "  " + array(["p" + str(i) for i in data["generator_row_indices"]], prefix="!["), ""]
    lines += kernel_lemma([
        "theorem gen_involutive : ∀ j : Fin 3, (genAt j)⁻¹ = genAt j := by",
        "  decide +kernel", ""])
    lines += kernel_lemma(["theorem rowAt_zero : rowAt 0 = 1 := by decide +kernel", ""])
    for j, action in enumerate(data["action_indices"]):
        lines += [f"def actionIndices{j} : Array (Fin 128) :=", "  " + array(action), ""]
    lines += ["def actionIndices : Fin 3 → Array (Fin 128) :=",
              "  ![actionIndices0, actionIndices1, actionIndices2]", "",
              "theorem actionIndices_size (j : Fin 3) : (actionIndices j).size = 128 := by",
              "  fin_cases j <;> rfl", "",
              "def actionIndex (j : Fin 3) (i : Fin 128) : Fin 128 :=",
              "  (actionIndices j)[i.val]'(by rw [actionIndices_size]; exact i.isLt)", ""]
    for name, key, bound in [("bfsAt", "bfs_order", 128), ("bfsInverse", "bfs_inverse", 128),
                             ("bfsParent", "bfs_parents", 128), ("bfsGen", "bfs_generators", 3)]:
        lines += [f"def {name}Data : Array (Fin {bound}) :=", "  " + array(data[key]), "",
                  f"def {name} (k : Fin 128) : Fin {bound} :=",
                  f"  {name}Data[k.val]'(by change k.val < 128; exact k.isLt)", ""]
    lines += kernel_lemma(["theorem bfsAt_zero : bfsAt 0 = 0 := by decide +kernel", ""])
    lines += kernel_lemma([
        "theorem bfs_cover : ∀ i : Fin 128, bfsAt (bfsInverse i) = i := by",
        "  decide +kernel", ""])
    lines += ["theorem bfsAt_surjective : Function.Surjective bfsAt :=",
              "  fun i ↦ ⟨bfsInverse i, bfs_cover i⟩", ""]
    lines += kernel_lemma([
        "theorem bfs_parent_lt : ∀ k : Fin 128, 0 < k → bfsParent k < k := by",
        "  decide +kernel", ""])
    lines += [
              "/-- Exactly 128 left-generator products, with no ambient-group enumeration. -/",
              "def actionCheck (j : Fin 3) : Bool :=",
              "  decide (∀ i : Fin 128, genAt j * rowAt i = rowAt (actionIndex j i))", "",
              "/-- One product per nonroot node of the spanning tree. -/",
              "def bfsEdgeCheck : Bool :=",
              "  decide (∀ k : Fin 128, 0 < k →",
              "    rowAt (bfsAt k) = genAt (bfsGen k) * rowAt (bfsAt (bfsParent k)))", ""]
    return finish(lines)


def action_lean(j):
    return finish(header([MODULE + ".FastData"]) + kernel_lemma([
        f"theorem actionCheck_{j} : actionCheck {j} = true := by", "  decide +kernel", ""]))


def bfs_lean():
    return finish(header([MODULE + ".FastData"]) + kernel_lemma([
        "theorem bfsEdgeCheck_checked : bfsEdgeCheck = true := by", "  decide +kernel", ""]))


def checks_lean():
    return finish(header([MODULE + f".FastChecks.Action{j}" for j in range(3)] +
                         [MODULE + ".FastChecks.Spanning"]) + [
        "/- Match the equality decider already captured in the imported Boolean checks. -/",
        "local instance fastChecksDecidableEqG : DecidableEq G := permutationCodeDecidableEq_fin8",
        ""] + kernel_lemma([
        "theorem action_checked : ∀ j : Fin 3, ∀ i : Fin 128,",
        "    genAt j * rowAt i = rowAt (actionIndex j i) := by",
        "  intro j",
        "  have h : actionCheck j = true := by",
        "    fin_cases j",
        "    · exact actionCheck_0",
        "    · exact actionCheck_1",
        "    · exact actionCheck_2",
        "  exact of_decide_eq_true h", ""]) + kernel_lemma([
        "theorem bfs_edge_checked : ∀ k : Fin 128, 0 < k →",
        "    rowAt (bfsAt k) = genAt (bfsGen k) * rowAt (bfsAt (bfsParent k)) :=",
        "  of_decide_eq_true bfsEdgeCheck_checked", ""]))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    data = document()
    outputs = {"FastData.json": json.dumps(data, indent=2) + "\n",
               "FastData.lean": data_lean(data), "FastChecks.lean": checks_lean(),
               "FastChecks/Spanning.lean": bfs_lean()}
    for j in range(3):
        outputs[f"FastChecks/Action{j}.lean"] = action_lean(j)
    for name, content in outputs.items():
        path = ROOT / name
        if args.check:
            assert path.read_text() == content, name
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(content)
    print(json.dumps({"files": len(outputs), "products": data["product_checks"],
                      "generator_row_indices": data["generator_row_indices"],
                      "source_data_sha256": data["source_data_sha256"],
                      "fast_data_sha256": hashlib.sha256(outputs["FastData.json"].encode()).hexdigest()},
                     sort_keys=True))


if __name__ == "__main__":
    main()
