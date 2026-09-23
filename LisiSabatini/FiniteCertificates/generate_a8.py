#!/usr/bin/env python3
"""Generate the four explicit subgroup rows used by the A8 certificate.

Only standard-library Python is required. These are candidate literals;
Lean checks the permutation identities, subgroup closure and Sylow orders.
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

GENERATORS = {
    2: [(2, 3, 0, 1, 4, 5, 6, 7), (4, 5, 6, 7, 0, 1, 2, 3),
        (3, 2, 1, 0, 4, 5, 6, 7), (5, 4, 6, 7, 1, 0, 2, 3)],
    3: [(1, 2, 0, 3, 4, 5, 6, 7), (0, 1, 2, 4, 5, 3, 6, 7)],
    5: [(1, 2, 3, 4, 0, 5, 6, 7)],
    7: [(1, 2, 3, 4, 5, 6, 0, 7)],
}


def document():
    rows = []
    identity = tuple(range(8))
    for prime, generators in GENERATORS.items():
        found = {identity}
        pending = [identity]
        for a in pending:
            for b in generators:
                c = tuple(a[b[i]] for i in range(8))
                if c not in found:
                    found.add(c)
                    pending.append(c)
        elements = sorted(found)
        order, remaining = 1, 20160
        while remaining % prime == 0:
            order *= prime
            remaining //= prime
        assert len(elements) == order
        assert all(sum(a[i] > a[j] for i in range(8) for j in range(i + 1, 8)) % 2 == 0
                   for a in elements)
        assert all(tuple(a[b[i]] for i in range(8)) in found
                   for a in elements for b in elements)
        assert all(tuple(a.index(i) for i in range(8)) in found for a in elements)
        rows.append({"prime": prime, "order": order,
                     "generators": [list(g) for g in generators],
                     "elements": [{"images": list(g)} for g in elements]})
    return {"format": "a8-sylow-rows-v1", "degree": 8,
            "multiplication": "(a*b)(i)=a(b(i))", "rows": rows}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    path = Path(__file__).with_name("A8Data.json")
    text = json.dumps(document(), indent=2) + "\n"
    if args.check:
        if path.read_text() != text:
            raise SystemExit("A8Data.json does not match deterministic generation")
    else:
        path.write_text(text)
    print("PASS: A8 subgroup rows of orders 64, 9, 5, 7")


if __name__ == "__main__":
    main()
