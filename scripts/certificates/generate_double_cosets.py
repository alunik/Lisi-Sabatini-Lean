#!/usr/bin/env python3
"""Generate literal failed-block witnesses, never acceptance claims from Python.

Every output proof uses Lean's kernel evaluator. Search inputs are independently
replayed and canonical row order is the certified P8 row times the literal tail.
"""
from pathlib import Path
import argparse
import itertools
import json
import textwrap
import tempfile

ROOT = Path(__file__).resolve().parents[2]
DESTINATION_ROOT = ROOT
TAILS = {
    9: [(0,)],
    10: [(0, 1), (1, 0)],
    12: [(0, 1, 2, 3), (0, 1, 3, 2), (1, 0, 2, 3), (1, 0, 3, 2),
         (2, 3, 0, 1), (2, 3, 1, 0), (3, 2, 0, 1), (3, 2, 1, 0)],
}


def inverse(g):
    ans = [0] * len(g)
    for a, b in enumerate(g):
        ans[b] = a
    return ans


def lean_vector(xs):
    return '![' + ', '.join(map(str, xs)) + ']'


def lean_array(xs):
    return '#[' + ', '.join(map(str, xs)) + ']'


def write_generated(path, text):
    """Keep generated literals readable and use the normal heartbeat budget."""
    text = text.replace('set_option maxHeartbeats 0\n', '')
    lines = []
    for line in text.splitlines():
        indent = line[:len(line) - len(line.lstrip())]
        lines.extend(textwrap.wrap(line, width=98, subsequent_indent=indent + '  ',
                                   break_long_words=False, break_on_hyphens=False) or [''])
    path.write_text('\n'.join(lines) + '\n')


def preamble(n, imports):
    return ('module\n\n' + ''.join(f'public import {x}\n' for x in imports) +
            '\n/-! Generated literal witnesses; every acceptance is kernel checked. -/\n\n'
            '@[expose] public section\n\n'
            f'namespace LisiSabatini.SymmetricDoubleCosetCertificates.S{n}\n\n'
            'open LisiSabatini.FiniteCertificates LisiSabatini.SymmetricDoubleCosetRows\n\n'
            'set_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\n')


def closing(n):
    return f'\nend LisiSabatini.SymmetricDoubleCosetCertificates.S{n}\n'


def indexed_array(name, xs, size):
    return (f'def {name}Array : Array (Fin {size}) :=\n  {lean_array(xs)}\n\n'
            f'def {name} (i : Fin {len(xs)}) : Fin {size} :=\n'
            f'  {name}Array[i.val]\'(by change i.val < {len(xs)}; exact i.isLt)\n\n')


def emit_chunked(n, out, module, size, step, pred, expr, theorem, goal,
                 extra='', suffix=''):
    """Stored proof chunks avoid long kernel reduction chains and replay."""
    data_module = f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.{module}Data'
    data = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Data',
                       'LisiSabatini.SymmetricDoubleCosetChunkCheck'])
    data += extra + f'def {pred} (i : Fin {size}) : Bool :=\n  {expr}\n'
    write_generated(out / f'{module}Data.lean', data + closing(n))
    chunks = []
    for k, start in enumerate(range(0, size, step)):
        name = f'{pred}Chunk{k:02}'
        chunks.append(name)
        text = preamble(n, [data_module])
        text += (f'def {name}Indices : List (Fin {size}) :=\n  '
                 + str(list(range(start, min(start + step, size)))) + '\n\n'
                 f'theorem {name}Checked : {name}Indices.all {pred} = true := by\n'
                 '  decide +kernel\n')
        write_generated(out / f'{module}Chunk{k:02}.lean', text + closing(n))
    text = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.{module}Chunk{k:02}'
                        for k in range(len(chunks))])
    text += (f'def {pred}Chunks : List (IndexedBooleanCheckChunk {pred}) :=\n  ['
             + ',\n   '.join(f'⟨{c}Indices, {c}Checked⟩' for c in chunks) + ']\n\n'
             f'theorem {theorem} : {goal} = true := by\n'
             '  exact all_finRange_of_checked_chunks\n'
             f'    {pred} {pred}Chunks (by decide +kernel)\n'
             + suffix)
    write_generated(out / f'{module}.lean', text + closing(n))


def generate(n, benchmark=False):
    p8 = json.loads((ROOT / 'LisiSabatini/SymmetricEightCertificates/Data.json').read_text())['row']
    inp = json.loads((ROOT / f'data/certificates/S{n}.json').read_text())
    reps = inp['representatives']
    rows = [list(a) + [8 + x for x in b] for a in p8 for b in TAILS[n]]
    assert rows[0] == list(range(n))
    comps = [(a, a + w // 2, w) for w in (2, 4, 8)
             for a in range(0, n - w + 1, w)]
    assert all(g[a] // w == g[b] // w for g in rows for a, b, w in comps)
    out = DESTINATION_ROOT / f'LisiSabatini/SymmetricDoubleCosetCertificates/S{n}'
    out.mkdir(parents=True, exist_ok=True)
    for old in out.glob('Sep*.lean'):
        old.unlink()
    involutions = [i for i, a in enumerate(rows) if i != 0 and
                   all(a[a[x]] == x for x in range(n))]
    data = preamble(n, ['LisiSabatini.SymmetricDoubleCosetRows',
                         'LisiSabatini.SymmetricEightTreeCheck',
                         'LisiSabatini.SymmetricDoubleCosetInvolutionCheck'])
    for i, g in enumerate(reps):
        data += (f'def rep{i} : Equiv.Perm (Fin {n}) where\n'
                 f'  toFun := {lean_vector(g)}\n'
                 f'  invFun := {lean_vector(inverse(g))}\n'
                 '  left_inv := by decide +kernel\n'
                 '  right_inv := by decide +kernel\n\n')
    data += (f'def repsArray : Array (Equiv.Perm (Fin {n})) :=\n  '
             + lean_array([f'rep{i}' for i in range(len(reps))]) + '\n\n'
             f'def reps (i : Fin {len(reps)}) : Equiv.Perm (Fin {n}) :=\n'
             f'  repsArray[i.val]\'(by change i.val < {len(reps)}; exact i.isLt)\n\n'
             f'def comparisons : Array (PermutationBlockComparison {n}) :=\n  '
             + lean_array([f'⟨{a}, {b}, {w}⟩' for a, b, w in comps]) + '\n\n'
             f'def tests (i : Fin {len(comps)}) (g : Equiv.Perm (Fin {n})) : Bool :=\n'
             '  blockComparisonCheck (comparisons[i.val]\'(by exact i.isLt)) g\n\n'
             f'def involutionIndices : List (Fin {len(rows)}) :=\n  '
             + str(involutions) + '\n')
    write_generated(out / 'Data.lean', data + closing(n))

    def witnesses(g, h, good=False):
        gi = inverse(g)
        ws = []
        for k, a in enumerate(rows):
            if good and k == 0:
                ws.append(0)
                continue
            cand = [gi[a[h[x]]] for x in range(n)]
            ws.append(next(j for j, (x, y, w) in enumerate(comps)
                           if cand[x] // w != cand[y] // w))
        return ws

    pairs = inp['ambiguous_pairs']
    if benchmark:
        pairs = pairs[:1]
    for pair_id, (i, j) in enumerate(pairs):
        text = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Data'])
        name = f'sepWitness_{i}_{j}'
        text += indexed_array(name, witnesses(reps[i], reps[j]), len(comps))
        text += (f'theorem separation_{i}_{j} :\n'
                 f'    doubleCosetSeparationCheck row{n} tests {name} (reps {i}) (reps {j}) = true := by\n'
                 '  decide +kernel\n')
        write_generated(out / f'Sep{pair_id:03}.lean', text + closing(n))
        if len(rows) > 128:
            emit_chunked(n, out, f'Sep{pair_id:03}', len(rows), 128,
                f'sepPredicate_{i}_{j}',
                f'!(tests ({name} i) ((reps {i})⁻¹ * row{n} i * reps {j}))',
                f'separation_{i}_{j}',
                f'doubleCosetSeparationCheck row{n} tests {name} (reps {i}) (reps {j})',
                extra=indexed_array(name, witnesses(reps[i], reps[j]), len(comps)))
    if not benchmark:
        for i, g in enumerate(reps):
            text = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Data'])
            name = f'goodWitness_{i}'
            text += indexed_array(name, witnesses(g, g, good=True), len(comps))
            text += (f'theorem good_{i} :\n'
                     f'    doubleCosetInvolutionGoodCheck row{n} involutionIndices tests {name} (reps {i}) = true := by\n'
                     '  decide +kernel\n')
            write_generated(out / f'Good{i:02}.lean', text + closing(n))
        text = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Data'])
        text += (f'theorem necessary : doubleCosetNecessaryCheck row{n} tests = true := by\n'
                 '  decide +kernel\n\n'
                 f'theorem row_zero : row{n} 0 = 1 := by\n  decide +kernel\n')
        write_generated(out / 'Necessary.lean', text + closing(n))
        text = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Data'])
        text += (f'theorem involutions_complete :\n'
                 f'    doubleCosetInvolutionIndicesCheck row{n} 0 involutionIndices = true := by\n'
                 '  decide +kernel\n')
        write_generated(out / 'Involutions.lean', text + closing(n))
        emit_chunked(n, out, 'Necessary', len(rows), 32, 'necessaryPredicate',
            f'(List.finRange {len(comps)}).all (fun j ↦ tests j (row{n} i))',
            'necessary', f'doubleCosetNecessaryCheck row{n} tests',
            suffix=f'\ntheorem row_zero : row{n} 0 = 1 := by\n  decide +kernel\n')
        emit_chunked(n, out, 'Involutions', len(rows), 32, 'involutionPredicate',
            f'if i = 0 then true else if row{n} i * row{n} i = 1 then decide (i ∈ involutionIndices) else true',
            'involutions_complete', f'doubleCosetInvolutionIndicesCheck row{n} 0 involutionIndices')

        text = preamble(n, ['LisiSabatini.SymmetricDoubleCosetCertificateAssembly'] +
            [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Good{i:02}'
             for i in range(len(reps))])
        text += (f'def goodCertificates : List (DoubleCosetInvolutionGoodCertificate row{n} involutionIndices tests reps) :=\n  ['
                 + ',\n   '.join(f'⟨{i}, goodWitness_{i}, good_{i}⟩' for i in range(len(reps)))
                 + ']\n\n'
                 'theorem goodCertificates_indices :\n'
                 f'    goodCertificates.map (fun c ↦ c.index) = List.finRange {len(reps)} := by\n'
                 '  decide +kernel\n')
        write_generated(out / 'AllGood.lean', text + closing(n))

        centers = (['z9'] if n == 9 else
                   [f'z{n}Left', f'z{n}Right', f'z{n}Both'])
        features = inp['central_features']
        text = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Data',
                           'LisiSabatini.SymmetricDoubleCosetCentralRows',
                           'LisiSabatini.SymmetricDoubleCosetCentralInvariant'])
        text += 'open LisiSabatini.SymmetricDoubleCosetCentralRows\n\n'
        text += (f'def features : List (CentralFixedPowerFeature {n}) :=\n  [' +
                 ', '.join(f'({centers[a]}, {centers[b]}, {k})' for a, b, k in features) + ']\n\n'
                 'def signatureArray : Array (List ℕ) :=\n  ' +
                 lean_array([str(s) for s in inp['central_signatures']]) + '\n\n'
                 f'def signatureAt (i : Fin {len(reps)}) : List ℕ :=\n'
                 f'  signatureArray[i.val]\'(by change i.val < {len(reps)}; exact i.isLt)\n\n'
                 'theorem signatures_checked :\n'
                 f'    (List.finRange {len(reps)}).all (fun i ↦\n'
                 '      decide (centralFixedPowerSignature features (reps i) = signatureAt i)) = true := by\n'
                 '  decide +kernel\n\n'
                 f'theorem signature_eq (i : Fin {len(reps)}) :\n'
                 '    centralFixedPowerSignature features (reps i) = signatureAt i := by\n'
                 '  exact of_decide_eq_true (List.all_eq_true.mp signatures_checked i (by simp))\n\n'
                 f'def shortcut (i j : Fin {len(reps)}) : Bool := decide (signatureAt i ≠ signatureAt j)\n')
        write_generated(out / 'Signatures.lean', text + closing(n))

        text = preamble(n, ['LisiSabatini.SymmetricDoubleCosetFallbackAssembly',
                           f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Signatures'] +
            [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.Sep{k:03}'
             for k in range(len(pairs))])
        text += (f'def pairCertificates : List (DoubleCosetPairCertificate row{n} tests reps) :=\n  ['
                 + ',\n   '.join(f'⟨({i}, {j}), sepWitness_{i}_{j}, separation_{i}_{j}⟩' for i, j in pairs)
                 + ']\n\n'
                 'theorem pairCertificates_indices :\n'
                 f'    doubleCosetPairCertificateIndices [pairCertificates] =\n'
                 f'      (doubleCosetOrderedPairs {len(reps)}).filter (fun ij ↦ !(shortcut ij.1 ij.2)) := by\n'
                 '  decide +kernel\n')
        write_generated(out / 'AllPairs.lean', text + closing(n))

        text = preamble(n, [f'LisiSabatini.SymmetricDoubleCosetCertificates.S{n}.{part}'
            for part in ('Necessary', 'Involutions', 'AllGood', 'AllPairs')] +
            ['LisiSabatini.SymmetricDoubleCosetGroupRows'])
        text += 'open LisiSabatini.SymmetricDoubleCosetCentralRows\n\n'
        text += (f'theorem necessary_on_sylow :\n'
                 f'    ∀ a ∈ (sylow{n} : Subgroup (Equiv.Perm (Fin {n}))), ∀ j, tests j a = true := by\n'
                 f'  apply doubleCosetNecessaryCheck_sound (sylow{n} : Subgroup _) row{n} tests\n'
                 f'  · intro a ha; exact (mem_sylow{n}_iff_row a).mp ha\n'
                 '  · exact necessary\n\n'
                 f'theorem all_good : ∀ i, mixedSylowInter sylow{n} sylow{n} (reps i) = ⊥ := by\n'
                 f'  apply doubleCosetInvolutionGoodCertificates_sound sylow{n} row{n} 0\n'
                 f'    (fun a ha ↦ (mem_sylow{n}_iff_row a).mp ha) row_zero involutionIndices\n'
                 '    involutions_complete tests necessary_on_sylow reps [goodCertificates]\n'
                 '  simpa [doubleCosetInvolutionGoodCertificateIndices] using goodCertificates_indices\n\n')
        for name in centers:
            text += (f'theorem {name}_central : {name} ∈\n'
                     f'    Subgroup.centralizer (sylow{n} : Set (Equiv.Perm (Fin {n}))) :=\n'
                     f'  mem_centralizer_of_row_commute (sylow{n} : Subgroup _) row{n}\n'
                     f'    mem_sylow{n}_iff_row {name} commute_{name}_row\n\n')
        text += (f'theorem features_central : ∀ f ∈ features,\n'
                 f'    f.1 ∈ Subgroup.centralizer (sylow{n} : Set (Equiv.Perm (Fin {n}))) ∧\n'
                 f'    f.2.1 ∈ Subgroup.centralizer (sylow{n} : Set _) := by\n'
                 '  intro f hf\n'
                 '  simp only [features, List.mem_cons, List.not_mem_nil, or_false] at hf\n'
                 '  rcases hf with ' + ' | '.join('rfl' for _ in features) + '\n')
        text += ''.join(f'  · exact ⟨{centers[a]}_central, {centers[b]}_central⟩\n' for a, b, _ in features)
        text += (f'\ntheorem shortcut_sound : ∀ i j, shortcut i j = true →\n'
                 f'    ∀ a ∈ (sylow{n} : Subgroup (Equiv.Perm (Fin {n}))),\n'
                 f'      (reps i)⁻¹ * a * reps j ∉ (sylow{n} : Subgroup _) := by\n'
                 '  intro i j hij\n'
                 f'  apply doubleCoset_separated_of_centralFixedPowerSignature_ne\n'
                 f'    (sylow{n} : Subgroup _) (sylow{n} : Subgroup _) features features_central\n'
                 '  rw [signature_eq, signature_eq]\n'
                 '  exact of_decide_eq_true hij\n\n'
                 f'theorem all_separated : ∀ i j, i ≠ j →\n'
                 f'    ∀ a ∈ (sylow{n} : Subgroup (Equiv.Perm (Fin {n}))),\n'
                 f'      (reps i)⁻¹ * a * reps j ∉ (sylow{n} : Subgroup _) := by\n'
                 f'  apply doubleCosetPairCertificates_sound_of_shortcut (sylow{n} : Subgroup _) row{n}\n'
                 f'    (fun a ha ↦ (mem_sylow{n}_iff_row a).mp ha) tests necessary_on_sylow\n'
                 '    reps shortcut shortcut_sound [pairCertificates] pairCertificates_indices\n')
        write_generated(out / 'Certificate.lean', text + closing(n))
    return {'degree': n, 'row_order': len(rows), 'representatives': len(reps),
            'comparisons': len(comps), 'separation_pairs_generated': len(pairs)}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
                        help='compare all generated modules without modifying checked sources')
    parser.add_argument('--degree', type=int, choices=(9, 10, 12), nargs='+', default=[9, 10, 12])
    parser.add_argument('--output-root', type=Path, default=ROOT,
                        help='write generated modules to a separate repository-shaped directory')
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix='lisi-double-cosets-') as temporary:
        DESTINATION_ROOT = Path(temporary) if args.check else args.output_root.resolve()
        results = [generate(n) for n in args.degree]
        if args.check:
            generated = sorted(DESTINATION_ROOT.rglob('*.lean'))
            mismatches = []
            for path in generated:
                relative = path.relative_to(DESTINATION_ROOT)
                current = ROOT / relative
                if not current.exists() or current.read_bytes() != path.read_bytes():
                    mismatches.append(str(relative))
            for n in args.degree:
                relative = Path(f'LisiSabatini/SymmetricDoubleCosetCertificates/S{n}')
                expected = {p.name for p in (DESTINATION_ROOT / relative).glob('*.lean')}
                actual = {p.name for p in (ROOT / relative).glob('*.lean')}
                mismatches += [str(relative / name) for name in sorted(actual - expected)]
            if mismatches:
                raise SystemExit('Generated source mismatch: ' + ', '.join(mismatches))
            print(f'PASS: {len(generated)} exact generated Lean modules')
        print(json.dumps(results, indent=2))
