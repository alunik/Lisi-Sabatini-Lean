#!/usr/bin/env python3
"""Regenerate the conservative A8 masks used by the checked witness."""
from pathlib import Path
import argparse, json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true', help='compare generated output without modifying files')
args=parser.parse_args()
ROOT=Path(__file__).resolve().parent
DATA=json.loads((ROOT/'A8Data.json').read_text())
MODULUS=4093
PRIMES=[2,3,5,7]

def code(g):
    result=0
    for x in g: result=result*8+x
    return result

def lean_nat(n):
    digits=str(n)
    first=len(digits)%64 or 64
    chunks=[digits[:first]]+[digits[i:i+64] for i in range(first,len(digits),64)]
    lines=['  let blockBase : ℕ := 10 ^ 64',f'  let acc : ℕ := {int(chunks[0])}']
    lines += [f'  let acc := acc * blockBase + {int(chunk)}' for chunk in chunks[1:]]
    lines += ['  acc']
    return '\n'.join(lines)

masks=[]
for row in DATA['rows']:
    elements=[tuple(e['images']) for e in row['elements']]
    residues={code(g)%MODULUS for g in elements}
    masks.append(sum(1<<i for i in residues))

files={}
base='''module

public import LisiSabatini.FiniteCertificates.A8Rows
public import LisiSabatini.FiniteCertificates.FingerprintCheck

/-!
# Small conservative fingerprints for the A8 rows

Generated data only: all mask-coverage proofs below use kernel evaluation.
A hash collision can reject an additional conjugator but cannot accept an
incorrect one. The resulting bounds are 2218, 276, 26, and 16.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates.A8FingerprintData

open A8Rows

abbrev G := A8Rows.G

local instance : DecidableEq G := alternatingCodeDecidableEq_fin8

set_option maxRecDepth 100000

/-- Eight-image base-8 code reduced to a 4093-bit fingerprint mask. -/
def fingerprint (g : G) : ℕ := permutationCode g.val % 4093

'''
for p,mask in zip(PRIMES,masks):
    base+=f'''def mask{p} : ℕ :=
{lean_nat(mask)}

set_option maxHeartbeats 0 in
-- Kernel evaluation checks every entry in this finite row.
theorem row{p}_mask : ∀ y ∈ row{p}, mask{p}.testBit (fingerprint y) = true := by
  have hcheck : row{p}Elements.all (fun y ↦ mask{p}.testBit (fingerprint y)) = true := by
    decide +kernel
  intro y hy
  change y ∈ row{p}Elements at hy
  exact List.all_eq_true.mp hcheck y hy

theorem row{p}_cover : ∀ y ∈ row{p}, y ≠ 1 → y ∈ row{p}Probes := by
  intro y hy hone
  change y ∈ row{p}Elements at hy
  rw [row{p}Elements_eq_one_cons] at hy
  exact (List.mem_cons.mp hy).resolve_left hone

/-- Rejection is deliberately conservative. -/
def rejected{p} (g : G) : Bool :=
  !(fingerprintGoodCheck fingerprint mask{p} row{p}Probes g)

'''
base+='end LisiSabatini.FiniteCertificates.A8FingerprintData\n'
files[ROOT/'A8FingerprintData.lean']=base
check=args.check
for path,txt in files.items():
    if check:
        assert path.exists() and path.read_text()==txt, path
    else:
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(txt)
print(('CHECK' if check else 'GENERATE')+' PASS: '+str(len(files))+' Lean mask module')
