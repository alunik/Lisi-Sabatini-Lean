module

public import LisiSabatini.FiniteCertificates.PermutationTable
public import LisiSabatini.SymmetricFiniteCertificates.ListTable
public import Mathlib.Tactic.NormNum

/-!
# Literal full-group and Sylow tables for S6

Generated deterministically by `SymmetricFiniteCertificates/generate.py`.
Every acceptance theorem is checked by the Lean kernel.
-/

@[expose] public section

namespace LisiSabatini.SymmetricFiniteCertificates.S6Three

set_option maxRecDepth 100000

open LisiSabatini.FiniteCertificates

abbrev G := Equiv.Perm (Fin 6)

def e0 : G where
  toFun := ![0, 1, 2, 3, 4, 5]
  invFun := ![0, 1, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : G where
  toFun := ![0, 1, 2, 3, 5, 4]
  invFun := ![0, 1, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : G where
  toFun := ![0, 1, 2, 4, 3, 5]
  invFun := ![0, 1, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : G where
  toFun := ![0, 1, 2, 4, 5, 3]
  invFun := ![0, 1, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : G where
  toFun := ![0, 1, 2, 5, 3, 4]
  invFun := ![0, 1, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : G where
  toFun := ![0, 1, 2, 5, 4, 3]
  invFun := ![0, 1, 2, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : G where
  toFun := ![0, 1, 3, 2, 4, 5]
  invFun := ![0, 1, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : G where
  toFun := ![0, 1, 3, 2, 5, 4]
  invFun := ![0, 1, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : G where
  toFun := ![0, 1, 3, 4, 2, 5]
  invFun := ![0, 1, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : G where
  toFun := ![0, 1, 3, 4, 5, 2]
  invFun := ![0, 1, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : G where
  toFun := ![0, 1, 3, 5, 2, 4]
  invFun := ![0, 1, 4, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : G where
  toFun := ![0, 1, 3, 5, 4, 2]
  invFun := ![0, 1, 5, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : G where
  toFun := ![0, 1, 4, 2, 3, 5]
  invFun := ![0, 1, 3, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : G where
  toFun := ![0, 1, 4, 2, 5, 3]
  invFun := ![0, 1, 3, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : G where
  toFun := ![0, 1, 4, 3, 2, 5]
  invFun := ![0, 1, 4, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : G where
  toFun := ![0, 1, 4, 3, 5, 2]
  invFun := ![0, 1, 5, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e16 : G where
  toFun := ![0, 1, 4, 5, 2, 3]
  invFun := ![0, 1, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e17 : G where
  toFun := ![0, 1, 4, 5, 3, 2]
  invFun := ![0, 1, 5, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e18 : G where
  toFun := ![0, 1, 5, 2, 3, 4]
  invFun := ![0, 1, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e19 : G where
  toFun := ![0, 1, 5, 2, 4, 3]
  invFun := ![0, 1, 3, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e20 : G where
  toFun := ![0, 1, 5, 3, 2, 4]
  invFun := ![0, 1, 4, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e21 : G where
  toFun := ![0, 1, 5, 3, 4, 2]
  invFun := ![0, 1, 5, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e22 : G where
  toFun := ![0, 1, 5, 4, 2, 3]
  invFun := ![0, 1, 4, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e23 : G where
  toFun := ![0, 1, 5, 4, 3, 2]
  invFun := ![0, 1, 5, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e24 : G where
  toFun := ![0, 2, 1, 3, 4, 5]
  invFun := ![0, 2, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e25 : G where
  toFun := ![0, 2, 1, 3, 5, 4]
  invFun := ![0, 2, 1, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e26 : G where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e27 : G where
  toFun := ![0, 2, 1, 4, 5, 3]
  invFun := ![0, 2, 1, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e28 : G where
  toFun := ![0, 2, 1, 5, 3, 4]
  invFun := ![0, 2, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e29 : G where
  toFun := ![0, 2, 1, 5, 4, 3]
  invFun := ![0, 2, 1, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e30 : G where
  toFun := ![0, 2, 3, 1, 4, 5]
  invFun := ![0, 3, 1, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e31 : G where
  toFun := ![0, 2, 3, 1, 5, 4]
  invFun := ![0, 3, 1, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e32 : G where
  toFun := ![0, 2, 3, 4, 1, 5]
  invFun := ![0, 4, 1, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e33 : G where
  toFun := ![0, 2, 3, 4, 5, 1]
  invFun := ![0, 5, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e34 : G where
  toFun := ![0, 2, 3, 5, 1, 4]
  invFun := ![0, 4, 1, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e35 : G where
  toFun := ![0, 2, 3, 5, 4, 1]
  invFun := ![0, 5, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e36 : G where
  toFun := ![0, 2, 4, 1, 3, 5]
  invFun := ![0, 3, 1, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e37 : G where
  toFun := ![0, 2, 4, 1, 5, 3]
  invFun := ![0, 3, 1, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e38 : G where
  toFun := ![0, 2, 4, 3, 1, 5]
  invFun := ![0, 4, 1, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e39 : G where
  toFun := ![0, 2, 4, 3, 5, 1]
  invFun := ![0, 5, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e40 : G where
  toFun := ![0, 2, 4, 5, 1, 3]
  invFun := ![0, 4, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e41 : G where
  toFun := ![0, 2, 4, 5, 3, 1]
  invFun := ![0, 5, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e42 : G where
  toFun := ![0, 2, 5, 1, 3, 4]
  invFun := ![0, 3, 1, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e43 : G where
  toFun := ![0, 2, 5, 1, 4, 3]
  invFun := ![0, 3, 1, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e44 : G where
  toFun := ![0, 2, 5, 3, 1, 4]
  invFun := ![0, 4, 1, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e45 : G where
  toFun := ![0, 2, 5, 3, 4, 1]
  invFun := ![0, 5, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e46 : G where
  toFun := ![0, 2, 5, 4, 1, 3]
  invFun := ![0, 4, 1, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e47 : G where
  toFun := ![0, 2, 5, 4, 3, 1]
  invFun := ![0, 5, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e48 : G where
  toFun := ![0, 3, 1, 2, 4, 5]
  invFun := ![0, 2, 3, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e49 : G where
  toFun := ![0, 3, 1, 2, 5, 4]
  invFun := ![0, 2, 3, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e50 : G where
  toFun := ![0, 3, 1, 4, 2, 5]
  invFun := ![0, 2, 4, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e51 : G where
  toFun := ![0, 3, 1, 4, 5, 2]
  invFun := ![0, 2, 5, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e52 : G where
  toFun := ![0, 3, 1, 5, 2, 4]
  invFun := ![0, 2, 4, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e53 : G where
  toFun := ![0, 3, 1, 5, 4, 2]
  invFun := ![0, 2, 5, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e54 : G where
  toFun := ![0, 3, 2, 1, 4, 5]
  invFun := ![0, 3, 2, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e55 : G where
  toFun := ![0, 3, 2, 1, 5, 4]
  invFun := ![0, 3, 2, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e56 : G where
  toFun := ![0, 3, 2, 4, 1, 5]
  invFun := ![0, 4, 2, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e57 : G where
  toFun := ![0, 3, 2, 4, 5, 1]
  invFun := ![0, 5, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e58 : G where
  toFun := ![0, 3, 2, 5, 1, 4]
  invFun := ![0, 4, 2, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e59 : G where
  toFun := ![0, 3, 2, 5, 4, 1]
  invFun := ![0, 5, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e60 : G where
  toFun := ![0, 3, 4, 1, 2, 5]
  invFun := ![0, 3, 4, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e61 : G where
  toFun := ![0, 3, 4, 1, 5, 2]
  invFun := ![0, 3, 5, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e62 : G where
  toFun := ![0, 3, 4, 2, 1, 5]
  invFun := ![0, 4, 3, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e63 : G where
  toFun := ![0, 3, 4, 2, 5, 1]
  invFun := ![0, 5, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e64 : G where
  toFun := ![0, 3, 4, 5, 1, 2]
  invFun := ![0, 4, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e65 : G where
  toFun := ![0, 3, 4, 5, 2, 1]
  invFun := ![0, 5, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e66 : G where
  toFun := ![0, 3, 5, 1, 2, 4]
  invFun := ![0, 3, 4, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e67 : G where
  toFun := ![0, 3, 5, 1, 4, 2]
  invFun := ![0, 3, 5, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e68 : G where
  toFun := ![0, 3, 5, 2, 1, 4]
  invFun := ![0, 4, 3, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e69 : G where
  toFun := ![0, 3, 5, 2, 4, 1]
  invFun := ![0, 5, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e70 : G where
  toFun := ![0, 3, 5, 4, 1, 2]
  invFun := ![0, 4, 5, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e71 : G where
  toFun := ![0, 3, 5, 4, 2, 1]
  invFun := ![0, 5, 4, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e72 : G where
  toFun := ![0, 4, 1, 2, 3, 5]
  invFun := ![0, 2, 3, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e73 : G where
  toFun := ![0, 4, 1, 2, 5, 3]
  invFun := ![0, 2, 3, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e74 : G where
  toFun := ![0, 4, 1, 3, 2, 5]
  invFun := ![0, 2, 4, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e75 : G where
  toFun := ![0, 4, 1, 3, 5, 2]
  invFun := ![0, 2, 5, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e76 : G where
  toFun := ![0, 4, 1, 5, 2, 3]
  invFun := ![0, 2, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e77 : G where
  toFun := ![0, 4, 1, 5, 3, 2]
  invFun := ![0, 2, 5, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e78 : G where
  toFun := ![0, 4, 2, 1, 3, 5]
  invFun := ![0, 3, 2, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e79 : G where
  toFun := ![0, 4, 2, 1, 5, 3]
  invFun := ![0, 3, 2, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e80 : G where
  toFun := ![0, 4, 2, 3, 1, 5]
  invFun := ![0, 4, 2, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e81 : G where
  toFun := ![0, 4, 2, 3, 5, 1]
  invFun := ![0, 5, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e82 : G where
  toFun := ![0, 4, 2, 5, 1, 3]
  invFun := ![0, 4, 2, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e83 : G where
  toFun := ![0, 4, 2, 5, 3, 1]
  invFun := ![0, 5, 2, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e84 : G where
  toFun := ![0, 4, 3, 1, 2, 5]
  invFun := ![0, 3, 4, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e85 : G where
  toFun := ![0, 4, 3, 1, 5, 2]
  invFun := ![0, 3, 5, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e86 : G where
  toFun := ![0, 4, 3, 2, 1, 5]
  invFun := ![0, 4, 3, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e87 : G where
  toFun := ![0, 4, 3, 2, 5, 1]
  invFun := ![0, 5, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e88 : G where
  toFun := ![0, 4, 3, 5, 1, 2]
  invFun := ![0, 4, 5, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e89 : G where
  toFun := ![0, 4, 3, 5, 2, 1]
  invFun := ![0, 5, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e90 : G where
  toFun := ![0, 4, 5, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e91 : G where
  toFun := ![0, 4, 5, 1, 3, 2]
  invFun := ![0, 3, 5, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e92 : G where
  toFun := ![0, 4, 5, 2, 1, 3]
  invFun := ![0, 4, 3, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e93 : G where
  toFun := ![0, 4, 5, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e94 : G where
  toFun := ![0, 4, 5, 3, 1, 2]
  invFun := ![0, 4, 5, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e95 : G where
  toFun := ![0, 4, 5, 3, 2, 1]
  invFun := ![0, 5, 4, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e96 : G where
  toFun := ![0, 5, 1, 2, 3, 4]
  invFun := ![0, 2, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e97 : G where
  toFun := ![0, 5, 1, 2, 4, 3]
  invFun := ![0, 2, 3, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e98 : G where
  toFun := ![0, 5, 1, 3, 2, 4]
  invFun := ![0, 2, 4, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e99 : G where
  toFun := ![0, 5, 1, 3, 4, 2]
  invFun := ![0, 2, 5, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e100 : G where
  toFun := ![0, 5, 1, 4, 2, 3]
  invFun := ![0, 2, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e101 : G where
  toFun := ![0, 5, 1, 4, 3, 2]
  invFun := ![0, 2, 5, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e102 : G where
  toFun := ![0, 5, 2, 1, 3, 4]
  invFun := ![0, 3, 2, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e103 : G where
  toFun := ![0, 5, 2, 1, 4, 3]
  invFun := ![0, 3, 2, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e104 : G where
  toFun := ![0, 5, 2, 3, 1, 4]
  invFun := ![0, 4, 2, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e105 : G where
  toFun := ![0, 5, 2, 3, 4, 1]
  invFun := ![0, 5, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e106 : G where
  toFun := ![0, 5, 2, 4, 1, 3]
  invFun := ![0, 4, 2, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e107 : G where
  toFun := ![0, 5, 2, 4, 3, 1]
  invFun := ![0, 5, 2, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e108 : G where
  toFun := ![0, 5, 3, 1, 2, 4]
  invFun := ![0, 3, 4, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e109 : G where
  toFun := ![0, 5, 3, 1, 4, 2]
  invFun := ![0, 3, 5, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e110 : G where
  toFun := ![0, 5, 3, 2, 1, 4]
  invFun := ![0, 4, 3, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e111 : G where
  toFun := ![0, 5, 3, 2, 4, 1]
  invFun := ![0, 5, 3, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e112 : G where
  toFun := ![0, 5, 3, 4, 1, 2]
  invFun := ![0, 4, 5, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e113 : G where
  toFun := ![0, 5, 3, 4, 2, 1]
  invFun := ![0, 5, 4, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e114 : G where
  toFun := ![0, 5, 4, 1, 2, 3]
  invFun := ![0, 3, 4, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e115 : G where
  toFun := ![0, 5, 4, 1, 3, 2]
  invFun := ![0, 3, 5, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e116 : G where
  toFun := ![0, 5, 4, 2, 1, 3]
  invFun := ![0, 4, 3, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e117 : G where
  toFun := ![0, 5, 4, 2, 3, 1]
  invFun := ![0, 5, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e118 : G where
  toFun := ![0, 5, 4, 3, 1, 2]
  invFun := ![0, 4, 5, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e119 : G where
  toFun := ![0, 5, 4, 3, 2, 1]
  invFun := ![0, 5, 4, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e120 : G where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e121 : G where
  toFun := ![1, 0, 2, 3, 5, 4]
  invFun := ![1, 0, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e122 : G where
  toFun := ![1, 0, 2, 4, 3, 5]
  invFun := ![1, 0, 2, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e123 : G where
  toFun := ![1, 0, 2, 4, 5, 3]
  invFun := ![1, 0, 2, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e124 : G where
  toFun := ![1, 0, 2, 5, 3, 4]
  invFun := ![1, 0, 2, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e125 : G where
  toFun := ![1, 0, 2, 5, 4, 3]
  invFun := ![1, 0, 2, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e126 : G where
  toFun := ![1, 0, 3, 2, 4, 5]
  invFun := ![1, 0, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e127 : G where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e128 : G where
  toFun := ![1, 0, 3, 4, 2, 5]
  invFun := ![1, 0, 4, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e129 : G where
  toFun := ![1, 0, 3, 4, 5, 2]
  invFun := ![1, 0, 5, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e130 : G where
  toFun := ![1, 0, 3, 5, 2, 4]
  invFun := ![1, 0, 4, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e131 : G where
  toFun := ![1, 0, 3, 5, 4, 2]
  invFun := ![1, 0, 5, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e132 : G where
  toFun := ![1, 0, 4, 2, 3, 5]
  invFun := ![1, 0, 3, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e133 : G where
  toFun := ![1, 0, 4, 2, 5, 3]
  invFun := ![1, 0, 3, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e134 : G where
  toFun := ![1, 0, 4, 3, 2, 5]
  invFun := ![1, 0, 4, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e135 : G where
  toFun := ![1, 0, 4, 3, 5, 2]
  invFun := ![1, 0, 5, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e136 : G where
  toFun := ![1, 0, 4, 5, 2, 3]
  invFun := ![1, 0, 4, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e137 : G where
  toFun := ![1, 0, 4, 5, 3, 2]
  invFun := ![1, 0, 5, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e138 : G where
  toFun := ![1, 0, 5, 2, 3, 4]
  invFun := ![1, 0, 3, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e139 : G where
  toFun := ![1, 0, 5, 2, 4, 3]
  invFun := ![1, 0, 3, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e140 : G where
  toFun := ![1, 0, 5, 3, 2, 4]
  invFun := ![1, 0, 4, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e141 : G where
  toFun := ![1, 0, 5, 3, 4, 2]
  invFun := ![1, 0, 5, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e142 : G where
  toFun := ![1, 0, 5, 4, 2, 3]
  invFun := ![1, 0, 4, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e143 : G where
  toFun := ![1, 0, 5, 4, 3, 2]
  invFun := ![1, 0, 5, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e144 : G where
  toFun := ![1, 2, 0, 3, 4, 5]
  invFun := ![2, 0, 1, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e145 : G where
  toFun := ![1, 2, 0, 3, 5, 4]
  invFun := ![2, 0, 1, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e146 : G where
  toFun := ![1, 2, 0, 4, 3, 5]
  invFun := ![2, 0, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e147 : G where
  toFun := ![1, 2, 0, 4, 5, 3]
  invFun := ![2, 0, 1, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e148 : G where
  toFun := ![1, 2, 0, 5, 3, 4]
  invFun := ![2, 0, 1, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e149 : G where
  toFun := ![1, 2, 0, 5, 4, 3]
  invFun := ![2, 0, 1, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e150 : G where
  toFun := ![1, 2, 3, 0, 4, 5]
  invFun := ![3, 0, 1, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e151 : G where
  toFun := ![1, 2, 3, 0, 5, 4]
  invFun := ![3, 0, 1, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e152 : G where
  toFun := ![1, 2, 3, 4, 0, 5]
  invFun := ![4, 0, 1, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e153 : G where
  toFun := ![1, 2, 3, 4, 5, 0]
  invFun := ![5, 0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e154 : G where
  toFun := ![1, 2, 3, 5, 0, 4]
  invFun := ![4, 0, 1, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e155 : G where
  toFun := ![1, 2, 3, 5, 4, 0]
  invFun := ![5, 0, 1, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e156 : G where
  toFun := ![1, 2, 4, 0, 3, 5]
  invFun := ![3, 0, 1, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e157 : G where
  toFun := ![1, 2, 4, 0, 5, 3]
  invFun := ![3, 0, 1, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e158 : G where
  toFun := ![1, 2, 4, 3, 0, 5]
  invFun := ![4, 0, 1, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e159 : G where
  toFun := ![1, 2, 4, 3, 5, 0]
  invFun := ![5, 0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e160 : G where
  toFun := ![1, 2, 4, 5, 0, 3]
  invFun := ![4, 0, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e161 : G where
  toFun := ![1, 2, 4, 5, 3, 0]
  invFun := ![5, 0, 1, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e162 : G where
  toFun := ![1, 2, 5, 0, 3, 4]
  invFun := ![3, 0, 1, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e163 : G where
  toFun := ![1, 2, 5, 0, 4, 3]
  invFun := ![3, 0, 1, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e164 : G where
  toFun := ![1, 2, 5, 3, 0, 4]
  invFun := ![4, 0, 1, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e165 : G where
  toFun := ![1, 2, 5, 3, 4, 0]
  invFun := ![5, 0, 1, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e166 : G where
  toFun := ![1, 2, 5, 4, 0, 3]
  invFun := ![4, 0, 1, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e167 : G where
  toFun := ![1, 2, 5, 4, 3, 0]
  invFun := ![5, 0, 1, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e168 : G where
  toFun := ![1, 3, 0, 2, 4, 5]
  invFun := ![2, 0, 3, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e169 : G where
  toFun := ![1, 3, 0, 2, 5, 4]
  invFun := ![2, 0, 3, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e170 : G where
  toFun := ![1, 3, 0, 4, 2, 5]
  invFun := ![2, 0, 4, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e171 : G where
  toFun := ![1, 3, 0, 4, 5, 2]
  invFun := ![2, 0, 5, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e172 : G where
  toFun := ![1, 3, 0, 5, 2, 4]
  invFun := ![2, 0, 4, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e173 : G where
  toFun := ![1, 3, 0, 5, 4, 2]
  invFun := ![2, 0, 5, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e174 : G where
  toFun := ![1, 3, 2, 0, 4, 5]
  invFun := ![3, 0, 2, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e175 : G where
  toFun := ![1, 3, 2, 0, 5, 4]
  invFun := ![3, 0, 2, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e176 : G where
  toFun := ![1, 3, 2, 4, 0, 5]
  invFun := ![4, 0, 2, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e177 : G where
  toFun := ![1, 3, 2, 4, 5, 0]
  invFun := ![5, 0, 2, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e178 : G where
  toFun := ![1, 3, 2, 5, 0, 4]
  invFun := ![4, 0, 2, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e179 : G where
  toFun := ![1, 3, 2, 5, 4, 0]
  invFun := ![5, 0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e180 : G where
  toFun := ![1, 3, 4, 0, 2, 5]
  invFun := ![3, 0, 4, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e181 : G where
  toFun := ![1, 3, 4, 0, 5, 2]
  invFun := ![3, 0, 5, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e182 : G where
  toFun := ![1, 3, 4, 2, 0, 5]
  invFun := ![4, 0, 3, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e183 : G where
  toFun := ![1, 3, 4, 2, 5, 0]
  invFun := ![5, 0, 3, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e184 : G where
  toFun := ![1, 3, 4, 5, 0, 2]
  invFun := ![4, 0, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e185 : G where
  toFun := ![1, 3, 4, 5, 2, 0]
  invFun := ![5, 0, 4, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e186 : G where
  toFun := ![1, 3, 5, 0, 2, 4]
  invFun := ![3, 0, 4, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e187 : G where
  toFun := ![1, 3, 5, 0, 4, 2]
  invFun := ![3, 0, 5, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e188 : G where
  toFun := ![1, 3, 5, 2, 0, 4]
  invFun := ![4, 0, 3, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e189 : G where
  toFun := ![1, 3, 5, 2, 4, 0]
  invFun := ![5, 0, 3, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e190 : G where
  toFun := ![1, 3, 5, 4, 0, 2]
  invFun := ![4, 0, 5, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e191 : G where
  toFun := ![1, 3, 5, 4, 2, 0]
  invFun := ![5, 0, 4, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e192 : G where
  toFun := ![1, 4, 0, 2, 3, 5]
  invFun := ![2, 0, 3, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e193 : G where
  toFun := ![1, 4, 0, 2, 5, 3]
  invFun := ![2, 0, 3, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e194 : G where
  toFun := ![1, 4, 0, 3, 2, 5]
  invFun := ![2, 0, 4, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e195 : G where
  toFun := ![1, 4, 0, 3, 5, 2]
  invFun := ![2, 0, 5, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e196 : G where
  toFun := ![1, 4, 0, 5, 2, 3]
  invFun := ![2, 0, 4, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e197 : G where
  toFun := ![1, 4, 0, 5, 3, 2]
  invFun := ![2, 0, 5, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e198 : G where
  toFun := ![1, 4, 2, 0, 3, 5]
  invFun := ![3, 0, 2, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e199 : G where
  toFun := ![1, 4, 2, 0, 5, 3]
  invFun := ![3, 0, 2, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e200 : G where
  toFun := ![1, 4, 2, 3, 0, 5]
  invFun := ![4, 0, 2, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e201 : G where
  toFun := ![1, 4, 2, 3, 5, 0]
  invFun := ![5, 0, 2, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e202 : G where
  toFun := ![1, 4, 2, 5, 0, 3]
  invFun := ![4, 0, 2, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e203 : G where
  toFun := ![1, 4, 2, 5, 3, 0]
  invFun := ![5, 0, 2, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e204 : G where
  toFun := ![1, 4, 3, 0, 2, 5]
  invFun := ![3, 0, 4, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e205 : G where
  toFun := ![1, 4, 3, 0, 5, 2]
  invFun := ![3, 0, 5, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e206 : G where
  toFun := ![1, 4, 3, 2, 0, 5]
  invFun := ![4, 0, 3, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e207 : G where
  toFun := ![1, 4, 3, 2, 5, 0]
  invFun := ![5, 0, 3, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e208 : G where
  toFun := ![1, 4, 3, 5, 0, 2]
  invFun := ![4, 0, 5, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e209 : G where
  toFun := ![1, 4, 3, 5, 2, 0]
  invFun := ![5, 0, 4, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e210 : G where
  toFun := ![1, 4, 5, 0, 2, 3]
  invFun := ![3, 0, 4, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e211 : G where
  toFun := ![1, 4, 5, 0, 3, 2]
  invFun := ![3, 0, 5, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e212 : G where
  toFun := ![1, 4, 5, 2, 0, 3]
  invFun := ![4, 0, 3, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e213 : G where
  toFun := ![1, 4, 5, 2, 3, 0]
  invFun := ![5, 0, 3, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e214 : G where
  toFun := ![1, 4, 5, 3, 0, 2]
  invFun := ![4, 0, 5, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e215 : G where
  toFun := ![1, 4, 5, 3, 2, 0]
  invFun := ![5, 0, 4, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e216 : G where
  toFun := ![1, 5, 0, 2, 3, 4]
  invFun := ![2, 0, 3, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e217 : G where
  toFun := ![1, 5, 0, 2, 4, 3]
  invFun := ![2, 0, 3, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e218 : G where
  toFun := ![1, 5, 0, 3, 2, 4]
  invFun := ![2, 0, 4, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e219 : G where
  toFun := ![1, 5, 0, 3, 4, 2]
  invFun := ![2, 0, 5, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e220 : G where
  toFun := ![1, 5, 0, 4, 2, 3]
  invFun := ![2, 0, 4, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e221 : G where
  toFun := ![1, 5, 0, 4, 3, 2]
  invFun := ![2, 0, 5, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e222 : G where
  toFun := ![1, 5, 2, 0, 3, 4]
  invFun := ![3, 0, 2, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e223 : G where
  toFun := ![1, 5, 2, 0, 4, 3]
  invFun := ![3, 0, 2, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e224 : G where
  toFun := ![1, 5, 2, 3, 0, 4]
  invFun := ![4, 0, 2, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e225 : G where
  toFun := ![1, 5, 2, 3, 4, 0]
  invFun := ![5, 0, 2, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e226 : G where
  toFun := ![1, 5, 2, 4, 0, 3]
  invFun := ![4, 0, 2, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e227 : G where
  toFun := ![1, 5, 2, 4, 3, 0]
  invFun := ![5, 0, 2, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e228 : G where
  toFun := ![1, 5, 3, 0, 2, 4]
  invFun := ![3, 0, 4, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e229 : G where
  toFun := ![1, 5, 3, 0, 4, 2]
  invFun := ![3, 0, 5, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e230 : G where
  toFun := ![1, 5, 3, 2, 0, 4]
  invFun := ![4, 0, 3, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e231 : G where
  toFun := ![1, 5, 3, 2, 4, 0]
  invFun := ![5, 0, 3, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e232 : G where
  toFun := ![1, 5, 3, 4, 0, 2]
  invFun := ![4, 0, 5, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e233 : G where
  toFun := ![1, 5, 3, 4, 2, 0]
  invFun := ![5, 0, 4, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e234 : G where
  toFun := ![1, 5, 4, 0, 2, 3]
  invFun := ![3, 0, 4, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e235 : G where
  toFun := ![1, 5, 4, 0, 3, 2]
  invFun := ![3, 0, 5, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e236 : G where
  toFun := ![1, 5, 4, 2, 0, 3]
  invFun := ![4, 0, 3, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e237 : G where
  toFun := ![1, 5, 4, 2, 3, 0]
  invFun := ![5, 0, 3, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e238 : G where
  toFun := ![1, 5, 4, 3, 0, 2]
  invFun := ![4, 0, 5, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e239 : G where
  toFun := ![1, 5, 4, 3, 2, 0]
  invFun := ![5, 0, 4, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e240 : G where
  toFun := ![2, 0, 1, 3, 4, 5]
  invFun := ![1, 2, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e241 : G where
  toFun := ![2, 0, 1, 3, 5, 4]
  invFun := ![1, 2, 0, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e242 : G where
  toFun := ![2, 0, 1, 4, 3, 5]
  invFun := ![1, 2, 0, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e243 : G where
  toFun := ![2, 0, 1, 4, 5, 3]
  invFun := ![1, 2, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e244 : G where
  toFun := ![2, 0, 1, 5, 3, 4]
  invFun := ![1, 2, 0, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e245 : G where
  toFun := ![2, 0, 1, 5, 4, 3]
  invFun := ![1, 2, 0, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e246 : G where
  toFun := ![2, 0, 3, 1, 4, 5]
  invFun := ![1, 3, 0, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e247 : G where
  toFun := ![2, 0, 3, 1, 5, 4]
  invFun := ![1, 3, 0, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e248 : G where
  toFun := ![2, 0, 3, 4, 1, 5]
  invFun := ![1, 4, 0, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e249 : G where
  toFun := ![2, 0, 3, 4, 5, 1]
  invFun := ![1, 5, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e250 : G where
  toFun := ![2, 0, 3, 5, 1, 4]
  invFun := ![1, 4, 0, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e251 : G where
  toFun := ![2, 0, 3, 5, 4, 1]
  invFun := ![1, 5, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e252 : G where
  toFun := ![2, 0, 4, 1, 3, 5]
  invFun := ![1, 3, 0, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e253 : G where
  toFun := ![2, 0, 4, 1, 5, 3]
  invFun := ![1, 3, 0, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e254 : G where
  toFun := ![2, 0, 4, 3, 1, 5]
  invFun := ![1, 4, 0, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e255 : G where
  toFun := ![2, 0, 4, 3, 5, 1]
  invFun := ![1, 5, 0, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e256 : G where
  toFun := ![2, 0, 4, 5, 1, 3]
  invFun := ![1, 4, 0, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e257 : G where
  toFun := ![2, 0, 4, 5, 3, 1]
  invFun := ![1, 5, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e258 : G where
  toFun := ![2, 0, 5, 1, 3, 4]
  invFun := ![1, 3, 0, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e259 : G where
  toFun := ![2, 0, 5, 1, 4, 3]
  invFun := ![1, 3, 0, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e260 : G where
  toFun := ![2, 0, 5, 3, 1, 4]
  invFun := ![1, 4, 0, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e261 : G where
  toFun := ![2, 0, 5, 3, 4, 1]
  invFun := ![1, 5, 0, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e262 : G where
  toFun := ![2, 0, 5, 4, 1, 3]
  invFun := ![1, 4, 0, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e263 : G where
  toFun := ![2, 0, 5, 4, 3, 1]
  invFun := ![1, 5, 0, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e264 : G where
  toFun := ![2, 1, 0, 3, 4, 5]
  invFun := ![2, 1, 0, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e265 : G where
  toFun := ![2, 1, 0, 3, 5, 4]
  invFun := ![2, 1, 0, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e266 : G where
  toFun := ![2, 1, 0, 4, 3, 5]
  invFun := ![2, 1, 0, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e267 : G where
  toFun := ![2, 1, 0, 4, 5, 3]
  invFun := ![2, 1, 0, 5, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e268 : G where
  toFun := ![2, 1, 0, 5, 3, 4]
  invFun := ![2, 1, 0, 4, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e269 : G where
  toFun := ![2, 1, 0, 5, 4, 3]
  invFun := ![2, 1, 0, 5, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e270 : G where
  toFun := ![2, 1, 3, 0, 4, 5]
  invFun := ![3, 1, 0, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e271 : G where
  toFun := ![2, 1, 3, 0, 5, 4]
  invFun := ![3, 1, 0, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e272 : G where
  toFun := ![2, 1, 3, 4, 0, 5]
  invFun := ![4, 1, 0, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e273 : G where
  toFun := ![2, 1, 3, 4, 5, 0]
  invFun := ![5, 1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e274 : G where
  toFun := ![2, 1, 3, 5, 0, 4]
  invFun := ![4, 1, 0, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e275 : G where
  toFun := ![2, 1, 3, 5, 4, 0]
  invFun := ![5, 1, 0, 2, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e276 : G where
  toFun := ![2, 1, 4, 0, 3, 5]
  invFun := ![3, 1, 0, 4, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e277 : G where
  toFun := ![2, 1, 4, 0, 5, 3]
  invFun := ![3, 1, 0, 5, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e278 : G where
  toFun := ![2, 1, 4, 3, 0, 5]
  invFun := ![4, 1, 0, 3, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e279 : G where
  toFun := ![2, 1, 4, 3, 5, 0]
  invFun := ![5, 1, 0, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e280 : G where
  toFun := ![2, 1, 4, 5, 0, 3]
  invFun := ![4, 1, 0, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e281 : G where
  toFun := ![2, 1, 4, 5, 3, 0]
  invFun := ![5, 1, 0, 4, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e282 : G where
  toFun := ![2, 1, 5, 0, 3, 4]
  invFun := ![3, 1, 0, 4, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e283 : G where
  toFun := ![2, 1, 5, 0, 4, 3]
  invFun := ![3, 1, 0, 5, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e284 : G where
  toFun := ![2, 1, 5, 3, 0, 4]
  invFun := ![4, 1, 0, 3, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e285 : G where
  toFun := ![2, 1, 5, 3, 4, 0]
  invFun := ![5, 1, 0, 3, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e286 : G where
  toFun := ![2, 1, 5, 4, 0, 3]
  invFun := ![4, 1, 0, 5, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e287 : G where
  toFun := ![2, 1, 5, 4, 3, 0]
  invFun := ![5, 1, 0, 4, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e288 : G where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e289 : G where
  toFun := ![2, 3, 0, 1, 5, 4]
  invFun := ![2, 3, 0, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e290 : G where
  toFun := ![2, 3, 0, 4, 1, 5]
  invFun := ![2, 4, 0, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e291 : G where
  toFun := ![2, 3, 0, 4, 5, 1]
  invFun := ![2, 5, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e292 : G where
  toFun := ![2, 3, 0, 5, 1, 4]
  invFun := ![2, 4, 0, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e293 : G where
  toFun := ![2, 3, 0, 5, 4, 1]
  invFun := ![2, 5, 0, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e294 : G where
  toFun := ![2, 3, 1, 0, 4, 5]
  invFun := ![3, 2, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e295 : G where
  toFun := ![2, 3, 1, 0, 5, 4]
  invFun := ![3, 2, 0, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e296 : G where
  toFun := ![2, 3, 1, 4, 0, 5]
  invFun := ![4, 2, 0, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e297 : G where
  toFun := ![2, 3, 1, 4, 5, 0]
  invFun := ![5, 2, 0, 1, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e298 : G where
  toFun := ![2, 3, 1, 5, 0, 4]
  invFun := ![4, 2, 0, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e299 : G where
  toFun := ![2, 3, 1, 5, 4, 0]
  invFun := ![5, 2, 0, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e300 : G where
  toFun := ![2, 3, 4, 0, 1, 5]
  invFun := ![3, 4, 0, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e301 : G where
  toFun := ![2, 3, 4, 0, 5, 1]
  invFun := ![3, 5, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e302 : G where
  toFun := ![2, 3, 4, 1, 0, 5]
  invFun := ![4, 3, 0, 1, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e303 : G where
  toFun := ![2, 3, 4, 1, 5, 0]
  invFun := ![5, 3, 0, 1, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e304 : G where
  toFun := ![2, 3, 4, 5, 0, 1]
  invFun := ![4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e305 : G where
  toFun := ![2, 3, 4, 5, 1, 0]
  invFun := ![5, 4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e306 : G where
  toFun := ![2, 3, 5, 0, 1, 4]
  invFun := ![3, 4, 0, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e307 : G where
  toFun := ![2, 3, 5, 0, 4, 1]
  invFun := ![3, 5, 0, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e308 : G where
  toFun := ![2, 3, 5, 1, 0, 4]
  invFun := ![4, 3, 0, 1, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e309 : G where
  toFun := ![2, 3, 5, 1, 4, 0]
  invFun := ![5, 3, 0, 1, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e310 : G where
  toFun := ![2, 3, 5, 4, 0, 1]
  invFun := ![4, 5, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e311 : G where
  toFun := ![2, 3, 5, 4, 1, 0]
  invFun := ![5, 4, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e312 : G where
  toFun := ![2, 4, 0, 1, 3, 5]
  invFun := ![2, 3, 0, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e313 : G where
  toFun := ![2, 4, 0, 1, 5, 3]
  invFun := ![2, 3, 0, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e314 : G where
  toFun := ![2, 4, 0, 3, 1, 5]
  invFun := ![2, 4, 0, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e315 : G where
  toFun := ![2, 4, 0, 3, 5, 1]
  invFun := ![2, 5, 0, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e316 : G where
  toFun := ![2, 4, 0, 5, 1, 3]
  invFun := ![2, 4, 0, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e317 : G where
  toFun := ![2, 4, 0, 5, 3, 1]
  invFun := ![2, 5, 0, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e318 : G where
  toFun := ![2, 4, 1, 0, 3, 5]
  invFun := ![3, 2, 0, 4, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e319 : G where
  toFun := ![2, 4, 1, 0, 5, 3]
  invFun := ![3, 2, 0, 5, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e320 : G where
  toFun := ![2, 4, 1, 3, 0, 5]
  invFun := ![4, 2, 0, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e321 : G where
  toFun := ![2, 4, 1, 3, 5, 0]
  invFun := ![5, 2, 0, 3, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e322 : G where
  toFun := ![2, 4, 1, 5, 0, 3]
  invFun := ![4, 2, 0, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e323 : G where
  toFun := ![2, 4, 1, 5, 3, 0]
  invFun := ![5, 2, 0, 4, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e324 : G where
  toFun := ![2, 4, 3, 0, 1, 5]
  invFun := ![3, 4, 0, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e325 : G where
  toFun := ![2, 4, 3, 0, 5, 1]
  invFun := ![3, 5, 0, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e326 : G where
  toFun := ![2, 4, 3, 1, 0, 5]
  invFun := ![4, 3, 0, 2, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e327 : G where
  toFun := ![2, 4, 3, 1, 5, 0]
  invFun := ![5, 3, 0, 2, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e328 : G where
  toFun := ![2, 4, 3, 5, 0, 1]
  invFun := ![4, 5, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e329 : G where
  toFun := ![2, 4, 3, 5, 1, 0]
  invFun := ![5, 4, 0, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e330 : G where
  toFun := ![2, 4, 5, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e331 : G where
  toFun := ![2, 4, 5, 0, 3, 1]
  invFun := ![3, 5, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e332 : G where
  toFun := ![2, 4, 5, 1, 0, 3]
  invFun := ![4, 3, 0, 5, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e333 : G where
  toFun := ![2, 4, 5, 1, 3, 0]
  invFun := ![5, 3, 0, 4, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e334 : G where
  toFun := ![2, 4, 5, 3, 0, 1]
  invFun := ![4, 5, 0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e335 : G where
  toFun := ![2, 4, 5, 3, 1, 0]
  invFun := ![5, 4, 0, 3, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e336 : G where
  toFun := ![2, 5, 0, 1, 3, 4]
  invFun := ![2, 3, 0, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e337 : G where
  toFun := ![2, 5, 0, 1, 4, 3]
  invFun := ![2, 3, 0, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e338 : G where
  toFun := ![2, 5, 0, 3, 1, 4]
  invFun := ![2, 4, 0, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e339 : G where
  toFun := ![2, 5, 0, 3, 4, 1]
  invFun := ![2, 5, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e340 : G where
  toFun := ![2, 5, 0, 4, 1, 3]
  invFun := ![2, 4, 0, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e341 : G where
  toFun := ![2, 5, 0, 4, 3, 1]
  invFun := ![2, 5, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e342 : G where
  toFun := ![2, 5, 1, 0, 3, 4]
  invFun := ![3, 2, 0, 4, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e343 : G where
  toFun := ![2, 5, 1, 0, 4, 3]
  invFun := ![3, 2, 0, 5, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e344 : G where
  toFun := ![2, 5, 1, 3, 0, 4]
  invFun := ![4, 2, 0, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e345 : G where
  toFun := ![2, 5, 1, 3, 4, 0]
  invFun := ![5, 2, 0, 3, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e346 : G where
  toFun := ![2, 5, 1, 4, 0, 3]
  invFun := ![4, 2, 0, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e347 : G where
  toFun := ![2, 5, 1, 4, 3, 0]
  invFun := ![5, 2, 0, 4, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e348 : G where
  toFun := ![2, 5, 3, 0, 1, 4]
  invFun := ![3, 4, 0, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e349 : G where
  toFun := ![2, 5, 3, 0, 4, 1]
  invFun := ![3, 5, 0, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e350 : G where
  toFun := ![2, 5, 3, 1, 0, 4]
  invFun := ![4, 3, 0, 2, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e351 : G where
  toFun := ![2, 5, 3, 1, 4, 0]
  invFun := ![5, 3, 0, 2, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e352 : G where
  toFun := ![2, 5, 3, 4, 0, 1]
  invFun := ![4, 5, 0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e353 : G where
  toFun := ![2, 5, 3, 4, 1, 0]
  invFun := ![5, 4, 0, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e354 : G where
  toFun := ![2, 5, 4, 0, 1, 3]
  invFun := ![3, 4, 0, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e355 : G where
  toFun := ![2, 5, 4, 0, 3, 1]
  invFun := ![3, 5, 0, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e356 : G where
  toFun := ![2, 5, 4, 1, 0, 3]
  invFun := ![4, 3, 0, 5, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e357 : G where
  toFun := ![2, 5, 4, 1, 3, 0]
  invFun := ![5, 3, 0, 4, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e358 : G where
  toFun := ![2, 5, 4, 3, 0, 1]
  invFun := ![4, 5, 0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e359 : G where
  toFun := ![2, 5, 4, 3, 1, 0]
  invFun := ![5, 4, 0, 3, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e360 : G where
  toFun := ![3, 0, 1, 2, 4, 5]
  invFun := ![1, 2, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e361 : G where
  toFun := ![3, 0, 1, 2, 5, 4]
  invFun := ![1, 2, 3, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e362 : G where
  toFun := ![3, 0, 1, 4, 2, 5]
  invFun := ![1, 2, 4, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e363 : G where
  toFun := ![3, 0, 1, 4, 5, 2]
  invFun := ![1, 2, 5, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e364 : G where
  toFun := ![3, 0, 1, 5, 2, 4]
  invFun := ![1, 2, 4, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e365 : G where
  toFun := ![3, 0, 1, 5, 4, 2]
  invFun := ![1, 2, 5, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e366 : G where
  toFun := ![3, 0, 2, 1, 4, 5]
  invFun := ![1, 3, 2, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e367 : G where
  toFun := ![3, 0, 2, 1, 5, 4]
  invFun := ![1, 3, 2, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e368 : G where
  toFun := ![3, 0, 2, 4, 1, 5]
  invFun := ![1, 4, 2, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e369 : G where
  toFun := ![3, 0, 2, 4, 5, 1]
  invFun := ![1, 5, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e370 : G where
  toFun := ![3, 0, 2, 5, 1, 4]
  invFun := ![1, 4, 2, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e371 : G where
  toFun := ![3, 0, 2, 5, 4, 1]
  invFun := ![1, 5, 2, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e372 : G where
  toFun := ![3, 0, 4, 1, 2, 5]
  invFun := ![1, 3, 4, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e373 : G where
  toFun := ![3, 0, 4, 1, 5, 2]
  invFun := ![1, 3, 5, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e374 : G where
  toFun := ![3, 0, 4, 2, 1, 5]
  invFun := ![1, 4, 3, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e375 : G where
  toFun := ![3, 0, 4, 2, 5, 1]
  invFun := ![1, 5, 3, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e376 : G where
  toFun := ![3, 0, 4, 5, 1, 2]
  invFun := ![1, 4, 5, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e377 : G where
  toFun := ![3, 0, 4, 5, 2, 1]
  invFun := ![1, 5, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e378 : G where
  toFun := ![3, 0, 5, 1, 2, 4]
  invFun := ![1, 3, 4, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e379 : G where
  toFun := ![3, 0, 5, 1, 4, 2]
  invFun := ![1, 3, 5, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e380 : G where
  toFun := ![3, 0, 5, 2, 1, 4]
  invFun := ![1, 4, 3, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e381 : G where
  toFun := ![3, 0, 5, 2, 4, 1]
  invFun := ![1, 5, 3, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e382 : G where
  toFun := ![3, 0, 5, 4, 1, 2]
  invFun := ![1, 4, 5, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e383 : G where
  toFun := ![3, 0, 5, 4, 2, 1]
  invFun := ![1, 5, 4, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e384 : G where
  toFun := ![3, 1, 0, 2, 4, 5]
  invFun := ![2, 1, 3, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e385 : G where
  toFun := ![3, 1, 0, 2, 5, 4]
  invFun := ![2, 1, 3, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e386 : G where
  toFun := ![3, 1, 0, 4, 2, 5]
  invFun := ![2, 1, 4, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e387 : G where
  toFun := ![3, 1, 0, 4, 5, 2]
  invFun := ![2, 1, 5, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e388 : G where
  toFun := ![3, 1, 0, 5, 2, 4]
  invFun := ![2, 1, 4, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e389 : G where
  toFun := ![3, 1, 0, 5, 4, 2]
  invFun := ![2, 1, 5, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e390 : G where
  toFun := ![3, 1, 2, 0, 4, 5]
  invFun := ![3, 1, 2, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e391 : G where
  toFun := ![3, 1, 2, 0, 5, 4]
  invFun := ![3, 1, 2, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e392 : G where
  toFun := ![3, 1, 2, 4, 0, 5]
  invFun := ![4, 1, 2, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e393 : G where
  toFun := ![3, 1, 2, 4, 5, 0]
  invFun := ![5, 1, 2, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e394 : G where
  toFun := ![3, 1, 2, 5, 0, 4]
  invFun := ![4, 1, 2, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e395 : G where
  toFun := ![3, 1, 2, 5, 4, 0]
  invFun := ![5, 1, 2, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e396 : G where
  toFun := ![3, 1, 4, 0, 2, 5]
  invFun := ![3, 1, 4, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e397 : G where
  toFun := ![3, 1, 4, 0, 5, 2]
  invFun := ![3, 1, 5, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e398 : G where
  toFun := ![3, 1, 4, 2, 0, 5]
  invFun := ![4, 1, 3, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e399 : G where
  toFun := ![3, 1, 4, 2, 5, 0]
  invFun := ![5, 1, 3, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e400 : G where
  toFun := ![3, 1, 4, 5, 0, 2]
  invFun := ![4, 1, 5, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e401 : G where
  toFun := ![3, 1, 4, 5, 2, 0]
  invFun := ![5, 1, 4, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e402 : G where
  toFun := ![3, 1, 5, 0, 2, 4]
  invFun := ![3, 1, 4, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e403 : G where
  toFun := ![3, 1, 5, 0, 4, 2]
  invFun := ![3, 1, 5, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e404 : G where
  toFun := ![3, 1, 5, 2, 0, 4]
  invFun := ![4, 1, 3, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e405 : G where
  toFun := ![3, 1, 5, 2, 4, 0]
  invFun := ![5, 1, 3, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e406 : G where
  toFun := ![3, 1, 5, 4, 0, 2]
  invFun := ![4, 1, 5, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e407 : G where
  toFun := ![3, 1, 5, 4, 2, 0]
  invFun := ![5, 1, 4, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e408 : G where
  toFun := ![3, 2, 0, 1, 4, 5]
  invFun := ![2, 3, 1, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e409 : G where
  toFun := ![3, 2, 0, 1, 5, 4]
  invFun := ![2, 3, 1, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e410 : G where
  toFun := ![3, 2, 0, 4, 1, 5]
  invFun := ![2, 4, 1, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e411 : G where
  toFun := ![3, 2, 0, 4, 5, 1]
  invFun := ![2, 5, 1, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e412 : G where
  toFun := ![3, 2, 0, 5, 1, 4]
  invFun := ![2, 4, 1, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e413 : G where
  toFun := ![3, 2, 0, 5, 4, 1]
  invFun := ![2, 5, 1, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e414 : G where
  toFun := ![3, 2, 1, 0, 4, 5]
  invFun := ![3, 2, 1, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e415 : G where
  toFun := ![3, 2, 1, 0, 5, 4]
  invFun := ![3, 2, 1, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e416 : G where
  toFun := ![3, 2, 1, 4, 0, 5]
  invFun := ![4, 2, 1, 0, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e417 : G where
  toFun := ![3, 2, 1, 4, 5, 0]
  invFun := ![5, 2, 1, 0, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e418 : G where
  toFun := ![3, 2, 1, 5, 0, 4]
  invFun := ![4, 2, 1, 0, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e419 : G where
  toFun := ![3, 2, 1, 5, 4, 0]
  invFun := ![5, 2, 1, 0, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e420 : G where
  toFun := ![3, 2, 4, 0, 1, 5]
  invFun := ![3, 4, 1, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e421 : G where
  toFun := ![3, 2, 4, 0, 5, 1]
  invFun := ![3, 5, 1, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e422 : G where
  toFun := ![3, 2, 4, 1, 0, 5]
  invFun := ![4, 3, 1, 0, 2, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e423 : G where
  toFun := ![3, 2, 4, 1, 5, 0]
  invFun := ![5, 3, 1, 0, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e424 : G where
  toFun := ![3, 2, 4, 5, 0, 1]
  invFun := ![4, 5, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e425 : G where
  toFun := ![3, 2, 4, 5, 1, 0]
  invFun := ![5, 4, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e426 : G where
  toFun := ![3, 2, 5, 0, 1, 4]
  invFun := ![3, 4, 1, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e427 : G where
  toFun := ![3, 2, 5, 0, 4, 1]
  invFun := ![3, 5, 1, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e428 : G where
  toFun := ![3, 2, 5, 1, 0, 4]
  invFun := ![4, 3, 1, 0, 5, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e429 : G where
  toFun := ![3, 2, 5, 1, 4, 0]
  invFun := ![5, 3, 1, 0, 4, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e430 : G where
  toFun := ![3, 2, 5, 4, 0, 1]
  invFun := ![4, 5, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e431 : G where
  toFun := ![3, 2, 5, 4, 1, 0]
  invFun := ![5, 4, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e432 : G where
  toFun := ![3, 4, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e433 : G where
  toFun := ![3, 4, 0, 1, 5, 2]
  invFun := ![2, 3, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e434 : G where
  toFun := ![3, 4, 0, 2, 1, 5]
  invFun := ![2, 4, 3, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e435 : G where
  toFun := ![3, 4, 0, 2, 5, 1]
  invFun := ![2, 5, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e436 : G where
  toFun := ![3, 4, 0, 5, 1, 2]
  invFun := ![2, 4, 5, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e437 : G where
  toFun := ![3, 4, 0, 5, 2, 1]
  invFun := ![2, 5, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e438 : G where
  toFun := ![3, 4, 1, 0, 2, 5]
  invFun := ![3, 2, 4, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e439 : G where
  toFun := ![3, 4, 1, 0, 5, 2]
  invFun := ![3, 2, 5, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e440 : G where
  toFun := ![3, 4, 1, 2, 0, 5]
  invFun := ![4, 2, 3, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e441 : G where
  toFun := ![3, 4, 1, 2, 5, 0]
  invFun := ![5, 2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e442 : G where
  toFun := ![3, 4, 1, 5, 0, 2]
  invFun := ![4, 2, 5, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e443 : G where
  toFun := ![3, 4, 1, 5, 2, 0]
  invFun := ![5, 2, 4, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e444 : G where
  toFun := ![3, 4, 2, 0, 1, 5]
  invFun := ![3, 4, 2, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e445 : G where
  toFun := ![3, 4, 2, 0, 5, 1]
  invFun := ![3, 5, 2, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e446 : G where
  toFun := ![3, 4, 2, 1, 0, 5]
  invFun := ![4, 3, 2, 0, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e447 : G where
  toFun := ![3, 4, 2, 1, 5, 0]
  invFun := ![5, 3, 2, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e448 : G where
  toFun := ![3, 4, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e449 : G where
  toFun := ![3, 4, 2, 5, 1, 0]
  invFun := ![5, 4, 2, 0, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e450 : G where
  toFun := ![3, 4, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e451 : G where
  toFun := ![3, 4, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e452 : G where
  toFun := ![3, 4, 5, 1, 0, 2]
  invFun := ![4, 3, 5, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e453 : G where
  toFun := ![3, 4, 5, 1, 2, 0]
  invFun := ![5, 3, 4, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e454 : G where
  toFun := ![3, 4, 5, 2, 0, 1]
  invFun := ![4, 5, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e455 : G where
  toFun := ![3, 4, 5, 2, 1, 0]
  invFun := ![5, 4, 3, 0, 1, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e456 : G where
  toFun := ![3, 5, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e457 : G where
  toFun := ![3, 5, 0, 1, 4, 2]
  invFun := ![2, 3, 5, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e458 : G where
  toFun := ![3, 5, 0, 2, 1, 4]
  invFun := ![2, 4, 3, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e459 : G where
  toFun := ![3, 5, 0, 2, 4, 1]
  invFun := ![2, 5, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e460 : G where
  toFun := ![3, 5, 0, 4, 1, 2]
  invFun := ![2, 4, 5, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e461 : G where
  toFun := ![3, 5, 0, 4, 2, 1]
  invFun := ![2, 5, 4, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e462 : G where
  toFun := ![3, 5, 1, 0, 2, 4]
  invFun := ![3, 2, 4, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e463 : G where
  toFun := ![3, 5, 1, 0, 4, 2]
  invFun := ![3, 2, 5, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e464 : G where
  toFun := ![3, 5, 1, 2, 0, 4]
  invFun := ![4, 2, 3, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e465 : G where
  toFun := ![3, 5, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e466 : G where
  toFun := ![3, 5, 1, 4, 0, 2]
  invFun := ![4, 2, 5, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e467 : G where
  toFun := ![3, 5, 1, 4, 2, 0]
  invFun := ![5, 2, 4, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e468 : G where
  toFun := ![3, 5, 2, 0, 1, 4]
  invFun := ![3, 4, 2, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e469 : G where
  toFun := ![3, 5, 2, 0, 4, 1]
  invFun := ![3, 5, 2, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e470 : G where
  toFun := ![3, 5, 2, 1, 0, 4]
  invFun := ![4, 3, 2, 0, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e471 : G where
  toFun := ![3, 5, 2, 1, 4, 0]
  invFun := ![5, 3, 2, 0, 4, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e472 : G where
  toFun := ![3, 5, 2, 4, 0, 1]
  invFun := ![4, 5, 2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e473 : G where
  toFun := ![3, 5, 2, 4, 1, 0]
  invFun := ![5, 4, 2, 0, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e474 : G where
  toFun := ![3, 5, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e475 : G where
  toFun := ![3, 5, 4, 0, 2, 1]
  invFun := ![3, 5, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e476 : G where
  toFun := ![3, 5, 4, 1, 0, 2]
  invFun := ![4, 3, 5, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e477 : G where
  toFun := ![3, 5, 4, 1, 2, 0]
  invFun := ![5, 3, 4, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e478 : G where
  toFun := ![3, 5, 4, 2, 0, 1]
  invFun := ![4, 5, 3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e479 : G where
  toFun := ![3, 5, 4, 2, 1, 0]
  invFun := ![5, 4, 3, 0, 2, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e480 : G where
  toFun := ![4, 0, 1, 2, 3, 5]
  invFun := ![1, 2, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e481 : G where
  toFun := ![4, 0, 1, 2, 5, 3]
  invFun := ![1, 2, 3, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e482 : G where
  toFun := ![4, 0, 1, 3, 2, 5]
  invFun := ![1, 2, 4, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e483 : G where
  toFun := ![4, 0, 1, 3, 5, 2]
  invFun := ![1, 2, 5, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e484 : G where
  toFun := ![4, 0, 1, 5, 2, 3]
  invFun := ![1, 2, 4, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e485 : G where
  toFun := ![4, 0, 1, 5, 3, 2]
  invFun := ![1, 2, 5, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e486 : G where
  toFun := ![4, 0, 2, 1, 3, 5]
  invFun := ![1, 3, 2, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e487 : G where
  toFun := ![4, 0, 2, 1, 5, 3]
  invFun := ![1, 3, 2, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e488 : G where
  toFun := ![4, 0, 2, 3, 1, 5]
  invFun := ![1, 4, 2, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e489 : G where
  toFun := ![4, 0, 2, 3, 5, 1]
  invFun := ![1, 5, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e490 : G where
  toFun := ![4, 0, 2, 5, 1, 3]
  invFun := ![1, 4, 2, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e491 : G where
  toFun := ![4, 0, 2, 5, 3, 1]
  invFun := ![1, 5, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e492 : G where
  toFun := ![4, 0, 3, 1, 2, 5]
  invFun := ![1, 3, 4, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e493 : G where
  toFun := ![4, 0, 3, 1, 5, 2]
  invFun := ![1, 3, 5, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e494 : G where
  toFun := ![4, 0, 3, 2, 1, 5]
  invFun := ![1, 4, 3, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e495 : G where
  toFun := ![4, 0, 3, 2, 5, 1]
  invFun := ![1, 5, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e496 : G where
  toFun := ![4, 0, 3, 5, 1, 2]
  invFun := ![1, 4, 5, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e497 : G where
  toFun := ![4, 0, 3, 5, 2, 1]
  invFun := ![1, 5, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e498 : G where
  toFun := ![4, 0, 5, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e499 : G where
  toFun := ![4, 0, 5, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e500 : G where
  toFun := ![4, 0, 5, 2, 1, 3]
  invFun := ![1, 4, 3, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e501 : G where
  toFun := ![4, 0, 5, 2, 3, 1]
  invFun := ![1, 5, 3, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e502 : G where
  toFun := ![4, 0, 5, 3, 1, 2]
  invFun := ![1, 4, 5, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e503 : G where
  toFun := ![4, 0, 5, 3, 2, 1]
  invFun := ![1, 5, 4, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e504 : G where
  toFun := ![4, 1, 0, 2, 3, 5]
  invFun := ![2, 1, 3, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e505 : G where
  toFun := ![4, 1, 0, 2, 5, 3]
  invFun := ![2, 1, 3, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e506 : G where
  toFun := ![4, 1, 0, 3, 2, 5]
  invFun := ![2, 1, 4, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e507 : G where
  toFun := ![4, 1, 0, 3, 5, 2]
  invFun := ![2, 1, 5, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e508 : G where
  toFun := ![4, 1, 0, 5, 2, 3]
  invFun := ![2, 1, 4, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e509 : G where
  toFun := ![4, 1, 0, 5, 3, 2]
  invFun := ![2, 1, 5, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e510 : G where
  toFun := ![4, 1, 2, 0, 3, 5]
  invFun := ![3, 1, 2, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e511 : G where
  toFun := ![4, 1, 2, 0, 5, 3]
  invFun := ![3, 1, 2, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e512 : G where
  toFun := ![4, 1, 2, 3, 0, 5]
  invFun := ![4, 1, 2, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e513 : G where
  toFun := ![4, 1, 2, 3, 5, 0]
  invFun := ![5, 1, 2, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e514 : G where
  toFun := ![4, 1, 2, 5, 0, 3]
  invFun := ![4, 1, 2, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e515 : G where
  toFun := ![4, 1, 2, 5, 3, 0]
  invFun := ![5, 1, 2, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e516 : G where
  toFun := ![4, 1, 3, 0, 2, 5]
  invFun := ![3, 1, 4, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e517 : G where
  toFun := ![4, 1, 3, 0, 5, 2]
  invFun := ![3, 1, 5, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e518 : G where
  toFun := ![4, 1, 3, 2, 0, 5]
  invFun := ![4, 1, 3, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e519 : G where
  toFun := ![4, 1, 3, 2, 5, 0]
  invFun := ![5, 1, 3, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e520 : G where
  toFun := ![4, 1, 3, 5, 0, 2]
  invFun := ![4, 1, 5, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e521 : G where
  toFun := ![4, 1, 3, 5, 2, 0]
  invFun := ![5, 1, 4, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e522 : G where
  toFun := ![4, 1, 5, 0, 2, 3]
  invFun := ![3, 1, 4, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e523 : G where
  toFun := ![4, 1, 5, 0, 3, 2]
  invFun := ![3, 1, 5, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e524 : G where
  toFun := ![4, 1, 5, 2, 0, 3]
  invFun := ![4, 1, 3, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e525 : G where
  toFun := ![4, 1, 5, 2, 3, 0]
  invFun := ![5, 1, 3, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e526 : G where
  toFun := ![4, 1, 5, 3, 0, 2]
  invFun := ![4, 1, 5, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e527 : G where
  toFun := ![4, 1, 5, 3, 2, 0]
  invFun := ![5, 1, 4, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e528 : G where
  toFun := ![4, 2, 0, 1, 3, 5]
  invFun := ![2, 3, 1, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e529 : G where
  toFun := ![4, 2, 0, 1, 5, 3]
  invFun := ![2, 3, 1, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e530 : G where
  toFun := ![4, 2, 0, 3, 1, 5]
  invFun := ![2, 4, 1, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e531 : G where
  toFun := ![4, 2, 0, 3, 5, 1]
  invFun := ![2, 5, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e532 : G where
  toFun := ![4, 2, 0, 5, 1, 3]
  invFun := ![2, 4, 1, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e533 : G where
  toFun := ![4, 2, 0, 5, 3, 1]
  invFun := ![2, 5, 1, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e534 : G where
  toFun := ![4, 2, 1, 0, 3, 5]
  invFun := ![3, 2, 1, 4, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e535 : G where
  toFun := ![4, 2, 1, 0, 5, 3]
  invFun := ![3, 2, 1, 5, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e536 : G where
  toFun := ![4, 2, 1, 3, 0, 5]
  invFun := ![4, 2, 1, 3, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e537 : G where
  toFun := ![4, 2, 1, 3, 5, 0]
  invFun := ![5, 2, 1, 3, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e538 : G where
  toFun := ![4, 2, 1, 5, 0, 3]
  invFun := ![4, 2, 1, 5, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e539 : G where
  toFun := ![4, 2, 1, 5, 3, 0]
  invFun := ![5, 2, 1, 4, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e540 : G where
  toFun := ![4, 2, 3, 0, 1, 5]
  invFun := ![3, 4, 1, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e541 : G where
  toFun := ![4, 2, 3, 0, 5, 1]
  invFun := ![3, 5, 1, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e542 : G where
  toFun := ![4, 2, 3, 1, 0, 5]
  invFun := ![4, 3, 1, 2, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e543 : G where
  toFun := ![4, 2, 3, 1, 5, 0]
  invFun := ![5, 3, 1, 2, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e544 : G where
  toFun := ![4, 2, 3, 5, 0, 1]
  invFun := ![4, 5, 1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e545 : G where
  toFun := ![4, 2, 3, 5, 1, 0]
  invFun := ![5, 4, 1, 2, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e546 : G where
  toFun := ![4, 2, 5, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e547 : G where
  toFun := ![4, 2, 5, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e548 : G where
  toFun := ![4, 2, 5, 1, 0, 3]
  invFun := ![4, 3, 1, 5, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e549 : G where
  toFun := ![4, 2, 5, 1, 3, 0]
  invFun := ![5, 3, 1, 4, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e550 : G where
  toFun := ![4, 2, 5, 3, 0, 1]
  invFun := ![4, 5, 1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e551 : G where
  toFun := ![4, 2, 5, 3, 1, 0]
  invFun := ![5, 4, 1, 3, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e552 : G where
  toFun := ![4, 3, 0, 1, 2, 5]
  invFun := ![2, 3, 4, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e553 : G where
  toFun := ![4, 3, 0, 1, 5, 2]
  invFun := ![2, 3, 5, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e554 : G where
  toFun := ![4, 3, 0, 2, 1, 5]
  invFun := ![2, 4, 3, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e555 : G where
  toFun := ![4, 3, 0, 2, 5, 1]
  invFun := ![2, 5, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e556 : G where
  toFun := ![4, 3, 0, 5, 1, 2]
  invFun := ![2, 4, 5, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e557 : G where
  toFun := ![4, 3, 0, 5, 2, 1]
  invFun := ![2, 5, 4, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e558 : G where
  toFun := ![4, 3, 1, 0, 2, 5]
  invFun := ![3, 2, 4, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e559 : G where
  toFun := ![4, 3, 1, 0, 5, 2]
  invFun := ![3, 2, 5, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e560 : G where
  toFun := ![4, 3, 1, 2, 0, 5]
  invFun := ![4, 2, 3, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e561 : G where
  toFun := ![4, 3, 1, 2, 5, 0]
  invFun := ![5, 2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e562 : G where
  toFun := ![4, 3, 1, 5, 0, 2]
  invFun := ![4, 2, 5, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e563 : G where
  toFun := ![4, 3, 1, 5, 2, 0]
  invFun := ![5, 2, 4, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e564 : G where
  toFun := ![4, 3, 2, 0, 1, 5]
  invFun := ![3, 4, 2, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e565 : G where
  toFun := ![4, 3, 2, 0, 5, 1]
  invFun := ![3, 5, 2, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e566 : G where
  toFun := ![4, 3, 2, 1, 0, 5]
  invFun := ![4, 3, 2, 1, 0, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e567 : G where
  toFun := ![4, 3, 2, 1, 5, 0]
  invFun := ![5, 3, 2, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e568 : G where
  toFun := ![4, 3, 2, 5, 0, 1]
  invFun := ![4, 5, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e569 : G where
  toFun := ![4, 3, 2, 5, 1, 0]
  invFun := ![5, 4, 2, 1, 0, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e570 : G where
  toFun := ![4, 3, 5, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e571 : G where
  toFun := ![4, 3, 5, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e572 : G where
  toFun := ![4, 3, 5, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e573 : G where
  toFun := ![4, 3, 5, 1, 2, 0]
  invFun := ![5, 3, 4, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e574 : G where
  toFun := ![4, 3, 5, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e575 : G where
  toFun := ![4, 3, 5, 2, 1, 0]
  invFun := ![5, 4, 3, 1, 0, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e576 : G where
  toFun := ![4, 5, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e577 : G where
  toFun := ![4, 5, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e578 : G where
  toFun := ![4, 5, 0, 2, 1, 3]
  invFun := ![2, 4, 3, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e579 : G where
  toFun := ![4, 5, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e580 : G where
  toFun := ![4, 5, 0, 3, 1, 2]
  invFun := ![2, 4, 5, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e581 : G where
  toFun := ![4, 5, 0, 3, 2, 1]
  invFun := ![2, 5, 4, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e582 : G where
  toFun := ![4, 5, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e583 : G where
  toFun := ![4, 5, 1, 0, 3, 2]
  invFun := ![3, 2, 5, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e584 : G where
  toFun := ![4, 5, 1, 2, 0, 3]
  invFun := ![4, 2, 3, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e585 : G where
  toFun := ![4, 5, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e586 : G where
  toFun := ![4, 5, 1, 3, 0, 2]
  invFun := ![4, 2, 5, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e587 : G where
  toFun := ![4, 5, 1, 3, 2, 0]
  invFun := ![5, 2, 4, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e588 : G where
  toFun := ![4, 5, 2, 0, 1, 3]
  invFun := ![3, 4, 2, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e589 : G where
  toFun := ![4, 5, 2, 0, 3, 1]
  invFun := ![3, 5, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e590 : G where
  toFun := ![4, 5, 2, 1, 0, 3]
  invFun := ![4, 3, 2, 5, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e591 : G where
  toFun := ![4, 5, 2, 1, 3, 0]
  invFun := ![5, 3, 2, 4, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e592 : G where
  toFun := ![4, 5, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e593 : G where
  toFun := ![4, 5, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e594 : G where
  toFun := ![4, 5, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e595 : G where
  toFun := ![4, 5, 3, 0, 2, 1]
  invFun := ![3, 5, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e596 : G where
  toFun := ![4, 5, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e597 : G where
  toFun := ![4, 5, 3, 1, 2, 0]
  invFun := ![5, 3, 4, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e598 : G where
  toFun := ![4, 5, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e599 : G where
  toFun := ![4, 5, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e600 : G where
  toFun := ![5, 0, 1, 2, 3, 4]
  invFun := ![1, 2, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e601 : G where
  toFun := ![5, 0, 1, 2, 4, 3]
  invFun := ![1, 2, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e602 : G where
  toFun := ![5, 0, 1, 3, 2, 4]
  invFun := ![1, 2, 4, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e603 : G where
  toFun := ![5, 0, 1, 3, 4, 2]
  invFun := ![1, 2, 5, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e604 : G where
  toFun := ![5, 0, 1, 4, 2, 3]
  invFun := ![1, 2, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e605 : G where
  toFun := ![5, 0, 1, 4, 3, 2]
  invFun := ![1, 2, 5, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e606 : G where
  toFun := ![5, 0, 2, 1, 3, 4]
  invFun := ![1, 3, 2, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e607 : G where
  toFun := ![5, 0, 2, 1, 4, 3]
  invFun := ![1, 3, 2, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e608 : G where
  toFun := ![5, 0, 2, 3, 1, 4]
  invFun := ![1, 4, 2, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e609 : G where
  toFun := ![5, 0, 2, 3, 4, 1]
  invFun := ![1, 5, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e610 : G where
  toFun := ![5, 0, 2, 4, 1, 3]
  invFun := ![1, 4, 2, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e611 : G where
  toFun := ![5, 0, 2, 4, 3, 1]
  invFun := ![1, 5, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e612 : G where
  toFun := ![5, 0, 3, 1, 2, 4]
  invFun := ![1, 3, 4, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e613 : G where
  toFun := ![5, 0, 3, 1, 4, 2]
  invFun := ![1, 3, 5, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e614 : G where
  toFun := ![5, 0, 3, 2, 1, 4]
  invFun := ![1, 4, 3, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e615 : G where
  toFun := ![5, 0, 3, 2, 4, 1]
  invFun := ![1, 5, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e616 : G where
  toFun := ![5, 0, 3, 4, 1, 2]
  invFun := ![1, 4, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e617 : G where
  toFun := ![5, 0, 3, 4, 2, 1]
  invFun := ![1, 5, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e618 : G where
  toFun := ![5, 0, 4, 1, 2, 3]
  invFun := ![1, 3, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e619 : G where
  toFun := ![5, 0, 4, 1, 3, 2]
  invFun := ![1, 3, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e620 : G where
  toFun := ![5, 0, 4, 2, 1, 3]
  invFun := ![1, 4, 3, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e621 : G where
  toFun := ![5, 0, 4, 2, 3, 1]
  invFun := ![1, 5, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e622 : G where
  toFun := ![5, 0, 4, 3, 1, 2]
  invFun := ![1, 4, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e623 : G where
  toFun := ![5, 0, 4, 3, 2, 1]
  invFun := ![1, 5, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e624 : G where
  toFun := ![5, 1, 0, 2, 3, 4]
  invFun := ![2, 1, 3, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e625 : G where
  toFun := ![5, 1, 0, 2, 4, 3]
  invFun := ![2, 1, 3, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e626 : G where
  toFun := ![5, 1, 0, 3, 2, 4]
  invFun := ![2, 1, 4, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e627 : G where
  toFun := ![5, 1, 0, 3, 4, 2]
  invFun := ![2, 1, 5, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e628 : G where
  toFun := ![5, 1, 0, 4, 2, 3]
  invFun := ![2, 1, 4, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e629 : G where
  toFun := ![5, 1, 0, 4, 3, 2]
  invFun := ![2, 1, 5, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e630 : G where
  toFun := ![5, 1, 2, 0, 3, 4]
  invFun := ![3, 1, 2, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e631 : G where
  toFun := ![5, 1, 2, 0, 4, 3]
  invFun := ![3, 1, 2, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e632 : G where
  toFun := ![5, 1, 2, 3, 0, 4]
  invFun := ![4, 1, 2, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e633 : G where
  toFun := ![5, 1, 2, 3, 4, 0]
  invFun := ![5, 1, 2, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e634 : G where
  toFun := ![5, 1, 2, 4, 0, 3]
  invFun := ![4, 1, 2, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e635 : G where
  toFun := ![5, 1, 2, 4, 3, 0]
  invFun := ![5, 1, 2, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e636 : G where
  toFun := ![5, 1, 3, 0, 2, 4]
  invFun := ![3, 1, 4, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e637 : G where
  toFun := ![5, 1, 3, 0, 4, 2]
  invFun := ![3, 1, 5, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e638 : G where
  toFun := ![5, 1, 3, 2, 0, 4]
  invFun := ![4, 1, 3, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e639 : G where
  toFun := ![5, 1, 3, 2, 4, 0]
  invFun := ![5, 1, 3, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e640 : G where
  toFun := ![5, 1, 3, 4, 0, 2]
  invFun := ![4, 1, 5, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e641 : G where
  toFun := ![5, 1, 3, 4, 2, 0]
  invFun := ![5, 1, 4, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e642 : G where
  toFun := ![5, 1, 4, 0, 2, 3]
  invFun := ![3, 1, 4, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e643 : G where
  toFun := ![5, 1, 4, 0, 3, 2]
  invFun := ![3, 1, 5, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e644 : G where
  toFun := ![5, 1, 4, 2, 0, 3]
  invFun := ![4, 1, 3, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e645 : G where
  toFun := ![5, 1, 4, 2, 3, 0]
  invFun := ![5, 1, 3, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e646 : G where
  toFun := ![5, 1, 4, 3, 0, 2]
  invFun := ![4, 1, 5, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e647 : G where
  toFun := ![5, 1, 4, 3, 2, 0]
  invFun := ![5, 1, 4, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e648 : G where
  toFun := ![5, 2, 0, 1, 3, 4]
  invFun := ![2, 3, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e649 : G where
  toFun := ![5, 2, 0, 1, 4, 3]
  invFun := ![2, 3, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e650 : G where
  toFun := ![5, 2, 0, 3, 1, 4]
  invFun := ![2, 4, 1, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e651 : G where
  toFun := ![5, 2, 0, 3, 4, 1]
  invFun := ![2, 5, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e652 : G where
  toFun := ![5, 2, 0, 4, 1, 3]
  invFun := ![2, 4, 1, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e653 : G where
  toFun := ![5, 2, 0, 4, 3, 1]
  invFun := ![2, 5, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e654 : G where
  toFun := ![5, 2, 1, 0, 3, 4]
  invFun := ![3, 2, 1, 4, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e655 : G where
  toFun := ![5, 2, 1, 0, 4, 3]
  invFun := ![3, 2, 1, 5, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e656 : G where
  toFun := ![5, 2, 1, 3, 0, 4]
  invFun := ![4, 2, 1, 3, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e657 : G where
  toFun := ![5, 2, 1, 3, 4, 0]
  invFun := ![5, 2, 1, 3, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e658 : G where
  toFun := ![5, 2, 1, 4, 0, 3]
  invFun := ![4, 2, 1, 5, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e659 : G where
  toFun := ![5, 2, 1, 4, 3, 0]
  invFun := ![5, 2, 1, 4, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e660 : G where
  toFun := ![5, 2, 3, 0, 1, 4]
  invFun := ![3, 4, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e661 : G where
  toFun := ![5, 2, 3, 0, 4, 1]
  invFun := ![3, 5, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e662 : G where
  toFun := ![5, 2, 3, 1, 0, 4]
  invFun := ![4, 3, 1, 2, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e663 : G where
  toFun := ![5, 2, 3, 1, 4, 0]
  invFun := ![5, 3, 1, 2, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e664 : G where
  toFun := ![5, 2, 3, 4, 0, 1]
  invFun := ![4, 5, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e665 : G where
  toFun := ![5, 2, 3, 4, 1, 0]
  invFun := ![5, 4, 1, 2, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e666 : G where
  toFun := ![5, 2, 4, 0, 1, 3]
  invFun := ![3, 4, 1, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e667 : G where
  toFun := ![5, 2, 4, 0, 3, 1]
  invFun := ![3, 5, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e668 : G where
  toFun := ![5, 2, 4, 1, 0, 3]
  invFun := ![4, 3, 1, 5, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e669 : G where
  toFun := ![5, 2, 4, 1, 3, 0]
  invFun := ![5, 3, 1, 4, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e670 : G where
  toFun := ![5, 2, 4, 3, 0, 1]
  invFun := ![4, 5, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e671 : G where
  toFun := ![5, 2, 4, 3, 1, 0]
  invFun := ![5, 4, 1, 3, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e672 : G where
  toFun := ![5, 3, 0, 1, 2, 4]
  invFun := ![2, 3, 4, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e673 : G where
  toFun := ![5, 3, 0, 1, 4, 2]
  invFun := ![2, 3, 5, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e674 : G where
  toFun := ![5, 3, 0, 2, 1, 4]
  invFun := ![2, 4, 3, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e675 : G where
  toFun := ![5, 3, 0, 2, 4, 1]
  invFun := ![2, 5, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e676 : G where
  toFun := ![5, 3, 0, 4, 1, 2]
  invFun := ![2, 4, 5, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e677 : G where
  toFun := ![5, 3, 0, 4, 2, 1]
  invFun := ![2, 5, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e678 : G where
  toFun := ![5, 3, 1, 0, 2, 4]
  invFun := ![3, 2, 4, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e679 : G where
  toFun := ![5, 3, 1, 0, 4, 2]
  invFun := ![3, 2, 5, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e680 : G where
  toFun := ![5, 3, 1, 2, 0, 4]
  invFun := ![4, 2, 3, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e681 : G where
  toFun := ![5, 3, 1, 2, 4, 0]
  invFun := ![5, 2, 3, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e682 : G where
  toFun := ![5, 3, 1, 4, 0, 2]
  invFun := ![4, 2, 5, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e683 : G where
  toFun := ![5, 3, 1, 4, 2, 0]
  invFun := ![5, 2, 4, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e684 : G where
  toFun := ![5, 3, 2, 0, 1, 4]
  invFun := ![3, 4, 2, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e685 : G where
  toFun := ![5, 3, 2, 0, 4, 1]
  invFun := ![3, 5, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e686 : G where
  toFun := ![5, 3, 2, 1, 0, 4]
  invFun := ![4, 3, 2, 1, 5, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e687 : G where
  toFun := ![5, 3, 2, 1, 4, 0]
  invFun := ![5, 3, 2, 1, 4, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e688 : G where
  toFun := ![5, 3, 2, 4, 0, 1]
  invFun := ![4, 5, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e689 : G where
  toFun := ![5, 3, 2, 4, 1, 0]
  invFun := ![5, 4, 2, 1, 3, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e690 : G where
  toFun := ![5, 3, 4, 0, 1, 2]
  invFun := ![3, 4, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e691 : G where
  toFun := ![5, 3, 4, 0, 2, 1]
  invFun := ![3, 5, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e692 : G where
  toFun := ![5, 3, 4, 1, 0, 2]
  invFun := ![4, 3, 5, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e693 : G where
  toFun := ![5, 3, 4, 1, 2, 0]
  invFun := ![5, 3, 4, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e694 : G where
  toFun := ![5, 3, 4, 2, 0, 1]
  invFun := ![4, 5, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e695 : G where
  toFun := ![5, 3, 4, 2, 1, 0]
  invFun := ![5, 4, 3, 1, 2, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e696 : G where
  toFun := ![5, 4, 0, 1, 2, 3]
  invFun := ![2, 3, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e697 : G where
  toFun := ![5, 4, 0, 1, 3, 2]
  invFun := ![2, 3, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e698 : G where
  toFun := ![5, 4, 0, 2, 1, 3]
  invFun := ![2, 4, 3, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e699 : G where
  toFun := ![5, 4, 0, 2, 3, 1]
  invFun := ![2, 5, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e700 : G where
  toFun := ![5, 4, 0, 3, 1, 2]
  invFun := ![2, 4, 5, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e701 : G where
  toFun := ![5, 4, 0, 3, 2, 1]
  invFun := ![2, 5, 4, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e702 : G where
  toFun := ![5, 4, 1, 0, 2, 3]
  invFun := ![3, 2, 4, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e703 : G where
  toFun := ![5, 4, 1, 0, 3, 2]
  invFun := ![3, 2, 5, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e704 : G where
  toFun := ![5, 4, 1, 2, 0, 3]
  invFun := ![4, 2, 3, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e705 : G where
  toFun := ![5, 4, 1, 2, 3, 0]
  invFun := ![5, 2, 3, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e706 : G where
  toFun := ![5, 4, 1, 3, 0, 2]
  invFun := ![4, 2, 5, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e707 : G where
  toFun := ![5, 4, 1, 3, 2, 0]
  invFun := ![5, 2, 4, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e708 : G where
  toFun := ![5, 4, 2, 0, 1, 3]
  invFun := ![3, 4, 2, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e709 : G where
  toFun := ![5, 4, 2, 0, 3, 1]
  invFun := ![3, 5, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e710 : G where
  toFun := ![5, 4, 2, 1, 0, 3]
  invFun := ![4, 3, 2, 5, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e711 : G where
  toFun := ![5, 4, 2, 1, 3, 0]
  invFun := ![5, 3, 2, 4, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e712 : G where
  toFun := ![5, 4, 2, 3, 0, 1]
  invFun := ![4, 5, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e713 : G where
  toFun := ![5, 4, 2, 3, 1, 0]
  invFun := ![5, 4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e714 : G where
  toFun := ![5, 4, 3, 0, 1, 2]
  invFun := ![3, 4, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e715 : G where
  toFun := ![5, 4, 3, 0, 2, 1]
  invFun := ![3, 5, 4, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e716 : G where
  toFun := ![5, 4, 3, 1, 0, 2]
  invFun := ![4, 3, 5, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e717 : G where
  toFun := ![5, 4, 3, 1, 2, 0]
  invFun := ![5, 3, 4, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e718 : G where
  toFun := ![5, 4, 3, 2, 0, 1]
  invFun := ![4, 5, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e719 : G where
  toFun := ![5, 4, 3, 2, 1, 0]
  invFun := ![5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def chunk00 : List G :=
  [e0, e1, e2, e3, e4, e5, e6, e7, e8, e9,
   e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
   e20, e21, e22, e23]

def chunk01 : List G :=
  [e24, e25, e26, e27, e28, e29, e30, e31, e32, e33,
   e34, e35, e36, e37, e38, e39, e40, e41, e42, e43,
   e44, e45, e46, e47]

def chunk02 : List G :=
  [e48, e49, e50, e51, e52, e53, e54, e55, e56, e57,
   e58, e59, e60, e61, e62, e63, e64, e65, e66, e67,
   e68, e69, e70, e71]

def chunk03 : List G :=
  [e72, e73, e74, e75, e76, e77, e78, e79, e80, e81,
   e82, e83, e84, e85, e86, e87, e88, e89, e90, e91,
   e92, e93, e94, e95]

def chunk04 : List G :=
  [e96, e97, e98, e99, e100, e101, e102, e103, e104, e105,
   e106, e107, e108, e109, e110, e111, e112, e113, e114, e115,
   e116, e117, e118, e119]

def chunk05 : List G :=
  [e120, e121, e122, e123, e124, e125, e126, e127, e128, e129,
   e130, e131, e132, e133, e134, e135, e136, e137, e138, e139,
   e140, e141, e142, e143]

def chunk06 : List G :=
  [e144, e145, e146, e147, e148, e149, e150, e151, e152, e153,
   e154, e155, e156, e157, e158, e159, e160, e161, e162, e163,
   e164, e165, e166, e167]

def chunk07 : List G :=
  [e168, e169, e170, e171, e172, e173, e174, e175, e176, e177,
   e178, e179, e180, e181, e182, e183, e184, e185, e186, e187,
   e188, e189, e190, e191]

def chunk08 : List G :=
  [e192, e193, e194, e195, e196, e197, e198, e199, e200, e201,
   e202, e203, e204, e205, e206, e207, e208, e209, e210, e211,
   e212, e213, e214, e215]

def chunk09 : List G :=
  [e216, e217, e218, e219, e220, e221, e222, e223, e224, e225,
   e226, e227, e228, e229, e230, e231, e232, e233, e234, e235,
   e236, e237, e238, e239]

def chunk10 : List G :=
  [e240, e241, e242, e243, e244, e245, e246, e247, e248, e249,
   e250, e251, e252, e253, e254, e255, e256, e257, e258, e259,
   e260, e261, e262, e263]

def chunk11 : List G :=
  [e264, e265, e266, e267, e268, e269, e270, e271, e272, e273,
   e274, e275, e276, e277, e278, e279, e280, e281, e282, e283,
   e284, e285, e286, e287]

def chunk12 : List G :=
  [e288, e289, e290, e291, e292, e293, e294, e295, e296, e297,
   e298, e299, e300, e301, e302, e303, e304, e305, e306, e307,
   e308, e309, e310, e311]

def chunk13 : List G :=
  [e312, e313, e314, e315, e316, e317, e318, e319, e320, e321,
   e322, e323, e324, e325, e326, e327, e328, e329, e330, e331,
   e332, e333, e334, e335]

def chunk14 : List G :=
  [e336, e337, e338, e339, e340, e341, e342, e343, e344, e345,
   e346, e347, e348, e349, e350, e351, e352, e353, e354, e355,
   e356, e357, e358, e359]

def chunk15 : List G :=
  [e360, e361, e362, e363, e364, e365, e366, e367, e368, e369,
   e370, e371, e372, e373, e374, e375, e376, e377, e378, e379,
   e380, e381, e382, e383]

def chunk16 : List G :=
  [e384, e385, e386, e387, e388, e389, e390, e391, e392, e393,
   e394, e395, e396, e397, e398, e399, e400, e401, e402, e403,
   e404, e405, e406, e407]

def chunk17 : List G :=
  [e408, e409, e410, e411, e412, e413, e414, e415, e416, e417,
   e418, e419, e420, e421, e422, e423, e424, e425, e426, e427,
   e428, e429, e430, e431]

def chunk18 : List G :=
  [e432, e433, e434, e435, e436, e437, e438, e439, e440, e441,
   e442, e443, e444, e445, e446, e447, e448, e449, e450, e451,
   e452, e453, e454, e455]

def chunk19 : List G :=
  [e456, e457, e458, e459, e460, e461, e462, e463, e464, e465,
   e466, e467, e468, e469, e470, e471, e472, e473, e474, e475,
   e476, e477, e478, e479]

def chunk20 : List G :=
  [e480, e481, e482, e483, e484, e485, e486, e487, e488, e489,
   e490, e491, e492, e493, e494, e495, e496, e497, e498, e499,
   e500, e501, e502, e503]

def chunk21 : List G :=
  [e504, e505, e506, e507, e508, e509, e510, e511, e512, e513,
   e514, e515, e516, e517, e518, e519, e520, e521, e522, e523,
   e524, e525, e526, e527]

def chunk22 : List G :=
  [e528, e529, e530, e531, e532, e533, e534, e535, e536, e537,
   e538, e539, e540, e541, e542, e543, e544, e545, e546, e547,
   e548, e549, e550, e551]

def chunk23 : List G :=
  [e552, e553, e554, e555, e556, e557, e558, e559, e560, e561,
   e562, e563, e564, e565, e566, e567, e568, e569, e570, e571,
   e572, e573, e574, e575]

def chunk24 : List G :=
  [e576, e577, e578, e579, e580, e581, e582, e583, e584, e585,
   e586, e587, e588, e589, e590, e591, e592, e593, e594, e595,
   e596, e597, e598, e599]

def chunk25 : List G :=
  [e600, e601, e602, e603, e604, e605, e606, e607, e608, e609,
   e610, e611, e612, e613, e614, e615, e616, e617, e618, e619,
   e620, e621, e622, e623]

def chunk26 : List G :=
  [e624, e625, e626, e627, e628, e629, e630, e631, e632, e633,
   e634, e635, e636, e637, e638, e639, e640, e641, e642, e643,
   e644, e645, e646, e647]

def chunk27 : List G :=
  [e648, e649, e650, e651, e652, e653, e654, e655, e656, e657,
   e658, e659, e660, e661, e662, e663, e664, e665, e666, e667,
   e668, e669, e670, e671]

def chunk28 : List G :=
  [e672, e673, e674, e675, e676, e677, e678, e679, e680, e681,
   e682, e683, e684, e685, e686, e687, e688, e689, e690, e691,
   e692, e693, e694, e695]

def chunk29 : List G :=
  [e696, e697, e698, e699, e700, e701, e702, e703, e704, e705,
   e706, e707, e708, e709, e710, e711, e712, e713, e714, e715,
   e716, e717, e718, e719]

def elements : List G :=
  chunk00 ++
  chunk01 ++
  chunk02 ++
  chunk03 ++
  chunk04 ++
  chunk05 ++
  chunk06 ++
  chunk07 ++
  chunk08 ++
  chunk09 ++
  chunk10 ++
  chunk11 ++
  chunk12 ++
  chunk13 ++
  chunk14 ++
  chunk15 ++
  chunk16 ++
  chunk17 ++
  chunk18 ++
  chunk19 ++
  chunk20 ++
  chunk21 ++
  chunk22 ++
  chunk23 ++
  chunk24 ++
  chunk25 ++
  chunk26 ++
  chunk27 ++
  chunk28 ++
  chunk29

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem elements_isChain :
    elements.IsChain (fun a b ↦ permutationCode a < permutationCode b) := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem elements_nodup : elements.Nodup :=
  nodup_of_code_isChain permutationCode elements_isChain

def sample : Finset G := finsetOfNodupList elements elements_nodup

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem sample_card : sample.card = 720 := by
  change elements.length = _
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem group_card : Nat.card G = 720 := by
  simp only [G, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem sample_eq_univ : sample = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ sample)
  rw [sample_card, Finset.card_univ, ← Nat.card_eq_fintype_card, group_card]

def row3Elements : List G :=
  [e0, e3, e4, e144, e147, e148, e240, e243, e244]

def row3 : Finset G := row3Elements.toFinset

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem row3_mem (x : G) : x ∈ row3 ↔ x ∈ row3Elements := by
  simp only [row3, List.mem_toFinset]

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem row3_list_closed : listSubgroupCheck row3Elements = true := by
  decide +kernel

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem row3_subgroup : subgroupCheck row3 = true := by
  exact listSubgroupCheck_sound row3 row3Elements row3_mem row3_list_closed

set_option maxHeartbeats 0 in
-- Kernel reduction checks explicit permutation tables and finite count chunks.
theorem row3_card : row3.card = 3 ^ (Nat.card G).factorization 3 := by
  rw [group_card]
  decide +kernel

noncomputable def sylow3 : Sylow 3 G :=
  checkedSylow row3 row3_subgroup row3_card

end LisiSabatini.SymmetricFiniteCertificates.S6Three
