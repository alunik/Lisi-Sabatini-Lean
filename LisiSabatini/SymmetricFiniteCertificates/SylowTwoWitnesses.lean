module

public import LisiSabatini.FiniteCertificates.TableCertificate
public import Mathlib.Tactic.NormNum

/-!
# Small explicit Sylow-two witnesses for S5 and S6

Generated deterministically by `SymmetricFiniteCertificates/generate.py`.
Every acceptance theorem is checked by the Lean kernel.
-/

@[expose] public section

namespace LisiSabatini.SymmetricFiniteCertificates

set_option maxRecDepth 100000

open LisiSabatini.FiniteCertificates

namespace S5Tiny

abbrev G := Equiv.Perm (Fin 5)

def e0 : G where
  toFun := ![0, 1, 2, 3, 4]
  invFun := ![0, 1, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e1 : G where
  toFun := ![0, 1, 3, 2, 4]
  invFun := ![0, 1, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e2 : G where
  toFun := ![1, 0, 2, 3, 4]
  invFun := ![1, 0, 2, 3, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : G where
  toFun := ![1, 0, 3, 2, 4]
  invFun := ![1, 0, 3, 2, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : G where
  toFun := ![2, 3, 0, 1, 4]
  invFun := ![2, 3, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : G where
  toFun := ![2, 3, 1, 0, 4]
  invFun := ![3, 2, 0, 1, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : G where
  toFun := ![3, 2, 0, 1, 4]
  invFun := ![2, 3, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : G where
  toFun := ![3, 2, 1, 0, 4]
  invFun := ![3, 2, 1, 0, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row2 : Finset G :=
  {e0, e1, e2, e3, e4, e5, e6, e7}

theorem row2_subgroup : subgroupCheck row2 = true := by
  decide +kernel

theorem row2_card : row2.card = 8 := by
  decide +kernel

theorem group_card : Nat.card G = 120 := by
  simp only [G, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem row2_card_factorization : row2.card = 2 ^ (Nat.card G).factorization 2 := by
  rw [row2_card, group_card]
  decide +kernel

noncomputable def sylow2 : Sylow 2 G :=
  checkedSylow row2 row2_subgroup row2_card_factorization

theorem card_sylow2 : Nat.card sylow2 = 8 := by
  exact (card_checkedSubgroup row2 row2_subgroup).trans row2_card

def witness : G where
  toFun := ![0, 2, 1, 4, 3]
  invFun := ![0, 2, 1, 4, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem witness_good : goodCheck row2 witness = true := by
  decide +kernel

theorem sylow2_inter_witness_eq_bot : sylowInter sylow2 witness = ⊥ := by
  exact checkedSylow_good row2 row2_subgroup row2_card_factorization witness witness_good

end S5Tiny

namespace S6Tiny

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
  toFun := ![0, 1, 3, 2, 4, 5]
  invFun := ![0, 1, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e3 : G where
  toFun := ![0, 1, 3, 2, 5, 4]
  invFun := ![0, 1, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e4 : G where
  toFun := ![1, 0, 2, 3, 4, 5]
  invFun := ![1, 0, 2, 3, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e5 : G where
  toFun := ![1, 0, 2, 3, 5, 4]
  invFun := ![1, 0, 2, 3, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e6 : G where
  toFun := ![1, 0, 3, 2, 4, 5]
  invFun := ![1, 0, 3, 2, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e7 : G where
  toFun := ![1, 0, 3, 2, 5, 4]
  invFun := ![1, 0, 3, 2, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e8 : G where
  toFun := ![2, 3, 0, 1, 4, 5]
  invFun := ![2, 3, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e9 : G where
  toFun := ![2, 3, 0, 1, 5, 4]
  invFun := ![2, 3, 0, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e10 : G where
  toFun := ![2, 3, 1, 0, 4, 5]
  invFun := ![3, 2, 0, 1, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e11 : G where
  toFun := ![2, 3, 1, 0, 5, 4]
  invFun := ![3, 2, 0, 1, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e12 : G where
  toFun := ![3, 2, 0, 1, 4, 5]
  invFun := ![2, 3, 1, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e13 : G where
  toFun := ![3, 2, 0, 1, 5, 4]
  invFun := ![2, 3, 1, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e14 : G where
  toFun := ![3, 2, 1, 0, 4, 5]
  invFun := ![3, 2, 1, 0, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def e15 : G where
  toFun := ![3, 2, 1, 0, 5, 4]
  invFun := ![3, 2, 1, 0, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def row2 : Finset G :=
  {e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15}

theorem row2_subgroup : subgroupCheck row2 = true := by
  decide +kernel

theorem row2_card : row2.card = 16 := by
  decide +kernel

theorem group_card : Nat.card G = 720 := by
  simp only [G, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  norm_num [Nat.factorial]

theorem row2_card_factorization : row2.card = 2 ^ (Nat.card G).factorization 2 := by
  rw [row2_card, group_card]
  decide +kernel

noncomputable def sylow2 : Sylow 2 G :=
  checkedSylow row2 row2_subgroup row2_card_factorization

theorem card_sylow2 : Nat.card sylow2 = 16 := by
  exact (card_checkedSubgroup row2 row2_subgroup).trans row2_card

def witness : G where
  toFun := ![0, 2, 1, 4, 3, 5]
  invFun := ![0, 2, 1, 4, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem witness_good : goodCheck row2 witness = true := by
  decide +kernel

theorem sylow2_inter_witness_eq_bot : sylowInter sylow2 witness = ⊥ := by
  exact checkedSylow_good row2 row2_subgroup row2_card_factorization witness witness_good

end S6Tiny

end LisiSabatini.SymmetricFiniteCertificates
