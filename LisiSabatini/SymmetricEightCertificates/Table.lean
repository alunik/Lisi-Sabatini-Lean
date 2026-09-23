module

public import LisiSabatini.FiniteCertificates.IndexedTable

/-! Generated candidate data with kernel-checked acceptance proofs. -/

@[expose] public section

namespace LisiSabatini.SymmetricEightCertificates

open LisiSabatini.FiniteCertificates

set_option maxRecDepth 100000

abbrev G := Equiv.Perm (Fin 8)

local instance : DecidableEq G := permutationCodeDecidableEq_fin8

/-- A necessary condition for membership in the tree automorphism group. -/
def treeCheck (g : G) : Bool :=
  decide ((g 0).val / 2 = (g 1).val / 2 ∧
    (g 2).val / 2 = (g 3).val / 2 ∧
    (g 4).val / 2 = (g 5).val / 2 ∧
    (g 6).val / 2 = (g 7).val / 2 ∧
    (g 0).val / 4 = (g 2).val / 4 ∧
    (g 4).val / 4 = (g 6).val / 4)

def p0 : G where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p1 : G where
  toFun := ![0, 1, 2, 3, 4, 5, 7, 6]
  invFun := ![0, 1, 2, 3, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p2 : G where
  toFun := ![0, 1, 2, 3, 5, 4, 6, 7]
  invFun := ![0, 1, 2, 3, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p3 : G where
  toFun := ![0, 1, 2, 3, 5, 4, 7, 6]
  invFun := ![0, 1, 2, 3, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p4 : G where
  toFun := ![0, 1, 2, 3, 6, 7, 4, 5]
  invFun := ![0, 1, 2, 3, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p5 : G where
  toFun := ![0, 1, 2, 3, 6, 7, 5, 4]
  invFun := ![0, 1, 2, 3, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p6 : G where
  toFun := ![0, 1, 2, 3, 7, 6, 4, 5]
  invFun := ![0, 1, 2, 3, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p7 : G where
  toFun := ![0, 1, 2, 3, 7, 6, 5, 4]
  invFun := ![0, 1, 2, 3, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p8 : G where
  toFun := ![0, 1, 3, 2, 4, 5, 6, 7]
  invFun := ![0, 1, 3, 2, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p9 : G where
  toFun := ![0, 1, 3, 2, 4, 5, 7, 6]
  invFun := ![0, 1, 3, 2, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p10 : G where
  toFun := ![0, 1, 3, 2, 5, 4, 6, 7]
  invFun := ![0, 1, 3, 2, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p11 : G where
  toFun := ![0, 1, 3, 2, 5, 4, 7, 6]
  invFun := ![0, 1, 3, 2, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p12 : G where
  toFun := ![0, 1, 3, 2, 6, 7, 4, 5]
  invFun := ![0, 1, 3, 2, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p13 : G where
  toFun := ![0, 1, 3, 2, 6, 7, 5, 4]
  invFun := ![0, 1, 3, 2, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p14 : G where
  toFun := ![0, 1, 3, 2, 7, 6, 4, 5]
  invFun := ![0, 1, 3, 2, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p15 : G where
  toFun := ![0, 1, 3, 2, 7, 6, 5, 4]
  invFun := ![0, 1, 3, 2, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p16 : G where
  toFun := ![1, 0, 2, 3, 4, 5, 6, 7]
  invFun := ![1, 0, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p17 : G where
  toFun := ![1, 0, 2, 3, 4, 5, 7, 6]
  invFun := ![1, 0, 2, 3, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p18 : G where
  toFun := ![1, 0, 2, 3, 5, 4, 6, 7]
  invFun := ![1, 0, 2, 3, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p19 : G where
  toFun := ![1, 0, 2, 3, 5, 4, 7, 6]
  invFun := ![1, 0, 2, 3, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p20 : G where
  toFun := ![1, 0, 2, 3, 6, 7, 4, 5]
  invFun := ![1, 0, 2, 3, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p21 : G where
  toFun := ![1, 0, 2, 3, 6, 7, 5, 4]
  invFun := ![1, 0, 2, 3, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p22 : G where
  toFun := ![1, 0, 2, 3, 7, 6, 4, 5]
  invFun := ![1, 0, 2, 3, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p23 : G where
  toFun := ![1, 0, 2, 3, 7, 6, 5, 4]
  invFun := ![1, 0, 2, 3, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p24 : G where
  toFun := ![1, 0, 3, 2, 4, 5, 6, 7]
  invFun := ![1, 0, 3, 2, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p25 : G where
  toFun := ![1, 0, 3, 2, 4, 5, 7, 6]
  invFun := ![1, 0, 3, 2, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p26 : G where
  toFun := ![1, 0, 3, 2, 5, 4, 6, 7]
  invFun := ![1, 0, 3, 2, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p27 : G where
  toFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  invFun := ![1, 0, 3, 2, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p28 : G where
  toFun := ![1, 0, 3, 2, 6, 7, 4, 5]
  invFun := ![1, 0, 3, 2, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p29 : G where
  toFun := ![1, 0, 3, 2, 6, 7, 5, 4]
  invFun := ![1, 0, 3, 2, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p30 : G where
  toFun := ![1, 0, 3, 2, 7, 6, 4, 5]
  invFun := ![1, 0, 3, 2, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p31 : G where
  toFun := ![1, 0, 3, 2, 7, 6, 5, 4]
  invFun := ![1, 0, 3, 2, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p32 : G where
  toFun := ![2, 3, 0, 1, 4, 5, 6, 7]
  invFun := ![2, 3, 0, 1, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p33 : G where
  toFun := ![2, 3, 0, 1, 4, 5, 7, 6]
  invFun := ![2, 3, 0, 1, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p34 : G where
  toFun := ![2, 3, 0, 1, 5, 4, 6, 7]
  invFun := ![2, 3, 0, 1, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p35 : G where
  toFun := ![2, 3, 0, 1, 5, 4, 7, 6]
  invFun := ![2, 3, 0, 1, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p36 : G where
  toFun := ![2, 3, 0, 1, 6, 7, 4, 5]
  invFun := ![2, 3, 0, 1, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p37 : G where
  toFun := ![2, 3, 0, 1, 6, 7, 5, 4]
  invFun := ![2, 3, 0, 1, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p38 : G where
  toFun := ![2, 3, 0, 1, 7, 6, 4, 5]
  invFun := ![2, 3, 0, 1, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p39 : G where
  toFun := ![2, 3, 0, 1, 7, 6, 5, 4]
  invFun := ![2, 3, 0, 1, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p40 : G where
  toFun := ![2, 3, 1, 0, 4, 5, 6, 7]
  invFun := ![3, 2, 0, 1, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p41 : G where
  toFun := ![2, 3, 1, 0, 4, 5, 7, 6]
  invFun := ![3, 2, 0, 1, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p42 : G where
  toFun := ![2, 3, 1, 0, 5, 4, 6, 7]
  invFun := ![3, 2, 0, 1, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p43 : G where
  toFun := ![2, 3, 1, 0, 5, 4, 7, 6]
  invFun := ![3, 2, 0, 1, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p44 : G where
  toFun := ![2, 3, 1, 0, 6, 7, 4, 5]
  invFun := ![3, 2, 0, 1, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p45 : G where
  toFun := ![2, 3, 1, 0, 6, 7, 5, 4]
  invFun := ![3, 2, 0, 1, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p46 : G where
  toFun := ![2, 3, 1, 0, 7, 6, 4, 5]
  invFun := ![3, 2, 0, 1, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p47 : G where
  toFun := ![2, 3, 1, 0, 7, 6, 5, 4]
  invFun := ![3, 2, 0, 1, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p48 : G where
  toFun := ![3, 2, 0, 1, 4, 5, 6, 7]
  invFun := ![2, 3, 1, 0, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p49 : G where
  toFun := ![3, 2, 0, 1, 4, 5, 7, 6]
  invFun := ![2, 3, 1, 0, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p50 : G where
  toFun := ![3, 2, 0, 1, 5, 4, 6, 7]
  invFun := ![2, 3, 1, 0, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p51 : G where
  toFun := ![3, 2, 0, 1, 5, 4, 7, 6]
  invFun := ![2, 3, 1, 0, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p52 : G where
  toFun := ![3, 2, 0, 1, 6, 7, 4, 5]
  invFun := ![2, 3, 1, 0, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p53 : G where
  toFun := ![3, 2, 0, 1, 6, 7, 5, 4]
  invFun := ![2, 3, 1, 0, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p54 : G where
  toFun := ![3, 2, 0, 1, 7, 6, 4, 5]
  invFun := ![2, 3, 1, 0, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p55 : G where
  toFun := ![3, 2, 0, 1, 7, 6, 5, 4]
  invFun := ![2, 3, 1, 0, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p56 : G where
  toFun := ![3, 2, 1, 0, 4, 5, 6, 7]
  invFun := ![3, 2, 1, 0, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p57 : G where
  toFun := ![3, 2, 1, 0, 4, 5, 7, 6]
  invFun := ![3, 2, 1, 0, 4, 5, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p58 : G where
  toFun := ![3, 2, 1, 0, 5, 4, 6, 7]
  invFun := ![3, 2, 1, 0, 5, 4, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p59 : G where
  toFun := ![3, 2, 1, 0, 5, 4, 7, 6]
  invFun := ![3, 2, 1, 0, 5, 4, 7, 6]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p60 : G where
  toFun := ![3, 2, 1, 0, 6, 7, 4, 5]
  invFun := ![3, 2, 1, 0, 6, 7, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p61 : G where
  toFun := ![3, 2, 1, 0, 6, 7, 5, 4]
  invFun := ![3, 2, 1, 0, 7, 6, 4, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p62 : G where
  toFun := ![3, 2, 1, 0, 7, 6, 4, 5]
  invFun := ![3, 2, 1, 0, 6, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p63 : G where
  toFun := ![3, 2, 1, 0, 7, 6, 5, 4]
  invFun := ![3, 2, 1, 0, 7, 6, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p64 : G where
  toFun := ![4, 5, 6, 7, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p65 : G where
  toFun := ![4, 5, 6, 7, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p66 : G where
  toFun := ![4, 5, 6, 7, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p67 : G where
  toFun := ![4, 5, 6, 7, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p68 : G where
  toFun := ![4, 5, 6, 7, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p69 : G where
  toFun := ![4, 5, 6, 7, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p70 : G where
  toFun := ![4, 5, 6, 7, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p71 : G where
  toFun := ![4, 5, 6, 7, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 0, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p72 : G where
  toFun := ![4, 5, 7, 6, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p73 : G where
  toFun := ![4, 5, 7, 6, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p74 : G where
  toFun := ![4, 5, 7, 6, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p75 : G where
  toFun := ![4, 5, 7, 6, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p76 : G where
  toFun := ![4, 5, 7, 6, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p77 : G where
  toFun := ![4, 5, 7, 6, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p78 : G where
  toFun := ![4, 5, 7, 6, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p79 : G where
  toFun := ![4, 5, 7, 6, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 0, 1, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p80 : G where
  toFun := ![5, 4, 6, 7, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p81 : G where
  toFun := ![5, 4, 6, 7, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p82 : G where
  toFun := ![5, 4, 6, 7, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p83 : G where
  toFun := ![5, 4, 6, 7, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p84 : G where
  toFun := ![5, 4, 6, 7, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p85 : G where
  toFun := ![5, 4, 6, 7, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p86 : G where
  toFun := ![5, 4, 6, 7, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p87 : G where
  toFun := ![5, 4, 6, 7, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 1, 0, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p88 : G where
  toFun := ![5, 4, 7, 6, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p89 : G where
  toFun := ![5, 4, 7, 6, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p90 : G where
  toFun := ![5, 4, 7, 6, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p91 : G where
  toFun := ![5, 4, 7, 6, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p92 : G where
  toFun := ![5, 4, 7, 6, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p93 : G where
  toFun := ![5, 4, 7, 6, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p94 : G where
  toFun := ![5, 4, 7, 6, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p95 : G where
  toFun := ![5, 4, 7, 6, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 1, 0, 3, 2]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p96 : G where
  toFun := ![6, 7, 4, 5, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p97 : G where
  toFun := ![6, 7, 4, 5, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p98 : G where
  toFun := ![6, 7, 4, 5, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p99 : G where
  toFun := ![6, 7, 4, 5, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p100 : G where
  toFun := ![6, 7, 4, 5, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p101 : G where
  toFun := ![6, 7, 4, 5, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p102 : G where
  toFun := ![6, 7, 4, 5, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p103 : G where
  toFun := ![6, 7, 4, 5, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 2, 3, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p104 : G where
  toFun := ![6, 7, 5, 4, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p105 : G where
  toFun := ![6, 7, 5, 4, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p106 : G where
  toFun := ![6, 7, 5, 4, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p107 : G where
  toFun := ![6, 7, 5, 4, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p108 : G where
  toFun := ![6, 7, 5, 4, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p109 : G where
  toFun := ![6, 7, 5, 4, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p110 : G where
  toFun := ![6, 7, 5, 4, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p111 : G where
  toFun := ![6, 7, 5, 4, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 3, 2, 0, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p112 : G where
  toFun := ![7, 6, 4, 5, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p113 : G where
  toFun := ![7, 6, 4, 5, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p114 : G where
  toFun := ![7, 6, 4, 5, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p115 : G where
  toFun := ![7, 6, 4, 5, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p116 : G where
  toFun := ![7, 6, 4, 5, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p117 : G where
  toFun := ![7, 6, 4, 5, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p118 : G where
  toFun := ![7, 6, 4, 5, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p119 : G where
  toFun := ![7, 6, 4, 5, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 2, 3, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p120 : G where
  toFun := ![7, 6, 5, 4, 0, 1, 2, 3]
  invFun := ![4, 5, 6, 7, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p121 : G where
  toFun := ![7, 6, 5, 4, 0, 1, 3, 2]
  invFun := ![4, 5, 7, 6, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p122 : G where
  toFun := ![7, 6, 5, 4, 1, 0, 2, 3]
  invFun := ![5, 4, 6, 7, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p123 : G where
  toFun := ![7, 6, 5, 4, 1, 0, 3, 2]
  invFun := ![5, 4, 7, 6, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p124 : G where
  toFun := ![7, 6, 5, 4, 2, 3, 0, 1]
  invFun := ![6, 7, 4, 5, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p125 : G where
  toFun := ![7, 6, 5, 4, 2, 3, 1, 0]
  invFun := ![7, 6, 4, 5, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p126 : G where
  toFun := ![7, 6, 5, 4, 3, 2, 0, 1]
  invFun := ![6, 7, 5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def p127 : G where
  toFun := ![7, 6, 5, 4, 3, 2, 1, 0]
  invFun := ![7, 6, 5, 4, 3, 2, 1, 0]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r0 : G where
  toFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  invFun := ![0, 1, 2, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r1 : G where
  toFun := ![0, 1, 2, 3, 4, 6, 5, 7]
  invFun := ![0, 1, 2, 3, 4, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r2 : G where
  toFun := ![0, 1, 2, 3, 4, 7, 5, 6]
  invFun := ![0, 1, 2, 3, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r3 : G where
  toFun := ![0, 1, 2, 4, 3, 5, 6, 7]
  invFun := ![0, 1, 2, 4, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r4 : G where
  toFun := ![0, 1, 2, 4, 3, 6, 5, 7]
  invFun := ![0, 1, 2, 4, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r5 : G where
  toFun := ![0, 1, 2, 4, 3, 7, 5, 6]
  invFun := ![0, 1, 2, 4, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r6 : G where
  toFun := ![0, 1, 2, 5, 3, 4, 6, 7]
  invFun := ![0, 1, 2, 4, 5, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r7 : G where
  toFun := ![0, 1, 2, 5, 3, 6, 4, 7]
  invFun := ![0, 1, 2, 4, 6, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r8 : G where
  toFun := ![0, 1, 2, 5, 3, 7, 4, 6]
  invFun := ![0, 1, 2, 4, 6, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r9 : G where
  toFun := ![0, 1, 2, 6, 3, 4, 5, 7]
  invFun := ![0, 1, 2, 4, 5, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r10 : G where
  toFun := ![0, 1, 2, 6, 3, 5, 4, 7]
  invFun := ![0, 1, 2, 4, 6, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r11 : G where
  toFun := ![0, 1, 2, 6, 3, 7, 4, 5]
  invFun := ![0, 1, 2, 4, 6, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r12 : G where
  toFun := ![0, 1, 2, 7, 3, 4, 5, 6]
  invFun := ![0, 1, 2, 4, 5, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r13 : G where
  toFun := ![0, 1, 2, 7, 3, 5, 4, 6]
  invFun := ![0, 1, 2, 4, 6, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r14 : G where
  toFun := ![0, 1, 2, 7, 3, 6, 4, 5]
  invFun := ![0, 1, 2, 4, 6, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r15 : G where
  toFun := ![0, 1, 3, 4, 2, 5, 6, 7]
  invFun := ![0, 1, 4, 2, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r16 : G where
  toFun := ![0, 1, 3, 4, 2, 6, 5, 7]
  invFun := ![0, 1, 4, 2, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r17 : G where
  toFun := ![0, 1, 3, 4, 2, 7, 5, 6]
  invFun := ![0, 1, 4, 2, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r18 : G where
  toFun := ![0, 1, 3, 5, 2, 4, 6, 7]
  invFun := ![0, 1, 4, 2, 5, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r19 : G where
  toFun := ![0, 1, 3, 5, 2, 6, 4, 7]
  invFun := ![0, 1, 4, 2, 6, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r20 : G where
  toFun := ![0, 1, 3, 5, 2, 7, 4, 6]
  invFun := ![0, 1, 4, 2, 6, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r21 : G where
  toFun := ![0, 1, 3, 6, 2, 4, 5, 7]
  invFun := ![0, 1, 4, 2, 5, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r22 : G where
  toFun := ![0, 1, 3, 6, 2, 5, 4, 7]
  invFun := ![0, 1, 4, 2, 6, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r23 : G where
  toFun := ![0, 1, 3, 6, 2, 7, 4, 5]
  invFun := ![0, 1, 4, 2, 6, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r24 : G where
  toFun := ![0, 1, 3, 7, 2, 4, 5, 6]
  invFun := ![0, 1, 4, 2, 5, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r25 : G where
  toFun := ![0, 1, 3, 7, 2, 5, 4, 6]
  invFun := ![0, 1, 4, 2, 6, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r26 : G where
  toFun := ![0, 1, 3, 7, 2, 6, 4, 5]
  invFun := ![0, 1, 4, 2, 6, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r27 : G where
  toFun := ![0, 1, 4, 5, 2, 3, 6, 7]
  invFun := ![0, 1, 4, 5, 2, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r28 : G where
  toFun := ![0, 1, 4, 5, 2, 6, 3, 7]
  invFun := ![0, 1, 4, 6, 2, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r29 : G where
  toFun := ![0, 1, 4, 5, 2, 7, 3, 6]
  invFun := ![0, 1, 4, 6, 2, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r30 : G where
  toFun := ![0, 1, 4, 6, 2, 3, 5, 7]
  invFun := ![0, 1, 4, 5, 2, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r31 : G where
  toFun := ![0, 1, 4, 6, 2, 5, 3, 7]
  invFun := ![0, 1, 4, 6, 2, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r32 : G where
  toFun := ![0, 1, 4, 6, 2, 7, 3, 5]
  invFun := ![0, 1, 4, 6, 2, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r33 : G where
  toFun := ![0, 1, 4, 7, 2, 3, 5, 6]
  invFun := ![0, 1, 4, 5, 2, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r34 : G where
  toFun := ![0, 1, 4, 7, 2, 5, 3, 6]
  invFun := ![0, 1, 4, 6, 2, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r35 : G where
  toFun := ![0, 1, 4, 7, 2, 6, 3, 5]
  invFun := ![0, 1, 4, 6, 2, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r36 : G where
  toFun := ![0, 1, 5, 6, 2, 3, 4, 7]
  invFun := ![0, 1, 4, 5, 6, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r37 : G where
  toFun := ![0, 1, 5, 6, 2, 4, 3, 7]
  invFun := ![0, 1, 4, 6, 5, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r38 : G where
  toFun := ![0, 1, 5, 6, 2, 7, 3, 4]
  invFun := ![0, 1, 4, 6, 7, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r39 : G where
  toFun := ![0, 1, 5, 7, 2, 3, 4, 6]
  invFun := ![0, 1, 4, 5, 6, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r40 : G where
  toFun := ![0, 1, 5, 7, 2, 4, 3, 6]
  invFun := ![0, 1, 4, 6, 5, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r41 : G where
  toFun := ![0, 1, 5, 7, 2, 6, 3, 4]
  invFun := ![0, 1, 4, 6, 7, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r42 : G where
  toFun := ![0, 1, 6, 7, 2, 3, 4, 5]
  invFun := ![0, 1, 4, 5, 6, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r43 : G where
  toFun := ![0, 1, 6, 7, 2, 4, 3, 5]
  invFun := ![0, 1, 4, 6, 5, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r44 : G where
  toFun := ![0, 1, 6, 7, 2, 5, 3, 4]
  invFun := ![0, 1, 4, 6, 7, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r45 : G where
  toFun := ![0, 2, 1, 3, 4, 5, 6, 7]
  invFun := ![0, 2, 1, 3, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r46 : G where
  toFun := ![0, 2, 1, 3, 4, 6, 5, 7]
  invFun := ![0, 2, 1, 3, 4, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r47 : G where
  toFun := ![0, 2, 1, 3, 4, 7, 5, 6]
  invFun := ![0, 2, 1, 3, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r48 : G where
  toFun := ![0, 2, 1, 4, 3, 5, 6, 7]
  invFun := ![0, 2, 1, 4, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r49 : G where
  toFun := ![0, 2, 1, 4, 3, 6, 5, 7]
  invFun := ![0, 2, 1, 4, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r50 : G where
  toFun := ![0, 2, 1, 4, 3, 7, 5, 6]
  invFun := ![0, 2, 1, 4, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r51 : G where
  toFun := ![0, 2, 1, 5, 3, 4, 6, 7]
  invFun := ![0, 2, 1, 4, 5, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r52 : G where
  toFun := ![0, 2, 1, 5, 3, 6, 4, 7]
  invFun := ![0, 2, 1, 4, 6, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r53 : G where
  toFun := ![0, 2, 1, 5, 3, 7, 4, 6]
  invFun := ![0, 2, 1, 4, 6, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r54 : G where
  toFun := ![0, 2, 1, 6, 3, 4, 5, 7]
  invFun := ![0, 2, 1, 4, 5, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r55 : G where
  toFun := ![0, 2, 1, 6, 3, 5, 4, 7]
  invFun := ![0, 2, 1, 4, 6, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r56 : G where
  toFun := ![0, 2, 1, 6, 3, 7, 4, 5]
  invFun := ![0, 2, 1, 4, 6, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r57 : G where
  toFun := ![0, 2, 1, 7, 3, 4, 5, 6]
  invFun := ![0, 2, 1, 4, 5, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r58 : G where
  toFun := ![0, 2, 1, 7, 3, 5, 4, 6]
  invFun := ![0, 2, 1, 4, 6, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r59 : G where
  toFun := ![0, 2, 1, 7, 3, 6, 4, 5]
  invFun := ![0, 2, 1, 4, 6, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r60 : G where
  toFun := ![0, 2, 3, 4, 1, 5, 6, 7]
  invFun := ![0, 4, 1, 2, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r61 : G where
  toFun := ![0, 2, 3, 4, 1, 6, 5, 7]
  invFun := ![0, 4, 1, 2, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r62 : G where
  toFun := ![0, 2, 3, 4, 1, 7, 5, 6]
  invFun := ![0, 4, 1, 2, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r63 : G where
  toFun := ![0, 2, 3, 5, 1, 4, 6, 7]
  invFun := ![0, 4, 1, 2, 5, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r64 : G where
  toFun := ![0, 2, 3, 5, 1, 6, 4, 7]
  invFun := ![0, 4, 1, 2, 6, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r65 : G where
  toFun := ![0, 2, 3, 5, 1, 7, 4, 6]
  invFun := ![0, 4, 1, 2, 6, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r66 : G where
  toFun := ![0, 2, 3, 6, 1, 4, 5, 7]
  invFun := ![0, 4, 1, 2, 5, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r67 : G where
  toFun := ![0, 2, 3, 6, 1, 5, 4, 7]
  invFun := ![0, 4, 1, 2, 6, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r68 : G where
  toFun := ![0, 2, 3, 6, 1, 7, 4, 5]
  invFun := ![0, 4, 1, 2, 6, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r69 : G where
  toFun := ![0, 2, 3, 7, 1, 4, 5, 6]
  invFun := ![0, 4, 1, 2, 5, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r70 : G where
  toFun := ![0, 2, 3, 7, 1, 5, 4, 6]
  invFun := ![0, 4, 1, 2, 6, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r71 : G where
  toFun := ![0, 2, 3, 7, 1, 6, 4, 5]
  invFun := ![0, 4, 1, 2, 6, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r72 : G where
  toFun := ![0, 2, 4, 5, 1, 3, 6, 7]
  invFun := ![0, 4, 1, 5, 2, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r73 : G where
  toFun := ![0, 2, 4, 5, 1, 6, 3, 7]
  invFun := ![0, 4, 1, 6, 2, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r74 : G where
  toFun := ![0, 2, 4, 5, 1, 7, 3, 6]
  invFun := ![0, 4, 1, 6, 2, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r75 : G where
  toFun := ![0, 2, 4, 6, 1, 3, 5, 7]
  invFun := ![0, 4, 1, 5, 2, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r76 : G where
  toFun := ![0, 2, 4, 6, 1, 5, 3, 7]
  invFun := ![0, 4, 1, 6, 2, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r77 : G where
  toFun := ![0, 2, 4, 6, 1, 7, 3, 5]
  invFun := ![0, 4, 1, 6, 2, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r78 : G where
  toFun := ![0, 2, 4, 7, 1, 3, 5, 6]
  invFun := ![0, 4, 1, 5, 2, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r79 : G where
  toFun := ![0, 2, 4, 7, 1, 5, 3, 6]
  invFun := ![0, 4, 1, 6, 2, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r80 : G where
  toFun := ![0, 2, 4, 7, 1, 6, 3, 5]
  invFun := ![0, 4, 1, 6, 2, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r81 : G where
  toFun := ![0, 2, 5, 6, 1, 3, 4, 7]
  invFun := ![0, 4, 1, 5, 6, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r82 : G where
  toFun := ![0, 2, 5, 6, 1, 4, 3, 7]
  invFun := ![0, 4, 1, 6, 5, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r83 : G where
  toFun := ![0, 2, 5, 6, 1, 7, 3, 4]
  invFun := ![0, 4, 1, 6, 7, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r84 : G where
  toFun := ![0, 2, 5, 7, 1, 3, 4, 6]
  invFun := ![0, 4, 1, 5, 6, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r85 : G where
  toFun := ![0, 2, 5, 7, 1, 4, 3, 6]
  invFun := ![0, 4, 1, 6, 5, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r86 : G where
  toFun := ![0, 2, 5, 7, 1, 6, 3, 4]
  invFun := ![0, 4, 1, 6, 7, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r87 : G where
  toFun := ![0, 2, 6, 7, 1, 3, 4, 5]
  invFun := ![0, 4, 1, 5, 6, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r88 : G where
  toFun := ![0, 2, 6, 7, 1, 4, 3, 5]
  invFun := ![0, 4, 1, 6, 5, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r89 : G where
  toFun := ![0, 2, 6, 7, 1, 5, 3, 4]
  invFun := ![0, 4, 1, 6, 7, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r90 : G where
  toFun := ![0, 3, 1, 2, 4, 5, 6, 7]
  invFun := ![0, 2, 3, 1, 4, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r91 : G where
  toFun := ![0, 3, 1, 2, 4, 6, 5, 7]
  invFun := ![0, 2, 3, 1, 4, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r92 : G where
  toFun := ![0, 3, 1, 2, 4, 7, 5, 6]
  invFun := ![0, 2, 3, 1, 4, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r93 : G where
  toFun := ![0, 3, 1, 4, 2, 5, 6, 7]
  invFun := ![0, 2, 4, 1, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r94 : G where
  toFun := ![0, 3, 1, 4, 2, 6, 5, 7]
  invFun := ![0, 2, 4, 1, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r95 : G where
  toFun := ![0, 3, 1, 4, 2, 7, 5, 6]
  invFun := ![0, 2, 4, 1, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r96 : G where
  toFun := ![0, 3, 1, 5, 2, 4, 6, 7]
  invFun := ![0, 2, 4, 1, 5, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r97 : G where
  toFun := ![0, 3, 1, 5, 2, 6, 4, 7]
  invFun := ![0, 2, 4, 1, 6, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r98 : G where
  toFun := ![0, 3, 1, 5, 2, 7, 4, 6]
  invFun := ![0, 2, 4, 1, 6, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r99 : G where
  toFun := ![0, 3, 1, 6, 2, 4, 5, 7]
  invFun := ![0, 2, 4, 1, 5, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r100 : G where
  toFun := ![0, 3, 1, 6, 2, 5, 4, 7]
  invFun := ![0, 2, 4, 1, 6, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r101 : G where
  toFun := ![0, 3, 1, 6, 2, 7, 4, 5]
  invFun := ![0, 2, 4, 1, 6, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r102 : G where
  toFun := ![0, 3, 1, 7, 2, 4, 5, 6]
  invFun := ![0, 2, 4, 1, 5, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r103 : G where
  toFun := ![0, 3, 1, 7, 2, 5, 4, 6]
  invFun := ![0, 2, 4, 1, 6, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r104 : G where
  toFun := ![0, 3, 1, 7, 2, 6, 4, 5]
  invFun := ![0, 2, 4, 1, 6, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r105 : G where
  toFun := ![0, 3, 2, 4, 1, 5, 6, 7]
  invFun := ![0, 4, 2, 1, 3, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r106 : G where
  toFun := ![0, 3, 2, 4, 1, 6, 5, 7]
  invFun := ![0, 4, 2, 1, 3, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r107 : G where
  toFun := ![0, 3, 2, 4, 1, 7, 5, 6]
  invFun := ![0, 4, 2, 1, 3, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r108 : G where
  toFun := ![0, 3, 2, 5, 1, 4, 6, 7]
  invFun := ![0, 4, 2, 1, 5, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r109 : G where
  toFun := ![0, 3, 2, 5, 1, 6, 4, 7]
  invFun := ![0, 4, 2, 1, 6, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r110 : G where
  toFun := ![0, 3, 2, 5, 1, 7, 4, 6]
  invFun := ![0, 4, 2, 1, 6, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r111 : G where
  toFun := ![0, 3, 2, 6, 1, 4, 5, 7]
  invFun := ![0, 4, 2, 1, 5, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r112 : G where
  toFun := ![0, 3, 2, 6, 1, 5, 4, 7]
  invFun := ![0, 4, 2, 1, 6, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r113 : G where
  toFun := ![0, 3, 2, 6, 1, 7, 4, 5]
  invFun := ![0, 4, 2, 1, 6, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r114 : G where
  toFun := ![0, 3, 2, 7, 1, 4, 5, 6]
  invFun := ![0, 4, 2, 1, 5, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r115 : G where
  toFun := ![0, 3, 2, 7, 1, 5, 4, 6]
  invFun := ![0, 4, 2, 1, 6, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r116 : G where
  toFun := ![0, 3, 2, 7, 1, 6, 4, 5]
  invFun := ![0, 4, 2, 1, 6, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r117 : G where
  toFun := ![0, 3, 4, 5, 1, 2, 6, 7]
  invFun := ![0, 4, 5, 1, 2, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r118 : G where
  toFun := ![0, 3, 4, 5, 1, 6, 2, 7]
  invFun := ![0, 4, 6, 1, 2, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r119 : G where
  toFun := ![0, 3, 4, 5, 1, 7, 2, 6]
  invFun := ![0, 4, 6, 1, 2, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r120 : G where
  toFun := ![0, 3, 4, 6, 1, 2, 5, 7]
  invFun := ![0, 4, 5, 1, 2, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r121 : G where
  toFun := ![0, 3, 4, 6, 1, 5, 2, 7]
  invFun := ![0, 4, 6, 1, 2, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r122 : G where
  toFun := ![0, 3, 4, 6, 1, 7, 2, 5]
  invFun := ![0, 4, 6, 1, 2, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r123 : G where
  toFun := ![0, 3, 4, 7, 1, 2, 5, 6]
  invFun := ![0, 4, 5, 1, 2, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r124 : G where
  toFun := ![0, 3, 4, 7, 1, 5, 2, 6]
  invFun := ![0, 4, 6, 1, 2, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r125 : G where
  toFun := ![0, 3, 4, 7, 1, 6, 2, 5]
  invFun := ![0, 4, 6, 1, 2, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r126 : G where
  toFun := ![0, 3, 5, 6, 1, 2, 4, 7]
  invFun := ![0, 4, 5, 1, 6, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r127 : G where
  toFun := ![0, 3, 5, 6, 1, 4, 2, 7]
  invFun := ![0, 4, 6, 1, 5, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r128 : G where
  toFun := ![0, 3, 5, 6, 1, 7, 2, 4]
  invFun := ![0, 4, 6, 1, 7, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r129 : G where
  toFun := ![0, 3, 5, 7, 1, 2, 4, 6]
  invFun := ![0, 4, 5, 1, 6, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r130 : G where
  toFun := ![0, 3, 5, 7, 1, 4, 2, 6]
  invFun := ![0, 4, 6, 1, 5, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r131 : G where
  toFun := ![0, 3, 5, 7, 1, 6, 2, 4]
  invFun := ![0, 4, 6, 1, 7, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r132 : G where
  toFun := ![0, 3, 6, 7, 1, 2, 4, 5]
  invFun := ![0, 4, 5, 1, 6, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r133 : G where
  toFun := ![0, 3, 6, 7, 1, 4, 2, 5]
  invFun := ![0, 4, 6, 1, 5, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r134 : G where
  toFun := ![0, 3, 6, 7, 1, 5, 2, 4]
  invFun := ![0, 4, 6, 1, 7, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r135 : G where
  toFun := ![0, 4, 1, 2, 3, 5, 6, 7]
  invFun := ![0, 2, 3, 4, 1, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r136 : G where
  toFun := ![0, 4, 1, 2, 3, 6, 5, 7]
  invFun := ![0, 2, 3, 4, 1, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r137 : G where
  toFun := ![0, 4, 1, 2, 3, 7, 5, 6]
  invFun := ![0, 2, 3, 4, 1, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r138 : G where
  toFun := ![0, 4, 1, 3, 2, 5, 6, 7]
  invFun := ![0, 2, 4, 3, 1, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r139 : G where
  toFun := ![0, 4, 1, 3, 2, 6, 5, 7]
  invFun := ![0, 2, 4, 3, 1, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r140 : G where
  toFun := ![0, 4, 1, 3, 2, 7, 5, 6]
  invFun := ![0, 2, 4, 3, 1, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r141 : G where
  toFun := ![0, 4, 1, 5, 2, 3, 6, 7]
  invFun := ![0, 2, 4, 5, 1, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r142 : G where
  toFun := ![0, 4, 1, 5, 2, 6, 3, 7]
  invFun := ![0, 2, 4, 6, 1, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r143 : G where
  toFun := ![0, 4, 1, 5, 2, 7, 3, 6]
  invFun := ![0, 2, 4, 6, 1, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r144 : G where
  toFun := ![0, 4, 1, 6, 2, 3, 5, 7]
  invFun := ![0, 2, 4, 5, 1, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r145 : G where
  toFun := ![0, 4, 1, 6, 2, 5, 3, 7]
  invFun := ![0, 2, 4, 6, 1, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r146 : G where
  toFun := ![0, 4, 1, 6, 2, 7, 3, 5]
  invFun := ![0, 2, 4, 6, 1, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r147 : G where
  toFun := ![0, 4, 1, 7, 2, 3, 5, 6]
  invFun := ![0, 2, 4, 5, 1, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r148 : G where
  toFun := ![0, 4, 1, 7, 2, 5, 3, 6]
  invFun := ![0, 2, 4, 6, 1, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r149 : G where
  toFun := ![0, 4, 1, 7, 2, 6, 3, 5]
  invFun := ![0, 2, 4, 6, 1, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r150 : G where
  toFun := ![0, 4, 2, 3, 1, 5, 6, 7]
  invFun := ![0, 4, 2, 3, 1, 5, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r151 : G where
  toFun := ![0, 4, 2, 3, 1, 6, 5, 7]
  invFun := ![0, 4, 2, 3, 1, 6, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r152 : G where
  toFun := ![0, 4, 2, 3, 1, 7, 5, 6]
  invFun := ![0, 4, 2, 3, 1, 6, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r153 : G where
  toFun := ![0, 4, 2, 5, 1, 3, 6, 7]
  invFun := ![0, 4, 2, 5, 1, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r154 : G where
  toFun := ![0, 4, 2, 5, 1, 6, 3, 7]
  invFun := ![0, 4, 2, 6, 1, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r155 : G where
  toFun := ![0, 4, 2, 5, 1, 7, 3, 6]
  invFun := ![0, 4, 2, 6, 1, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r156 : G where
  toFun := ![0, 4, 2, 6, 1, 3, 5, 7]
  invFun := ![0, 4, 2, 5, 1, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r157 : G where
  toFun := ![0, 4, 2, 6, 1, 5, 3, 7]
  invFun := ![0, 4, 2, 6, 1, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r158 : G where
  toFun := ![0, 4, 2, 6, 1, 7, 3, 5]
  invFun := ![0, 4, 2, 6, 1, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r159 : G where
  toFun := ![0, 4, 2, 7, 1, 3, 5, 6]
  invFun := ![0, 4, 2, 5, 1, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r160 : G where
  toFun := ![0, 4, 2, 7, 1, 5, 3, 6]
  invFun := ![0, 4, 2, 6, 1, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r161 : G where
  toFun := ![0, 4, 2, 7, 1, 6, 3, 5]
  invFun := ![0, 4, 2, 6, 1, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r162 : G where
  toFun := ![0, 4, 3, 5, 1, 2, 6, 7]
  invFun := ![0, 4, 5, 2, 1, 3, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r163 : G where
  toFun := ![0, 4, 3, 5, 1, 6, 2, 7]
  invFun := ![0, 4, 6, 2, 1, 3, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r164 : G where
  toFun := ![0, 4, 3, 5, 1, 7, 2, 6]
  invFun := ![0, 4, 6, 2, 1, 3, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r165 : G where
  toFun := ![0, 4, 3, 6, 1, 2, 5, 7]
  invFun := ![0, 4, 5, 2, 1, 6, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r166 : G where
  toFun := ![0, 4, 3, 6, 1, 5, 2, 7]
  invFun := ![0, 4, 6, 2, 1, 5, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r167 : G where
  toFun := ![0, 4, 3, 6, 1, 7, 2, 5]
  invFun := ![0, 4, 6, 2, 1, 7, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r168 : G where
  toFun := ![0, 4, 3, 7, 1, 2, 5, 6]
  invFun := ![0, 4, 5, 2, 1, 6, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r169 : G where
  toFun := ![0, 4, 3, 7, 1, 5, 2, 6]
  invFun := ![0, 4, 6, 2, 1, 5, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r170 : G where
  toFun := ![0, 4, 3, 7, 1, 6, 2, 5]
  invFun := ![0, 4, 6, 2, 1, 7, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r171 : G where
  toFun := ![0, 4, 5, 6, 1, 2, 3, 7]
  invFun := ![0, 4, 5, 6, 1, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r172 : G where
  toFun := ![0, 4, 5, 6, 1, 3, 2, 7]
  invFun := ![0, 4, 6, 5, 1, 2, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r173 : G where
  toFun := ![0, 4, 5, 6, 1, 7, 2, 3]
  invFun := ![0, 4, 6, 7, 1, 2, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r174 : G where
  toFun := ![0, 4, 5, 7, 1, 2, 3, 6]
  invFun := ![0, 4, 5, 6, 1, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r175 : G where
  toFun := ![0, 4, 5, 7, 1, 3, 2, 6]
  invFun := ![0, 4, 6, 5, 1, 2, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r176 : G where
  toFun := ![0, 4, 5, 7, 1, 6, 2, 3]
  invFun := ![0, 4, 6, 7, 1, 2, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r177 : G where
  toFun := ![0, 4, 6, 7, 1, 2, 3, 5]
  invFun := ![0, 4, 5, 6, 1, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r178 : G where
  toFun := ![0, 4, 6, 7, 1, 3, 2, 5]
  invFun := ![0, 4, 6, 5, 1, 7, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r179 : G where
  toFun := ![0, 4, 6, 7, 1, 5, 2, 3]
  invFun := ![0, 4, 6, 7, 1, 5, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r180 : G where
  toFun := ![0, 5, 1, 2, 3, 4, 6, 7]
  invFun := ![0, 2, 3, 4, 5, 1, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r181 : G where
  toFun := ![0, 5, 1, 2, 3, 6, 4, 7]
  invFun := ![0, 2, 3, 4, 6, 1, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r182 : G where
  toFun := ![0, 5, 1, 2, 3, 7, 4, 6]
  invFun := ![0, 2, 3, 4, 6, 1, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r183 : G where
  toFun := ![0, 5, 1, 3, 2, 4, 6, 7]
  invFun := ![0, 2, 4, 3, 5, 1, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r184 : G where
  toFun := ![0, 5, 1, 3, 2, 6, 4, 7]
  invFun := ![0, 2, 4, 3, 6, 1, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r185 : G where
  toFun := ![0, 5, 1, 3, 2, 7, 4, 6]
  invFun := ![0, 2, 4, 3, 6, 1, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r186 : G where
  toFun := ![0, 5, 1, 4, 2, 3, 6, 7]
  invFun := ![0, 2, 4, 5, 3, 1, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r187 : G where
  toFun := ![0, 5, 1, 4, 2, 6, 3, 7]
  invFun := ![0, 2, 4, 6, 3, 1, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r188 : G where
  toFun := ![0, 5, 1, 4, 2, 7, 3, 6]
  invFun := ![0, 2, 4, 6, 3, 1, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r189 : G where
  toFun := ![0, 5, 1, 6, 2, 3, 4, 7]
  invFun := ![0, 2, 4, 5, 6, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r190 : G where
  toFun := ![0, 5, 1, 6, 2, 4, 3, 7]
  invFun := ![0, 2, 4, 6, 5, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r191 : G where
  toFun := ![0, 5, 1, 6, 2, 7, 3, 4]
  invFun := ![0, 2, 4, 6, 7, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r192 : G where
  toFun := ![0, 5, 1, 7, 2, 3, 4, 6]
  invFun := ![0, 2, 4, 5, 6, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r193 : G where
  toFun := ![0, 5, 1, 7, 2, 4, 3, 6]
  invFun := ![0, 2, 4, 6, 5, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r194 : G where
  toFun := ![0, 5, 1, 7, 2, 6, 3, 4]
  invFun := ![0, 2, 4, 6, 7, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r195 : G where
  toFun := ![0, 5, 2, 3, 1, 4, 6, 7]
  invFun := ![0, 4, 2, 3, 5, 1, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r196 : G where
  toFun := ![0, 5, 2, 3, 1, 6, 4, 7]
  invFun := ![0, 4, 2, 3, 6, 1, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r197 : G where
  toFun := ![0, 5, 2, 3, 1, 7, 4, 6]
  invFun := ![0, 4, 2, 3, 6, 1, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r198 : G where
  toFun := ![0, 5, 2, 4, 1, 3, 6, 7]
  invFun := ![0, 4, 2, 5, 3, 1, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r199 : G where
  toFun := ![0, 5, 2, 4, 1, 6, 3, 7]
  invFun := ![0, 4, 2, 6, 3, 1, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r200 : G where
  toFun := ![0, 5, 2, 4, 1, 7, 3, 6]
  invFun := ![0, 4, 2, 6, 3, 1, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r201 : G where
  toFun := ![0, 5, 2, 6, 1, 3, 4, 7]
  invFun := ![0, 4, 2, 5, 6, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r202 : G where
  toFun := ![0, 5, 2, 6, 1, 4, 3, 7]
  invFun := ![0, 4, 2, 6, 5, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r203 : G where
  toFun := ![0, 5, 2, 6, 1, 7, 3, 4]
  invFun := ![0, 4, 2, 6, 7, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r204 : G where
  toFun := ![0, 5, 2, 7, 1, 3, 4, 6]
  invFun := ![0, 4, 2, 5, 6, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r205 : G where
  toFun := ![0, 5, 2, 7, 1, 4, 3, 6]
  invFun := ![0, 4, 2, 6, 5, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r206 : G where
  toFun := ![0, 5, 2, 7, 1, 6, 3, 4]
  invFun := ![0, 4, 2, 6, 7, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r207 : G where
  toFun := ![0, 5, 3, 4, 1, 2, 6, 7]
  invFun := ![0, 4, 5, 2, 3, 1, 6, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r208 : G where
  toFun := ![0, 5, 3, 4, 1, 6, 2, 7]
  invFun := ![0, 4, 6, 2, 3, 1, 5, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r209 : G where
  toFun := ![0, 5, 3, 4, 1, 7, 2, 6]
  invFun := ![0, 4, 6, 2, 3, 1, 7, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r210 : G where
  toFun := ![0, 5, 3, 6, 1, 2, 4, 7]
  invFun := ![0, 4, 5, 2, 6, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r211 : G where
  toFun := ![0, 5, 3, 6, 1, 4, 2, 7]
  invFun := ![0, 4, 6, 2, 5, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r212 : G where
  toFun := ![0, 5, 3, 6, 1, 7, 2, 4]
  invFun := ![0, 4, 6, 2, 7, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r213 : G where
  toFun := ![0, 5, 3, 7, 1, 2, 4, 6]
  invFun := ![0, 4, 5, 2, 6, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r214 : G where
  toFun := ![0, 5, 3, 7, 1, 4, 2, 6]
  invFun := ![0, 4, 6, 2, 5, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r215 : G where
  toFun := ![0, 5, 3, 7, 1, 6, 2, 4]
  invFun := ![0, 4, 6, 2, 7, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r216 : G where
  toFun := ![0, 5, 4, 6, 1, 2, 3, 7]
  invFun := ![0, 4, 5, 6, 2, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r217 : G where
  toFun := ![0, 5, 4, 6, 1, 3, 2, 7]
  invFun := ![0, 4, 6, 5, 2, 1, 3, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r218 : G where
  toFun := ![0, 5, 4, 6, 1, 7, 2, 3]
  invFun := ![0, 4, 6, 7, 2, 1, 3, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r219 : G where
  toFun := ![0, 5, 4, 7, 1, 2, 3, 6]
  invFun := ![0, 4, 5, 6, 2, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r220 : G where
  toFun := ![0, 5, 4, 7, 1, 3, 2, 6]
  invFun := ![0, 4, 6, 5, 2, 1, 7, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r221 : G where
  toFun := ![0, 5, 4, 7, 1, 6, 2, 3]
  invFun := ![0, 4, 6, 7, 2, 1, 5, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r222 : G where
  toFun := ![0, 5, 6, 7, 1, 2, 3, 4]
  invFun := ![0, 4, 5, 6, 7, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r223 : G where
  toFun := ![0, 5, 6, 7, 1, 3, 2, 4]
  invFun := ![0, 4, 6, 5, 7, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r224 : G where
  toFun := ![0, 5, 6, 7, 1, 4, 2, 3]
  invFun := ![0, 4, 6, 7, 5, 1, 2, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r225 : G where
  toFun := ![0, 6, 1, 2, 3, 4, 5, 7]
  invFun := ![0, 2, 3, 4, 5, 6, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r226 : G where
  toFun := ![0, 6, 1, 2, 3, 5, 4, 7]
  invFun := ![0, 2, 3, 4, 6, 5, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r227 : G where
  toFun := ![0, 6, 1, 2, 3, 7, 4, 5]
  invFun := ![0, 2, 3, 4, 6, 7, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r228 : G where
  toFun := ![0, 6, 1, 3, 2, 4, 5, 7]
  invFun := ![0, 2, 4, 3, 5, 6, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r229 : G where
  toFun := ![0, 6, 1, 3, 2, 5, 4, 7]
  invFun := ![0, 2, 4, 3, 6, 5, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r230 : G where
  toFun := ![0, 6, 1, 3, 2, 7, 4, 5]
  invFun := ![0, 2, 4, 3, 6, 7, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r231 : G where
  toFun := ![0, 6, 1, 4, 2, 3, 5, 7]
  invFun := ![0, 2, 4, 5, 3, 6, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r232 : G where
  toFun := ![0, 6, 1, 4, 2, 5, 3, 7]
  invFun := ![0, 2, 4, 6, 3, 5, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r233 : G where
  toFun := ![0, 6, 1, 4, 2, 7, 3, 5]
  invFun := ![0, 2, 4, 6, 3, 7, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r234 : G where
  toFun := ![0, 6, 1, 5, 2, 3, 4, 7]
  invFun := ![0, 2, 4, 5, 6, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r235 : G where
  toFun := ![0, 6, 1, 5, 2, 4, 3, 7]
  invFun := ![0, 2, 4, 6, 5, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r236 : G where
  toFun := ![0, 6, 1, 5, 2, 7, 3, 4]
  invFun := ![0, 2, 4, 6, 7, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r237 : G where
  toFun := ![0, 6, 1, 7, 2, 3, 4, 5]
  invFun := ![0, 2, 4, 5, 6, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r238 : G where
  toFun := ![0, 6, 1, 7, 2, 4, 3, 5]
  invFun := ![0, 2, 4, 6, 5, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r239 : G where
  toFun := ![0, 6, 1, 7, 2, 5, 3, 4]
  invFun := ![0, 2, 4, 6, 7, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r240 : G where
  toFun := ![0, 6, 2, 3, 1, 4, 5, 7]
  invFun := ![0, 4, 2, 3, 5, 6, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r241 : G where
  toFun := ![0, 6, 2, 3, 1, 5, 4, 7]
  invFun := ![0, 4, 2, 3, 6, 5, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r242 : G where
  toFun := ![0, 6, 2, 3, 1, 7, 4, 5]
  invFun := ![0, 4, 2, 3, 6, 7, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r243 : G where
  toFun := ![0, 6, 2, 4, 1, 3, 5, 7]
  invFun := ![0, 4, 2, 5, 3, 6, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r244 : G where
  toFun := ![0, 6, 2, 4, 1, 5, 3, 7]
  invFun := ![0, 4, 2, 6, 3, 5, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r245 : G where
  toFun := ![0, 6, 2, 4, 1, 7, 3, 5]
  invFun := ![0, 4, 2, 6, 3, 7, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r246 : G where
  toFun := ![0, 6, 2, 5, 1, 3, 4, 7]
  invFun := ![0, 4, 2, 5, 6, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r247 : G where
  toFun := ![0, 6, 2, 5, 1, 4, 3, 7]
  invFun := ![0, 4, 2, 6, 5, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r248 : G where
  toFun := ![0, 6, 2, 5, 1, 7, 3, 4]
  invFun := ![0, 4, 2, 6, 7, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r249 : G where
  toFun := ![0, 6, 2, 7, 1, 3, 4, 5]
  invFun := ![0, 4, 2, 5, 6, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r250 : G where
  toFun := ![0, 6, 2, 7, 1, 4, 3, 5]
  invFun := ![0, 4, 2, 6, 5, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r251 : G where
  toFun := ![0, 6, 2, 7, 1, 5, 3, 4]
  invFun := ![0, 4, 2, 6, 7, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r252 : G where
  toFun := ![0, 6, 3, 4, 1, 2, 5, 7]
  invFun := ![0, 4, 5, 2, 3, 6, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r253 : G where
  toFun := ![0, 6, 3, 4, 1, 5, 2, 7]
  invFun := ![0, 4, 6, 2, 3, 5, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r254 : G where
  toFun := ![0, 6, 3, 4, 1, 7, 2, 5]
  invFun := ![0, 4, 6, 2, 3, 7, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r255 : G where
  toFun := ![0, 6, 3, 5, 1, 2, 4, 7]
  invFun := ![0, 4, 5, 2, 6, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r256 : G where
  toFun := ![0, 6, 3, 5, 1, 4, 2, 7]
  invFun := ![0, 4, 6, 2, 5, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r257 : G where
  toFun := ![0, 6, 3, 5, 1, 7, 2, 4]
  invFun := ![0, 4, 6, 2, 7, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r258 : G where
  toFun := ![0, 6, 3, 7, 1, 2, 4, 5]
  invFun := ![0, 4, 5, 2, 6, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r259 : G where
  toFun := ![0, 6, 3, 7, 1, 4, 2, 5]
  invFun := ![0, 4, 6, 2, 5, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r260 : G where
  toFun := ![0, 6, 3, 7, 1, 5, 2, 4]
  invFun := ![0, 4, 6, 2, 7, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r261 : G where
  toFun := ![0, 6, 4, 5, 1, 2, 3, 7]
  invFun := ![0, 4, 5, 6, 2, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r262 : G where
  toFun := ![0, 6, 4, 5, 1, 3, 2, 7]
  invFun := ![0, 4, 6, 5, 2, 3, 1, 7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r263 : G where
  toFun := ![0, 6, 4, 5, 1, 7, 2, 3]
  invFun := ![0, 4, 6, 7, 2, 3, 1, 5]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r264 : G where
  toFun := ![0, 6, 4, 7, 1, 2, 3, 5]
  invFun := ![0, 4, 5, 6, 2, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r265 : G where
  toFun := ![0, 6, 4, 7, 1, 3, 2, 5]
  invFun := ![0, 4, 6, 5, 2, 7, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r266 : G where
  toFun := ![0, 6, 4, 7, 1, 5, 2, 3]
  invFun := ![0, 4, 6, 7, 2, 5, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r267 : G where
  toFun := ![0, 6, 5, 7, 1, 2, 3, 4]
  invFun := ![0, 4, 5, 6, 7, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r268 : G where
  toFun := ![0, 6, 5, 7, 1, 3, 2, 4]
  invFun := ![0, 4, 6, 5, 7, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r269 : G where
  toFun := ![0, 6, 5, 7, 1, 4, 2, 3]
  invFun := ![0, 4, 6, 7, 5, 2, 1, 3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r270 : G where
  toFun := ![0, 7, 1, 2, 3, 4, 5, 6]
  invFun := ![0, 2, 3, 4, 5, 6, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r271 : G where
  toFun := ![0, 7, 1, 2, 3, 5, 4, 6]
  invFun := ![0, 2, 3, 4, 6, 5, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r272 : G where
  toFun := ![0, 7, 1, 2, 3, 6, 4, 5]
  invFun := ![0, 2, 3, 4, 6, 7, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r273 : G where
  toFun := ![0, 7, 1, 3, 2, 4, 5, 6]
  invFun := ![0, 2, 4, 3, 5, 6, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r274 : G where
  toFun := ![0, 7, 1, 3, 2, 5, 4, 6]
  invFun := ![0, 2, 4, 3, 6, 5, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r275 : G where
  toFun := ![0, 7, 1, 3, 2, 6, 4, 5]
  invFun := ![0, 2, 4, 3, 6, 7, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r276 : G where
  toFun := ![0, 7, 1, 4, 2, 3, 5, 6]
  invFun := ![0, 2, 4, 5, 3, 6, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r277 : G where
  toFun := ![0, 7, 1, 4, 2, 5, 3, 6]
  invFun := ![0, 2, 4, 6, 3, 5, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r278 : G where
  toFun := ![0, 7, 1, 4, 2, 6, 3, 5]
  invFun := ![0, 2, 4, 6, 3, 7, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r279 : G where
  toFun := ![0, 7, 1, 5, 2, 3, 4, 6]
  invFun := ![0, 2, 4, 5, 6, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r280 : G where
  toFun := ![0, 7, 1, 5, 2, 4, 3, 6]
  invFun := ![0, 2, 4, 6, 5, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r281 : G where
  toFun := ![0, 7, 1, 5, 2, 6, 3, 4]
  invFun := ![0, 2, 4, 6, 7, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r282 : G where
  toFun := ![0, 7, 1, 6, 2, 3, 4, 5]
  invFun := ![0, 2, 4, 5, 6, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r283 : G where
  toFun := ![0, 7, 1, 6, 2, 4, 3, 5]
  invFun := ![0, 2, 4, 6, 5, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r284 : G where
  toFun := ![0, 7, 1, 6, 2, 5, 3, 4]
  invFun := ![0, 2, 4, 6, 7, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r285 : G where
  toFun := ![0, 7, 2, 3, 1, 4, 5, 6]
  invFun := ![0, 4, 2, 3, 5, 6, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r286 : G where
  toFun := ![0, 7, 2, 3, 1, 5, 4, 6]
  invFun := ![0, 4, 2, 3, 6, 5, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r287 : G where
  toFun := ![0, 7, 2, 3, 1, 6, 4, 5]
  invFun := ![0, 4, 2, 3, 6, 7, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r288 : G where
  toFun := ![0, 7, 2, 4, 1, 3, 5, 6]
  invFun := ![0, 4, 2, 5, 3, 6, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r289 : G where
  toFun := ![0, 7, 2, 4, 1, 5, 3, 6]
  invFun := ![0, 4, 2, 6, 3, 5, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r290 : G where
  toFun := ![0, 7, 2, 4, 1, 6, 3, 5]
  invFun := ![0, 4, 2, 6, 3, 7, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r291 : G where
  toFun := ![0, 7, 2, 5, 1, 3, 4, 6]
  invFun := ![0, 4, 2, 5, 6, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r292 : G where
  toFun := ![0, 7, 2, 5, 1, 4, 3, 6]
  invFun := ![0, 4, 2, 6, 5, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r293 : G where
  toFun := ![0, 7, 2, 5, 1, 6, 3, 4]
  invFun := ![0, 4, 2, 6, 7, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r294 : G where
  toFun := ![0, 7, 2, 6, 1, 3, 4, 5]
  invFun := ![0, 4, 2, 5, 6, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r295 : G where
  toFun := ![0, 7, 2, 6, 1, 4, 3, 5]
  invFun := ![0, 4, 2, 6, 5, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r296 : G where
  toFun := ![0, 7, 2, 6, 1, 5, 3, 4]
  invFun := ![0, 4, 2, 6, 7, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r297 : G where
  toFun := ![0, 7, 3, 4, 1, 2, 5, 6]
  invFun := ![0, 4, 5, 2, 3, 6, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r298 : G where
  toFun := ![0, 7, 3, 4, 1, 5, 2, 6]
  invFun := ![0, 4, 6, 2, 3, 5, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r299 : G where
  toFun := ![0, 7, 3, 4, 1, 6, 2, 5]
  invFun := ![0, 4, 6, 2, 3, 7, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r300 : G where
  toFun := ![0, 7, 3, 5, 1, 2, 4, 6]
  invFun := ![0, 4, 5, 2, 6, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r301 : G where
  toFun := ![0, 7, 3, 5, 1, 4, 2, 6]
  invFun := ![0, 4, 6, 2, 5, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r302 : G where
  toFun := ![0, 7, 3, 5, 1, 6, 2, 4]
  invFun := ![0, 4, 6, 2, 7, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r303 : G where
  toFun := ![0, 7, 3, 6, 1, 2, 4, 5]
  invFun := ![0, 4, 5, 2, 6, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r304 : G where
  toFun := ![0, 7, 3, 6, 1, 4, 2, 5]
  invFun := ![0, 4, 6, 2, 5, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r305 : G where
  toFun := ![0, 7, 3, 6, 1, 5, 2, 4]
  invFun := ![0, 4, 6, 2, 7, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r306 : G where
  toFun := ![0, 7, 4, 5, 1, 2, 3, 6]
  invFun := ![0, 4, 5, 6, 2, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r307 : G where
  toFun := ![0, 7, 4, 5, 1, 3, 2, 6]
  invFun := ![0, 4, 6, 5, 2, 3, 7, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r308 : G where
  toFun := ![0, 7, 4, 5, 1, 6, 2, 3]
  invFun := ![0, 4, 6, 7, 2, 3, 5, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r309 : G where
  toFun := ![0, 7, 4, 6, 1, 2, 3, 5]
  invFun := ![0, 4, 5, 6, 2, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r310 : G where
  toFun := ![0, 7, 4, 6, 1, 3, 2, 5]
  invFun := ![0, 4, 6, 5, 2, 7, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r311 : G where
  toFun := ![0, 7, 4, 6, 1, 5, 2, 3]
  invFun := ![0, 4, 6, 7, 2, 5, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r312 : G where
  toFun := ![0, 7, 5, 6, 1, 2, 3, 4]
  invFun := ![0, 4, 5, 6, 7, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r313 : G where
  toFun := ![0, 7, 5, 6, 1, 3, 2, 4]
  invFun := ![0, 4, 6, 5, 7, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def r314 : G where
  toFun := ![0, 7, 5, 6, 1, 4, 2, 3]
  invFun := ![0, 4, 6, 7, 5, 2, 3, 1]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def rowElements : List G :=
  [p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15,
   p16, p17, p18, p19, p20, p21, p22, p23, p24, p25, p26, p27, p28, p29, p30, p31,
   p32, p33, p34, p35, p36, p37, p38, p39, p40, p41, p42, p43, p44, p45, p46, p47,
   p48, p49, p50, p51, p52, p53, p54, p55, p56, p57, p58, p59, p60, p61, p62, p63,
   p64, p65, p66, p67, p68, p69, p70, p71, p72, p73, p74, p75, p76, p77, p78, p79,
   p80, p81, p82, p83, p84, p85, p86, p87, p88, p89, p90, p91, p92, p93, p94, p95,
   p96, p97, p98, p99, p100, p101, p102, p103, p104, p105, p106, p107, p108, p109, p110, p111,
   p112, p113, p114, p115, p116, p117, p118, p119, p120, p121, p122, p123, p124, p125, p126, p127]

def rowArray : Array G := rowElements.toArray

def rowAt (i : Fin 128) : G :=
  rowArray[i.val]'(by change i.val < 128; exact i.isLt)

theorem rowElements_nodup : rowElements.Nodup :=
  nodup_of_code_isChain permutationCode (by decide +kernel)

def row : Finset G := finsetOfNodupList rowElements rowElements_nodup

theorem row_card : row.card = 128 := rfl

theorem mem_row_iff (g : G) : g ∈ row ↔ ∃ i : Fin 128, rowAt i = g := by
  change g ∈ rowElements ↔ ∃ i : Fin rowElements.length, rowElements[i] = g
  exact List.mem_iff_get

theorem rowAt_mem (i : Fin 128) : rowAt i ∈ row :=
  (mem_row_iff _).mpr ⟨i, rfl⟩

def representatives : Array G :=
  #[r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15,
   r16, r17, r18, r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31,
   r32, r33, r34, r35, r36, r37, r38, r39, r40, r41, r42, r43, r44, r45, r46, r47,
   r48, r49, r50, r51, r52, r53, r54, r55, r56, r57, r58, r59, r60, r61, r62, r63,
   r64, r65, r66, r67, r68, r69, r70, r71, r72, r73, r74, r75, r76, r77, r78, r79,
   r80, r81, r82, r83, r84, r85, r86, r87, r88, r89, r90, r91, r92, r93, r94, r95,
   r96, r97, r98, r99, r100, r101, r102, r103, r104, r105, r106, r107, r108, r109, r110, r111,
   r112, r113, r114, r115, r116, r117, r118, r119, r120, r121, r122, r123, r124, r125, r126, r127,
   r128, r129, r130, r131, r132, r133, r134, r135, r136, r137, r138, r139, r140, r141, r142, r143,
   r144, r145, r146, r147, r148, r149, r150, r151, r152, r153, r154, r155, r156, r157, r158, r159,
   r160, r161, r162, r163, r164, r165, r166, r167, r168, r169, r170, r171, r172, r173, r174, r175,
   r176, r177, r178, r179, r180, r181, r182, r183, r184, r185, r186, r187, r188, r189, r190, r191,
   r192, r193, r194, r195, r196, r197, r198, r199, r200, r201, r202, r203, r204, r205, r206, r207,
   r208, r209, r210, r211, r212, r213, r214, r215, r216, r217, r218, r219, r220, r221, r222, r223,
   r224, r225, r226, r227, r228, r229, r230, r231, r232, r233, r234, r235, r236, r237, r238, r239,
   r240, r241, r242, r243, r244, r245, r246, r247, r248, r249, r250, r251, r252, r253, r254, r255,
   r256, r257, r258, r259, r260, r261, r262, r263, r264, r265, r266, r267, r268, r269, r270, r271,
   r272, r273, r274, r275, r276, r277, r278, r279, r280, r281, r282, r283, r284, r285, r286, r287,
   r288, r289, r290, r291, r292, r293, r294, r295, r296, r297, r298, r299, r300, r301, r302, r303,
   r304, r305, r306, r307, r308, r309, r310, r311, r312, r313, r314]

def repAt (i : Fin 315) : G :=
  representatives[i.val]'(by change i.val < 315; exact i.isLt)

def inverseIndexData : Array (Fin 128) :=
  #[0, 1, 2, 3, 4, 6, 5, 7, 8, 9, 10, 11, 12, 14, 13, 15,
   16, 17, 18, 19, 20, 22, 21, 23, 24, 25, 26, 27, 28, 30, 29, 31,
   32, 33, 34, 35, 36, 38, 37, 39, 48, 49, 50, 51, 52, 54, 53, 55,
   40, 41, 42, 43, 44, 46, 45, 47, 56, 57, 58, 59, 60, 62, 61, 63,
   64, 72, 80, 88, 96, 112, 104, 120, 65, 73, 81, 89, 97, 113, 105, 121,
   66, 74, 82, 90, 98, 114, 106, 122, 67, 75, 83, 91, 99, 115, 107, 123,
   68, 76, 84, 92, 100, 116, 108, 124, 70, 78, 86, 94, 102, 118, 110, 126,
   69, 77, 85, 93, 101, 117, 109, 125, 71, 79, 87, 95, 103, 119, 111, 127]

def inverseIndex (i : Fin 128) : Fin 128 :=
  inverseIndexData[i.val]'(by change i.val < 128; exact i.isLt)

def productIndexBlock00 : Array (Fin 128) :=
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71,
   88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71,
   120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71,
   88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71]

def productIndexBlock01 : Array (Fin 128) :=
  #[8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
   24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69]

def productIndexBlock02 : Array (Fin 128) :=
  #[16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70]

def productIndexBlock03 : Array (Fin 128) :=
  #[24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
   56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68]

def productIndexBlock04 : Array (Fin 128) :=
  #[32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67]

def productIndexBlock05 : Array (Fin 128) :=
  #[40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65]

def productIndexBlock06 : Array (Fin 128) :=
  #[48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
   24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66]

def productIndexBlock07 : Array (Fin 128) :=
  #[56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64]

def productIndexBlock08 : Array (Fin 128) :=
  #[64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
   24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
   56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31,
   0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63,
   32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47,
   8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7,
   24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   56, 57, 58, 59, 60, 61, 62, 63, 48, 49, 50, 51, 52, 53, 54, 55,
   40, 41, 42, 43, 44, 45, 46, 47, 32, 33, 34, 35, 36, 37, 38, 39,
   24, 25, 26, 27, 28, 29, 30, 31, 16, 17, 18, 19, 20, 21, 22, 23,
   8, 9, 10, 11, 12, 13, 14, 15, 0, 1, 2, 3, 4, 5, 6, 7]

def productIndexBlock09 : Array (Fin 128) :=
  #[72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71,
   88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   17, 16, 19, 18, 22, 23, 20, 21, 25, 24, 27, 26, 30, 31, 28, 29,
   1, 0, 3, 2, 6, 7, 4, 5, 9, 8, 11, 10, 14, 15, 12, 13,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   49, 48, 51, 50, 54, 55, 52, 53, 57, 56, 59, 58, 62, 63, 60, 61,
   33, 32, 35, 34, 38, 39, 36, 37, 41, 40, 43, 42, 46, 47, 44, 45,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   57, 56, 59, 58, 62, 63, 60, 61, 49, 48, 51, 50, 54, 55, 52, 53,
   41, 40, 43, 42, 46, 47, 44, 45, 33, 32, 35, 34, 38, 39, 36, 37,
   25, 24, 27, 26, 30, 31, 28, 29, 17, 16, 19, 18, 22, 23, 20, 21,
   9, 8, 11, 10, 14, 15, 12, 13, 1, 0, 3, 2, 6, 7, 4, 5]

def productIndexBlock10 : Array (Fin 128) :=
  #[80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   18, 19, 16, 17, 21, 20, 23, 22, 26, 27, 24, 25, 29, 28, 31, 30,
   2, 3, 0, 1, 5, 4, 7, 6, 10, 11, 8, 9, 13, 12, 15, 14,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   50, 51, 48, 49, 53, 52, 55, 54, 58, 59, 56, 57, 61, 60, 63, 62,
   34, 35, 32, 33, 37, 36, 39, 38, 42, 43, 40, 41, 45, 44, 47, 46,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   58, 59, 56, 57, 61, 60, 63, 62, 50, 51, 48, 49, 53, 52, 55, 54,
   42, 43, 40, 41, 45, 44, 47, 46, 34, 35, 32, 33, 37, 36, 39, 38,
   26, 27, 24, 25, 29, 28, 31, 30, 18, 19, 16, 17, 21, 20, 23, 22,
   10, 11, 8, 9, 13, 12, 15, 14, 2, 3, 0, 1, 5, 4, 7, 6]

def productIndexBlock11 : Array (Fin 128) :=
  #[88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71,
   120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   19, 18, 17, 16, 23, 22, 21, 20, 27, 26, 25, 24, 31, 30, 29, 28,
   3, 2, 1, 0, 7, 6, 5, 4, 11, 10, 9, 8, 15, 14, 13, 12,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   51, 50, 49, 48, 55, 54, 53, 52, 59, 58, 57, 56, 63, 62, 61, 60,
   35, 34, 33, 32, 39, 38, 37, 36, 43, 42, 41, 40, 47, 46, 45, 44,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   59, 58, 57, 56, 63, 62, 61, 60, 51, 50, 49, 48, 55, 54, 53, 52,
   43, 42, 41, 40, 47, 46, 45, 44, 35, 34, 33, 32, 39, 38, 37, 36,
   27, 26, 25, 24, 31, 30, 29, 28, 19, 18, 17, 16, 23, 22, 21, 20,
   11, 10, 9, 8, 15, 14, 13, 12, 3, 2, 1, 0, 7, 6, 5, 4]

def productIndexBlock12 : Array (Fin 128) :=
  #[96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   20, 21, 22, 23, 16, 17, 18, 19, 28, 29, 30, 31, 24, 25, 26, 27,
   4, 5, 6, 7, 0, 1, 2, 3, 12, 13, 14, 15, 8, 9, 10, 11,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   52, 53, 54, 55, 48, 49, 50, 51, 60, 61, 62, 63, 56, 57, 58, 59,
   36, 37, 38, 39, 32, 33, 34, 35, 44, 45, 46, 47, 40, 41, 42, 43,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   60, 61, 62, 63, 56, 57, 58, 59, 52, 53, 54, 55, 48, 49, 50, 51,
   44, 45, 46, 47, 40, 41, 42, 43, 36, 37, 38, 39, 32, 33, 34, 35,
   28, 29, 30, 31, 24, 25, 26, 27, 20, 21, 22, 23, 16, 17, 18, 19,
   12, 13, 14, 15, 8, 9, 10, 11, 4, 5, 6, 7, 0, 1, 2, 3]

def productIndexBlock13 : Array (Fin 128) :=
  #[104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95,
   64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   81, 80, 83, 82, 86, 87, 84, 85, 89, 88, 91, 90, 94, 95, 92, 93,
   65, 64, 67, 66, 70, 71, 68, 69, 73, 72, 75, 74, 78, 79, 76, 77,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   82, 83, 80, 81, 85, 84, 87, 86, 90, 91, 88, 89, 93, 92, 95, 94,
   66, 67, 64, 65, 69, 68, 71, 70, 74, 75, 72, 73, 77, 76, 79, 78,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   83, 82, 81, 80, 87, 86, 85, 84, 91, 90, 89, 88, 95, 94, 93, 92,
   67, 66, 65, 64, 71, 70, 69, 68, 75, 74, 73, 72, 79, 78, 77, 76,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   84, 85, 86, 87, 80, 81, 82, 83, 92, 93, 94, 95, 88, 89, 90, 91,
   68, 69, 70, 71, 64, 65, 66, 67, 76, 77, 78, 79, 72, 73, 74, 75,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   85, 84, 87, 86, 82, 83, 80, 81, 93, 92, 95, 94, 90, 91, 88, 89,
   69, 68, 71, 70, 66, 67, 64, 65, 77, 76, 79, 78, 74, 75, 72, 73,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   21, 20, 23, 22, 18, 19, 16, 17, 29, 28, 31, 30, 26, 27, 24, 25,
   5, 4, 7, 6, 2, 3, 0, 1, 13, 12, 15, 14, 10, 11, 8, 9,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   86, 87, 84, 85, 81, 80, 83, 82, 94, 95, 92, 93, 89, 88, 91, 90,
   70, 71, 68, 69, 65, 64, 67, 66, 78, 79, 76, 77, 73, 72, 75, 74,
   53, 52, 55, 54, 50, 51, 48, 49, 61, 60, 63, 62, 58, 59, 56, 57,
   37, 36, 39, 38, 34, 35, 32, 33, 45, 44, 47, 46, 42, 43, 40, 41,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   87, 86, 85, 84, 83, 82, 81, 80, 95, 94, 93, 92, 91, 90, 89, 88,
   71, 70, 69, 68, 67, 66, 65, 64, 79, 78, 77, 76, 75, 74, 73, 72,
   61, 60, 63, 62, 58, 59, 56, 57, 53, 52, 55, 54, 50, 51, 48, 49,
   45, 44, 47, 46, 42, 43, 40, 41, 37, 36, 39, 38, 34, 35, 32, 33,
   29, 28, 31, 30, 26, 27, 24, 25, 21, 20, 23, 22, 18, 19, 16, 17,
   13, 12, 15, 14, 10, 11, 8, 9, 5, 4, 7, 6, 2, 3, 0, 1]

def productIndexBlock14 : Array (Fin 128) :=
  #[112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127,
   96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111,
   72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71,
   88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   113, 112, 115, 114, 118, 119, 116, 117, 121, 120, 123, 122, 126, 127, 124, 125,
   97, 96, 99, 98, 102, 103, 100, 101, 105, 104, 107, 106, 110, 111, 108, 109,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   114, 115, 112, 113, 117, 116, 119, 118, 122, 123, 120, 121, 125, 124, 127, 126,
   98, 99, 96, 97, 101, 100, 103, 102, 106, 107, 104, 105, 109, 108, 111, 110,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   115, 114, 113, 112, 119, 118, 117, 116, 123, 122, 121, 120, 127, 126, 125, 124,
   99, 98, 97, 96, 103, 102, 101, 100, 107, 106, 105, 104, 111, 110, 109, 108,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   116, 117, 118, 119, 112, 113, 114, 115, 124, 125, 126, 127, 120, 121, 122, 123,
   100, 101, 102, 103, 96, 97, 98, 99, 108, 109, 110, 111, 104, 105, 106, 107,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   117, 116, 119, 118, 114, 115, 112, 113, 125, 124, 127, 126, 122, 123, 120, 121,
   101, 100, 103, 102, 98, 99, 96, 97, 109, 108, 111, 110, 106, 107, 104, 105,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   22, 23, 20, 21, 17, 16, 19, 18, 30, 31, 28, 29, 25, 24, 27, 26,
   6, 7, 4, 5, 1, 0, 3, 2, 14, 15, 12, 13, 9, 8, 11, 10,
   118, 119, 116, 117, 113, 112, 115, 114, 126, 127, 124, 125, 121, 120, 123, 122,
   102, 103, 100, 101, 97, 96, 99, 98, 110, 111, 108, 109, 105, 104, 107, 106,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   54, 55, 52, 53, 49, 48, 51, 50, 62, 63, 60, 61, 57, 56, 59, 58,
   38, 39, 36, 37, 33, 32, 35, 34, 46, 47, 44, 45, 41, 40, 43, 42,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   119, 118, 117, 116, 115, 114, 113, 112, 127, 126, 125, 124, 123, 122, 121, 120,
   103, 102, 101, 100, 99, 98, 97, 96, 111, 110, 109, 108, 107, 106, 105, 104,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   62, 63, 60, 61, 57, 56, 59, 58, 54, 55, 52, 53, 49, 48, 51, 50,
   46, 47, 44, 45, 41, 40, 43, 42, 38, 39, 36, 37, 33, 32, 35, 34,
   30, 31, 28, 29, 25, 24, 27, 26, 22, 23, 20, 21, 17, 16, 19, 18,
   14, 15, 12, 13, 9, 8, 11, 10, 6, 7, 4, 5, 1, 0, 3, 2]

def productIndexBlock15 : Array (Fin 128) :=
  #[120, 121, 122, 123, 124, 125, 126, 127, 112, 113, 114, 115, 116, 117, 118, 119,
   104, 105, 106, 107, 108, 109, 110, 111, 96, 97, 98, 99, 100, 101, 102, 103,
   88, 89, 90, 91, 92, 93, 94, 95, 80, 81, 82, 83, 84, 85, 86, 87,
   72, 73, 74, 75, 76, 77, 78, 79, 64, 65, 66, 67, 68, 69, 70, 71,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   121, 120, 123, 122, 126, 127, 124, 125, 113, 112, 115, 114, 118, 119, 116, 117,
   105, 104, 107, 106, 110, 111, 108, 109, 97, 96, 99, 98, 102, 103, 100, 101,
   89, 88, 91, 90, 94, 95, 92, 93, 81, 80, 83, 82, 86, 87, 84, 85,
   73, 72, 75, 74, 78, 79, 76, 77, 65, 64, 67, 66, 70, 71, 68, 69,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   122, 123, 120, 121, 125, 124, 127, 126, 114, 115, 112, 113, 117, 116, 119, 118,
   106, 107, 104, 105, 109, 108, 111, 110, 98, 99, 96, 97, 101, 100, 103, 102,
   90, 91, 88, 89, 93, 92, 95, 94, 82, 83, 80, 81, 85, 84, 87, 86,
   74, 75, 72, 73, 77, 76, 79, 78, 66, 67, 64, 65, 69, 68, 71, 70,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   123, 122, 121, 120, 127, 126, 125, 124, 115, 114, 113, 112, 119, 118, 117, 116,
   107, 106, 105, 104, 111, 110, 109, 108, 99, 98, 97, 96, 103, 102, 101, 100,
   91, 90, 89, 88, 95, 94, 93, 92, 83, 82, 81, 80, 87, 86, 85, 84,
   75, 74, 73, 72, 79, 78, 77, 76, 67, 66, 65, 64, 71, 70, 69, 68,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   124, 125, 126, 127, 120, 121, 122, 123, 116, 117, 118, 119, 112, 113, 114, 115,
   108, 109, 110, 111, 104, 105, 106, 107, 100, 101, 102, 103, 96, 97, 98, 99,
   92, 93, 94, 95, 88, 89, 90, 91, 84, 85, 86, 87, 80, 81, 82, 83,
   76, 77, 78, 79, 72, 73, 74, 75, 68, 69, 70, 71, 64, 65, 66, 67,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   125, 124, 127, 126, 122, 123, 120, 121, 117, 116, 119, 118, 114, 115, 112, 113,
   109, 108, 111, 110, 106, 107, 104, 105, 101, 100, 103, 102, 98, 99, 96, 97,
   93, 92, 95, 94, 90, 91, 88, 89, 85, 84, 87, 86, 82, 83, 80, 81,
   77, 76, 79, 78, 74, 75, 72, 73, 69, 68, 71, 70, 66, 67, 64, 65,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   23, 22, 21, 20, 19, 18, 17, 16, 31, 30, 29, 28, 27, 26, 25, 24,
   7, 6, 5, 4, 3, 2, 1, 0, 15, 14, 13, 12, 11, 10, 9, 8,
   126, 127, 124, 125, 121, 120, 123, 122, 118, 119, 116, 117, 113, 112, 115, 114,
   110, 111, 108, 109, 105, 104, 107, 106, 102, 103, 100, 101, 97, 96, 99, 98,
   94, 95, 92, 93, 89, 88, 91, 90, 86, 87, 84, 85, 81, 80, 83, 82,
   78, 79, 76, 77, 73, 72, 75, 74, 70, 71, 68, 69, 65, 64, 67, 66,
   55, 54, 53, 52, 51, 50, 49, 48, 63, 62, 61, 60, 59, 58, 57, 56,
   39, 38, 37, 36, 35, 34, 33, 32, 47, 46, 45, 44, 43, 42, 41, 40,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   127, 126, 125, 124, 123, 122, 121, 120, 119, 118, 117, 116, 115, 114, 113, 112,
   111, 110, 109, 108, 107, 106, 105, 104, 103, 102, 101, 100, 99, 98, 97, 96,
   95, 94, 93, 92, 91, 90, 89, 88, 87, 86, 85, 84, 83, 82, 81, 80,
   79, 78, 77, 76, 75, 74, 73, 72, 71, 70, 69, 68, 67, 66, 65, 64,
   63, 62, 61, 60, 59, 58, 57, 56, 55, 54, 53, 52, 51, 50, 49, 48,
   47, 46, 45, 44, 43, 42, 41, 40, 39, 38, 37, 36, 35, 34, 33, 32,
   31, 30, 29, 28, 27, 26, 25, 24, 23, 22, 21, 20, 19, 18, 17, 16,
   15, 14, 13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

def productIndexBlocks : Fin 16 → Array (Fin 128) :=
  ![productIndexBlock00, productIndexBlock01, productIndexBlock02, productIndexBlock03,
   productIndexBlock04, productIndexBlock05, productIndexBlock06, productIndexBlock07,
   productIndexBlock08, productIndexBlock09, productIndexBlock10, productIndexBlock11,
   productIndexBlock12, productIndexBlock13, productIndexBlock14, productIndexBlock15]

theorem productIndexBlocks_size (s : Fin 16) :
    (productIndexBlocks s).size = 1024 := by
  fin_cases s <;> rfl

def productIndex (i j : Fin 128) : Fin 128 :=
  (productIndexBlocks ⟨i.val / 8, by omega⟩)[(i.val % 8) * 128 + j.val]'(by
    rw [productIndexBlocks_size]
    have hj := j.isLt; have hi := Nat.mod_lt i.val (by decide : 0 < 8)
    omega)

def witnessAData : Array (Fin 128) :=
  #[1, 3, 3, 1, 16, 16, 1, 16, 16, 16, 16, 2, 16, 16, 2, 1,
   16, 16, 1, 16, 16, 16, 16, 2, 16, 16, 2, 1, 2, 2, 4, 12,
   12, 7, 15, 15, 7, 15, 15, 4, 12, 12, 1, 1, 1, 1, 3, 3,
   1, 127, 110, 1, 117, 100, 91, 73, 2, 82, 64, 2, 1, 91, 82, 1,
   73, 64, 127, 117, 2, 110, 100, 2, 1, 2, 2, 4, 36, 36, 7, 39,
   39, 7, 39, 39, 4, 36, 36, 1, 1, 1, 1, 3, 3, 1, 117, 100,
   1, 127, 110, 82, 64, 2, 91, 73, 2, 1, 82, 91, 1, 64, 73, 117,
   127, 2, 100, 110, 2, 1, 2, 2, 4, 60, 60, 7, 63, 63, 7, 63,
   63, 4, 60, 60, 1, 1, 1, 1, 110, 127, 1, 100, 117, 1, 9, 9,
   8, 28, 28, 8, 31, 31, 1, 8, 8, 1, 28, 31, 36, 27, 31, 39,
   27, 28, 1, 28, 31, 60, 27, 31, 63, 27, 28, 127, 117, 8, 110, 100,
   8, 1, 1, 1, 1, 100, 117, 1, 110, 127, 1, 9, 9, 8, 31, 31,
   8, 28, 28, 1, 8, 8, 1, 31, 28, 39, 27, 28, 36, 27, 31, 1,
   31, 28, 63, 27, 28, 60, 27, 31, 117, 127, 8, 100, 110, 8, 1, 1,
   1, 73, 91, 2, 64, 82, 2, 8, 28, 28, 8, 31, 31, 2, 10, 10,
   8, 8, 2, 36, 31, 27, 39, 28, 27, 2, 28, 31, 60, 31, 27, 63,
   28, 27, 2, 28, 31, 2, 2, 2, 91, 82, 8, 73, 64, 8, 64, 82,
   2, 73, 91, 2, 8, 31, 31, 8, 28, 28, 2, 10, 10, 8, 8, 2,
   39, 28, 27, 36, 31, 27, 2, 31, 28, 63, 28, 27, 60, 31, 27, 2,
   31, 28, 2, 2, 2, 82, 91, 8, 64, 73, 8]

def witnessA (i : Fin 315) : Fin 128 :=
  witnessAData[i.val]'(by change i.val < 315; exact i.isLt)

def witnessBData : Array (Fin 128) :=
  #[1, 4, 4, 1, 16, 16, 1, 16, 16, 16, 16, 1, 16, 16, 1, 1,
   16, 16, 1, 16, 16, 16, 16, 1, 16, 16, 1, 1, 8, 8, 9, 12,
   12, 9, 12, 12, 9, 12, 12, 9, 12, 12, 8, 8, 8, 1, 4, 4,
   1, 127, 127, 1, 127, 127, 110, 110, 1, 110, 110, 1, 1, 110, 110, 1,
   110, 110, 127, 127, 1, 127, 127, 1, 1, 8, 8, 9, 28, 28, 9, 28,
   28, 9, 28, 28, 9, 28, 28, 8, 8, 8, 1, 4, 4, 1, 127, 127,
   1, 127, 127, 110, 110, 1, 110, 110, 1, 1, 110, 110, 1, 110, 110, 127,
   127, 1, 127, 127, 1, 1, 8, 8, 9, 28, 28, 9, 28, 28, 9, 28,
   28, 9, 28, 28, 8, 8, 8, 1, 91, 91, 1, 91, 91, 1, 4, 4,
   2, 36, 36, 2, 36, 36, 1, 8, 8, 1, 64, 64, 35, 64, 64, 35,
   64, 64, 1, 64, 64, 35, 64, 64, 35, 64, 64, 127, 127, 1, 127, 127,
   1, 8, 8, 8, 1, 91, 91, 1, 91, 91, 1, 4, 4, 2, 36, 36,
   2, 36, 36, 1, 8, 8, 1, 64, 64, 35, 64, 64, 35, 64, 64, 1,
   64, 64, 35, 64, 64, 35, 64, 64, 127, 127, 1, 127, 127, 1, 8, 8,
   8, 82, 82, 1, 82, 82, 1, 2, 36, 36, 2, 36, 36, 1, 4, 4,
   8, 8, 1, 35, 64, 64, 35, 64, 64, 1, 64, 64, 35, 64, 64, 35,
   64, 64, 1, 64, 64, 8, 8, 8, 117, 117, 1, 117, 117, 1, 82, 82,
   1, 82, 82, 1, 2, 36, 36, 2, 36, 36, 1, 4, 4, 8, 8, 1,
   35, 64, 64, 35, 64, 64, 1, 64, 64, 35, 64, 64, 35, 64, 64, 1,
   64, 64, 8, 8, 8, 117, 117, 1, 117, 117, 1]

def witnessB (i : Fin 315) : Fin 128 :=
  witnessBData[i.val]'(by change i.val < 315; exact i.isLt)

def chosenRep : Fin 315 := 4

def chosenWitness : Fin 128 := 16

/-- Eight-row closure check, leaving the table data shared by all shards. -/
def closureCheck (s : Fin 16) : Bool :=
  decide (∀ k : Fin 8, let i : Fin 128 := ⟨s.val * 8 + k.val, by omega⟩;
    rowAt (inverseIndex i) = (rowAt i)⁻¹ ∧
    ∀ j : Fin 128, rowAt (productIndex i j) = rowAt i * rowAt j)

/-- Fifteen rows of pairwise distinctness tests for the right cosets. -/
def separationCheck (s : Fin 21) : Bool :=
  decide (∀ k : Fin 15, let i : Fin 315 := ⟨s.val * 15 + k.val, by omega⟩;
    ∀ j : Fin 315, i < j → treeCheck ((repAt i)⁻¹ * repAt j) = false)

end LisiSabatini.SymmetricEightCertificates
