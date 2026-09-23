module

public import LisiSabatini.SymmetricEightCertificates.FastChecks.Action0
public import LisiSabatini.SymmetricEightCertificates.FastChecks.Action1
public import LisiSabatini.SymmetricEightCertificates.FastChecks.Action2
public import LisiSabatini.SymmetricEightCertificates.FastChecks.Spanning

/-! Generated generator-closure and spanning-tree certificate data. -/

@[expose] public section

namespace LisiSabatini.SymmetricEightCertificates.FastData

open LisiSabatini.FiniteCertificates

set_option maxRecDepth 100000

/- Match the equality decider already captured in the imported Boolean checks. -/
local instance fastChecksDecidableEqG : DecidableEq G := permutationCodeDecidableEq_fin8

set_option maxHeartbeats 0 in
/- This certificate proof unfolds finite checks; scope its elaboration budget here. -/
theorem action_checked : ∀ j : Fin 3, ∀ i : Fin 128,
    genAt j * rowAt i = rowAt (actionIndex j i) := by
  intro j
  have h : actionCheck j = true := by
    fin_cases j
    · exact actionCheck_0
    · exact actionCheck_1
    · exact actionCheck_2
  exact of_decide_eq_true h

set_option maxHeartbeats 0 in
/- This certificate proof unfolds finite checks; scope its elaboration budget here. -/
theorem bfs_edge_checked : ∀ k : Fin 128, 0 < k →
    rowAt (bfsAt k) = genAt (bfsGen k) * rowAt (bfsAt (bfsParent k)) :=
  of_decide_eq_true bfsEdgeCheck_checked

end LisiSabatini.SymmetricEightCertificates.FastData
