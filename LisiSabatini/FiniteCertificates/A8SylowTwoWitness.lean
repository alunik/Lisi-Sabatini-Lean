module

public import LisiSabatini.FiniteCertificates.A8FingerprintData

/-!
# An explicit trivial intersection for a Sylow 2-subgroup of A8

This certificate uses one concrete permutation and 63 nonidentity probes.
The group-theoretic conclusion follows from the sound fingerprint checker.
-/

@[expose] public section

namespace LisiSabatini.FiniteCertificates.A8SylowTwoWitness

open A8Rows A8FingerprintData

abbrev G := A8Rows.G

local instance : DecidableEq G := alternatingCodeDecidableEq_fin8
local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

set_option maxRecDepth 100000

def witnessPerm : Equiv.Perm (Fin 8) where
  toFun := ![1, 2, 0, 4, 7, 6, 3, 5]
  invFun := ![2, 0, 1, 6, 3, 7, 5, 4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def witness : G := ⟨witnessPerm, by
  change Equiv.Perm.sign witnessPerm = 1
  decide +kernel⟩

set_option maxHeartbeats 0 in
-- Kernel evaluation checks all 63 nonidentity row entries.
theorem witness_fingerprint_good :
    fingerprintGoodCheck fingerprint mask2 row2Probes witness = true := by
  decide +kernel

/-- The row order is the full 2-part of the actual alternating group. -/
theorem card_sylow2 : Nat.card A8Rows.sylow2 = 64 := by
  exact (card_checkedSubgroup row2 row2_closed).trans row2_card

/-- One kernel-checked pair of disjoint Sylow 2-subgroups. -/
theorem sylow2_inter_witness_eq_bot : sylowInter A8Rows.sylow2 witness = ⊥ := by
  apply checkedSylow_good row2 row2_closed row2_card_factorization
  exact fingerprintGoodCheck_sound row2 fingerprint mask2 row2Probes
    row2_cover row2_mask witness witness_fingerprint_good

end LisiSabatini.FiniteCertificates.A8SylowTwoWitness
