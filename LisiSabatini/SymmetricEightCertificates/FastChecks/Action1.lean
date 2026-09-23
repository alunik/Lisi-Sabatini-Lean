module

public import LisiSabatini.SymmetricEightCertificates.FastData

/-! Generated generator-closure and spanning-tree certificate data. -/

@[expose] public section

namespace LisiSabatini.SymmetricEightCertificates.FastData

open LisiSabatini.FiniteCertificates

set_option maxRecDepth 100000

set_option maxHeartbeats 0 in
/- This certificate proof unfolds finite checks; scope its elaboration budget here. -/
theorem actionCheck_1 : actionCheck 1 = true := by
  decide +kernel

end LisiSabatini.SymmetricEightCertificates.FastData
