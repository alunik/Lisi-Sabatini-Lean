module

public import LisiSabatini.ImprimitiveBundleAction

/-!
# The graph identity for an imprimitive bundle action

This generic identity is used by both the publication one-orbit argument
and the legacy labelled-palette construction.  It does not depend on the
labelled multi-orbit machinery.
-/

@[expose] public section

noncomputable section

namespace LisiSabatini

universe uI uR uW

variable {I : Type uI} {R : Type uR} {W : Type uW}
variable [Semiring R] [AddCommGroup W] [Module R W]

namespace ImprimitiveLinearActionData

variable {K : Subgroup
    (LinearMap.GeneralLinearGroup R (I → W))}
variable {L : Subgroup (LinearMap.GeneralLinearGroup R W)}

/-- The exact bundle action sends a point on the graph of `x` to the point
on the graph of `g • x` over the permuted block. -/
theorem bundleMap_graph
    (D : ImprimitiveLinearActionData K L)
    (g : K) (x : I → W) (i : I) :
    D.bundleMap g (i, x i) =
      (D.blockPerm g i, (g.1 • x) (D.blockPerm g i)) := by
  apply Prod.ext
  · rfl
  · have hi := D.action_apply g x (D.blockPerm g i)
    simpa [bundleMap] using hi.symm

end ImprimitiveLinearActionData
end LisiSabatini
