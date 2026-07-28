module

public import LisiSabatini.Alternating
public import LisiSabatini.NilpotentIntersectionApplications
public import LisiSabatini.Symmetric

/-!
# Formalized Sylow-intersection results

The library exposes two related but distinct developments:

* the original Lisi--Sabatini property for finite solvable groups of odd
  order, and for alternating and symmetric groups of degree at least forty;
  and
* mixed three-Sylow-core synchronization, hence the same-row
  three-conjugates property, for every finite solvable group.

For alternating and symmetric groups of degree at least forty, the library
also exports mixed two-row Sylow synchronization with trivial intersection.
Consequently any two nilpotent subgroups admit a relative conjugate with
trivial intersection; the corresponding three-subgroup statement follows
immediately.  The nilpotent-subgroup consequences of the solvable
synchronization theorems are exported here as well.
-/
