import LisiSabatini.FeitThompsonApplications

/-!
Transitive axiom audit of the separate Feit--Thompson applications.
This legacy audit entrypoint deliberately does not enter the core module root.
-/

set_option linter.hashCommand false

#print axioms OddOrder.feitThompson
#print axioms LisiSabatini.strongLisiSabatini_of_odd
#print axioms LisiSabatini.hasLisiSabatini_of_odd
#print axioms LisiSabatini.mixedStrongLisiSabatini_of_odd
#print axioms LisiSabatini.nilpotentSelfIntersectionInFitting_of_odd
#print axioms LisiSabatini.mixedNilpotentIntersectionInFitting_of_odd
