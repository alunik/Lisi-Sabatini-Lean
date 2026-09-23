module

public import LisiSabatini.GoodSolvable
public import LisiSabatini.NilpotentTranslatedRegularity
public import LisiSabatini.PaperAlternating
public import LisiSabatini.PaperSymmetric
public import LisiSabatini.SylowCoreAttainmentNormal

/-!
# Main results of the paper

The principal endpoints in namespace `LisiSabatini` are:

* `hasLisiSabatini_of_solvable_of_normal_quotients`: the conjecture for a
  finite solvable group whose every normal quotient has property (*).
* `exists_translated_regular_sylows`: translated regular orbits for a
  faithful semisimple representation of a finite nilpotent group, over
  an arbitrary field and module.
* `hasLisiSabatini_alternatingGroup` and
  `hasLisiSabatini_symmetricGroup`: the conjecture in every degree.

The stronger core-intersection conclusion is available for every
alternating group and for symmetric groups other than S8. In degree
at least five, these mixed intersections are trivial. The S8 endpoint
proves the conjecture's original inclusion-minimality conclusion.

The property-(*) equivalences, normal-subgroup inheritance and nilpotent
intersection corollaries are also exported. The external finite-simple-group
input is not formalized here. The separate import
`LisiSabatini.FeitThompsonApplications` adds the odd-order corollaries using
the pinned Feit–Thompson formalization.
-/
