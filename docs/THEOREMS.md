# Manuscript-to-Lean correspondence

All declarations below are in the `LisiSabatini` namespace. The core
entrypoint is `import LisiSabatini`; the odd-order corollaries require
`import LisiSabatini.FeitThompsonApplications`.

| Manuscript result | Declaration | Source |
| --- | --- | --- |
| Property $(*)$ | `SylowCoreAttainment` | [SylowCoreAttainment.lean](../LisiSabatini/SylowCoreAttainment.lean) |
| Normal-subgroup inheritance, Lemma 2.1 | `SylowCoreAttainment.of_normal_subgroup` | [SylowCoreAttainmentNormal.lean](../LisiSabatini/SylowCoreAttainmentNormal.lean) |
| Translated regular orbits, Proposition 2.3 | `exists_translated_regular_sylows` | [NilpotentTranslatedRegularity.lean](../LisiSabatini/NilpotentTranslatedRegularity.lean) |
| Main solvable theorem | `hasLisiSabatini_of_solvable_of_normal_quotients` | [GoodSolvable.lean](../LisiSabatini/GoodSolvable.lean) |
| Strong conclusion of the main theorem | `strongLisiSabatini_of_solvable_of_quotientSylowCoreAttainment` | [GoodSolvable.lean](../LisiSabatini/GoodSolvable.lean) |
| Odd-order corollary | `hasLisiSabatini_of_odd` | [FeitThompsonApplications.lean](../LisiSabatini/FeitThompsonApplications.lean) |
| Nilpotent subgroup in an odd-order group | `nilpotentSelfIntersectionInFitting_of_odd` | [FeitThompsonApplications.lean](../LisiSabatini/FeitThompsonApplications.lean) |
| Every alternating group | `hasLisiSabatini_alternatingGroup` | [PaperAlternating.lean](../LisiSabatini/PaperAlternating.lean) |
| Every symmetric group | `hasLisiSabatini_symmetricGroup` | [PaperSymmetric.lean](../LisiSabatini/PaperSymmetric.lean) |

## Exact hypotheses and conclusions

The main theorem assumes a finite solvable group and property $(*)$ for
**every normal quotient**, including the group itself. It supplies the
original inclusion-minimality conclusion, and its strong form attains all
prescribed prime cores with a common conjugator. The condition on every
quotient has not been removed.

Proposition 2.3 allows arbitrary fields and modules. It assumes a faithful
completely reducible action of a finite nilpotent group, an individual
regular vector for each selected Sylow subgroup, and independently chosen
translations. The resulting common vector satisfies all translated
regularity conditions. No finite-field or dimension hypothesis is added.

The alternating and symmetric theorems quantify over every natural-number
degree and every prescribed family of Sylow subgroups at distinct primes.
Alternating degrees at least five also have simultaneous trivial mixed
intersections. The corresponding symmetric result excludes degree eight;
the $S_8$ proof establishes inclusion-minimality through an index-two
argument using the $A_8$ certificate. Small degrees retain their actual
prime cores.

The odd-order results assume only finiteness and odd group order.
Solvability is discharged by `OddOrder.feitThompson` from the pinned
dependency, not by a new axiom.

## Relationship to the written proofs

The formal group proof uses induction through an elementary abelian minimal
normal subgroup. The translated-orbit proof uses irreducible induction,
semisimple assembly, a finite invariant span and affine-subspace avoidance.
It does not formalize the manuscript's later tensor/determinant proof.
The finite-degree arguments use kernel-checked certificates and exact
counting bounds; external search programs are not proof oracles.

The formalization does not include the external Burness–Huang theorem
for nonalternating finite simple groups. It also makes no claim to settle
the unrestricted solvable conjecture or the assumption $(*)$ only for the
original group.
