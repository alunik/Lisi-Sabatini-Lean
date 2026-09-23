module

public import LisiSabatini.FiniteCertificates.PermutationTable
public import LisiSabatini.FiniteCertificates.TableCertificate
public import LisiSabatini.FiniteCertificates.ConjugacySampling

/-!
# Composable checked bad-conjugator counts

Literal sample lists can be checked in bounded chunks. Their lengths add
without evaluating a full symmetric-group enumeration.
-/

@[expose] public section

namespace LisiSabatini.SymmetricFiniteCertificates

open LisiSabatini.FiniteCertificates

variable {G : Type*} [Group G] [DecidableEq G]

/-- Count sample entries which the sound trivial-intersection test does not accept. -/
def uncheckedCount (s : Finset G) (l : List G) : ℕ :=
  (l.filter fun x ↦ goodCheck s x = false).length

theorem uncheckedCount_append (s : Finset G) (a b : List G) :
    uncheckedCount s (a ++ b) = uncheckedCount s a + uncheckedCount s b := by
  simp only [uncheckedCount, List.filter_append, List.length_append]

theorem card_unchecked_finsetOfNodupList (s : Finset G) (l : List G) (h : l.Nodup) :
    ((finsetOfNodupList l h).filter fun x ↦ goodCheck s x = false).card =
      uncheckedCount s l := rfl

end LisiSabatini.SymmetricFiniteCertificates
