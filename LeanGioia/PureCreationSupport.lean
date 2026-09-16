import LeanGioia.PureCreationClassification

/-!
# LeanGioia.PureCreationSupport

Checkpoint 39: bridge the list-level higher-creation classification from
Checkpoint 38 to the finite-set support cardinality used by the verified
higher-creation machinery.

Checkpoint 38 proves that a nonempty creator list is either a singleton
list or has length at least two.  The higher-creation theorems are stated
using the cardinality of the creator support finset.

Under the existing `Nodup` hypothesis these quantities agree exactly.
This checkpoint records that representation bridge without changing the
creator syntax or introducing a new indexing scheme.

The remaining boundary is identification of a higher pure-creation mixed
term, together with its coefficient, with the indexed higher-creation
family used by `PureCreationSectorBridge`.
-/

namespace LeanGioia

/--
For a duplicate-free creator list, list length and finite-set support
cardinality agree.
-/
theorem creatorSupport_card_eq_length_of_nodup
    {N : Nat}
    {xs : List (Fin N)}
    (hnodup : xs.Nodup) :
    xs.toFinset.card = xs.length := by
  exact List.toFinset_card_of_nodup hnodup

/--
A duplicate-free creator list with at least two creator positions has
finite-set support of cardinality at least two.
-/
theorem creatorSupport_card_ge_two_of_length_ge_two
    {N : Nat}
    {xs : List (Fin N)}
    (hnodup : xs.Nodup)
    (hlen : 2 ≤ xs.length) :
    2 ≤ xs.toFinset.card := by
  rw [List.toFinset_card_of_nodup hnodup]
  exact hlen

/--
For a duplicate-free pure-creation term, the higher branch from
Checkpoint 38 supplies exactly the support-cardinality condition used by
the higher-creation sector.
-/
theorem pureCreationTerm_support_card_ge_two_of_length_ge_two
    {N : Nat}
    {t : NormalOrderedTerm N}
    (_hann : t.annihilators = [])
    (hnodup : t.creators.Nodup)
    (hlen : 2 ≤ t.creators.length) :
    2 ≤ t.creators.toFinset.card := by
  exact creatorSupport_card_ge_two_of_length_ge_two
    hnodup hlen

/--
Combining Checkpoints 38 and 39: a duplicate-free nonempty pure-creation
term is either represented by a singleton creator list or has creator
support of cardinality at least two.
-/
theorem pureCreationTerm_single_or_support_card_ge_two
    {N : Nat}
    {t : NormalOrderedTerm N}
    (hann : t.annihilators = [])
    (hcre : t.creators ≠ [])
    (hnodup : t.creators.Nodup) :
    (∃ j : Fin N, t.creators = [j]) ∨
      2 ≤ t.creators.toFinset.card := by
  rcases pureCreationTerm_single_or_length_ge_two hann hcre with
    hsingle | hhigher
  · exact Or.inl hsingle
  · exact Or.inr
      (pureCreationTerm_support_card_ge_two_of_length_ge_two
        hann hnodup hhigher)

end LeanGioia
