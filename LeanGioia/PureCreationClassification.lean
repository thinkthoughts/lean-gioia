import LeanGioia.PureCreationBridge

/-!
# LeanGioia.PureCreationClassification

Checkpoint 38: expose the intrinsic classification of nonempty
pure-creation terms in a mixed normal-ordered expansion.

`PureCreationSectorBridge` currently packages two logically distinct tasks:

1. classify a nonempty creator list as a single-creation or
   higher-creation term;
2. identify that term and its coefficient with the externally supplied
   single/higher creation families.

The first task is intrinsic to `NormalOrderedTerm` and can be discharged
without additional representation data.

This checkpoint isolates that structural fact at the list level.
The remaining boundary is representation of the higher-creation branch
by the indexed family used by the verified higher-creation theorem.
-/

namespace LeanGioia

/--
A nonempty creator list is either exactly one creator or contains at
least two creator positions.
-/
theorem creatorList_single_or_length_ge_two
    {N : Nat}
    (xs : List (Fin N))
    (hxs : xs ≠ []) :
    (∃ j : Fin N, xs = [j]) ∨ 2 ≤ xs.length := by
  cases xs with
  | nil =>
      exact False.elim (hxs rfl)
  | cons j rest =>
      cases rest with
      | nil =>
          left
          exact ⟨j, rfl⟩
      | cons k tail =>
          right
          simp

/--
Every nonidentity pure-creation mixed term therefore has an intrinsic
single-versus-higher list-level classification.
-/
theorem pureCreationTerm_single_or_length_ge_two
    {N : Nat}
    {t : NormalOrderedTerm N}
    (_hann : t.annihilators = [])
    (hcre : t.creators ≠ []) :
    (∃ j : Fin N, t.creators = [j]) ∨
      2 ≤ t.creators.length := by
  exact creatorList_single_or_length_ge_two
    t.creators hcre

end LeanGioia
