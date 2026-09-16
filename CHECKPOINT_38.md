# Checkpoint 38 — Pure-creation classification

## Goal

Separate the intrinsic classification of mixed pure-creation terms from
the external representation data carried by `PureCreationSectorBridge`.

`PureCreationSectorBridge` currently performs two jobs:

1. classifies each nonidentity pure-creation mixed term as belonging to
   the single-creation or higher-creation sector;
2. identifies the term's creator list and coefficient with the externally
   supplied sector family.

Checkpoint 38 closes the first, purely structural part.

## Result

For a nonempty creator list `xs : List (Fin N)`, Lean proves:

```lean
(∃ j : Fin N, xs = [j]) ∨ 2 ≤ xs.length
```

The result is also lifted directly to the creator list of a
`NormalOrderedTerm`.

Thus every mixed term in the pure-creation branch has an intrinsic
list-level classification:

- exactly one creator: `creators = [j]`;
- higher creation: `2 ≤ creators.length`.

## Why list length

This checkpoint deliberately classifies at the `List` level rather than
using `(creators.toFinset).card`.

The existing higher-creation machinery supplies `Nodup` separately.
Using `toFinset.card` before that condition is available could erase
repeated creator positions. For example, `[j, j]` has list length two but
singleton finite-set support.

Keeping CP38 list-based preserves the syntax already carried by
`NormalOrderedTerm` without silently strengthening the representation.

## Remaining boundary

`PureCreationSectorBridge` still contains genuine representation data.

The higher branch must be connected to the indexed higher-creation family
used by the verified higher-creation theorem while preserving the creator
list, its coefficient, and the hypotheses required by the higher-creation
cancellation theorem, including creator-support injectivity and `Nodup`.

Checkpoint 39 should determine whether that representation can be
constructed canonically from the mixed expansion or whether an explicit
representation hypothesis remains appropriate.

## File

`LeanGioia/PureCreationClassification.lean`

## Verification

```bash
lake env lean LeanGioia/PureCreationClassification.lean
```

After this succeeds, CP38 can be recorded as verified.
