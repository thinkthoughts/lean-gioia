# Checkpoint 6 — finite-range separation geometry

Appendix C.1.a chooses an extra occupied site sufficiently far from the
support of a range-`R` pure-creation term.  The paper explicitly notes that
`N > 3R` is sufficient for the separation arguments presented there.

Checkpoint 6 formalizes the finite counting core of that geometry.

## Added

`LeanGioia/Geometry.lean`

with:

- `ExclusionRegion N R`
- `IsSeparated`
- `exists_site_outside_of_card_lt`
- `exists_separated_site`
- `SeparatedSite`
- `chooseSeparatedSite`
- `addSeparatedExcitation`

## Formal boundary

An `ExclusionRegion` represents the selected local support together with the
two range-`R` buffer zones relevant to the paper's cancellation argument.
The current checkpoint records the paper-level geometric fact needed next:

```text
excluded sites ≤ 3R
3R < N
----------------
there exists a separated site
```

This does **not yet** assert that the exclusion region for every concrete
normal-ordered local operator has cardinality at most `3R`; that connection
belongs to the concrete support encoding in the next step.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- Lean derives existence of a separated site from the `N > 3R` bound.

## Next checkpoint

Checkpoint 7 should connect a concrete pure-creation support to an
`ExclusionRegion`, use the separated site to build the higher-particle
basis configuration, and prove that other range-`R` local terms contribute
zero amplitude there.  That will produce the `UncancellableWitness`
required by Checkpoint 5.
