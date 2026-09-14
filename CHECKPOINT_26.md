# Checkpoint 26 — reduce the last PBC containment to an offset theorem

Checkpoint 25 left one modular set-containment theorem:

```text
overlapInteraction
⊆ threeRInteractionCover.
```

Rather than mix modular arithmetic with finite-set and operator reasoning,
Checkpoint 26 expresses that statement as a pointwise offset certificate.

## Added

`LeanGioia/PeriodicOverlapContainment.lean`

with:

- `IsForwardOffset`
- `IsBackwardOffset`
- `IsStrictBackwardOffset`
- `InThreeRCoverByOffset`
- `mem_cyclicBlock_of_forwardOffset`
- `mem_backwardBlock_of_strictBackwardOffset`
- `mem_threeRInteractionCover_of_offset`
- `OverlapOffsetBound`
- `overlapInteraction_subset_threeRInteractionCover`
- `overlapInteraction_card_lt_of_offsetBound`
- `periodicOverlapModel_of_offsetBound`
- `corollary_one_from_periodic_offset_bound`

## Reduction

The remaining arithmetic theorem is now exactly:

```text
OverlapOffsetBound N R
```

meaning every site in an overlapping range-`R` block is either

```text
< 2R forward from the selected start
```

or

```text
< R into the backward side.
```

From that pointwise statement Lean derives the set containment, the `3R`
cardinality bound, the separated witness, Table I Row 1, and Corollary 1.

## Next checkpoint

Checkpoint 27 can focus only on proving `OverlapOffsetBound` from the
`cyclicBlock` membership equations and `3R < N`.

## Build

```bash
lake build
```
