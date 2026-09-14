# Checkpoint 25 — quantitative `3R` interaction cover

Checkpoint 24 defined the exact periodic overlap hull and removed the
abstract overlap-localization hypothesis.

Checkpoint 25 separates the remaining quantitative argument into a clean
finite-set bound.

## Added

`LeanGioia/PeriodicOverlapBound.lean`

with:

- `cyclicBackStart`
- `threeRInteractionCover`
- `threeRInteractionCover_card_le`
- `card_le_three_mul_of_subset_cover`
- `overlapInteraction_card_lt_of_subset_threeR`
- `periodicOverlapModel_of_threeR_cover`
- `corollary_one_from_threeR_overlap_cover`

## Quantitative result

The explicit cover is

```text
forward cyclic block of width 2R
∪
backward cyclic block of width R.
```

Lean proves

```text
card threeRInteractionCover ≤ 3R.
```

Hence:

```text
overlapInteraction ⊆ threeRInteractionCover
3R < N
--------------------------------------------
card overlapInteraction < N.
```

## Remaining geometry

The only remaining periodic arithmetic statement is now

```text
overlapInteraction N R s
⊆ threeRInteractionCover N R s.
```

This is a pure modular-interval containment lemma, with all operator and
cardinality machinery removed from the problem.

That containment is the target for Checkpoint 26.

## Build

```bash
lake build
```
