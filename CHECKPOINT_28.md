# Checkpoint 28 — canonical coordinates for an overlapping block

Checkpoint 27 converted cyclic-block membership into canonical offset
inequalities.

Checkpoint 28 applies that conversion to the exact overlap hull.

## Added

`LeanGioia/OverlapCoordinates.lean`

with:

- `OverlapCoordinateWitness`
- `overlapCoordinateWitness_of_mem`
- `CanonicalOverlapCoordinates`
- `canonicalOverlapCoordinates_of_mem`
- `CanonicalOverlapImpliesCover`
- `overlapOffsetBound_of_canonical`

## Verified extraction

For every

```text
x ∈ overlapInteraction N R start
```

Lean extracts a competing start `c` and shared site `y` with

```text
cyclicOffset N start y < R
cyclicOffset N c y     < R
cyclicOffset N c x     < R.
```

These are precisely the three inequalities behind the informal picture of
two overlapping range-`R` intervals.

## Remaining theorem

The final arithmetic statement is now:

```text
CanonicalOverlapImpliesCover N R
```

i.e. those three canonical inequalities imply that `x` is in either the
forward `2R` block or the backward `R` block.

Once this is proved, `OverlapOffsetBound` follows immediately.

## Build

```bash
lake build
```
