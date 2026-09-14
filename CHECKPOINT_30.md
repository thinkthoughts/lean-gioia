# Checkpoint 30 — canonical offset composition

Checkpoint 29 isolated the modular composition identity as
`CanonicalOffsetComposition`.

Checkpoint 30 proves it by composing the canonical offset equations through
the shared point between two overlapping range-`R` blocks.

## Added

`LeanGioia/OffsetComposition.lean`

with:

- `cyclicOffset_compose_through_shared`
- `canonicalOffsetComposition`
- `canonicalOverlapInThreeRRegion`
- `overlapOffsetBound`

## Target

This checkpoint is intended to close the last abstract PBC arithmetic
proposition:

```text
3R < N
→ OverlapOffsetBound N R.
```

If the build passes, the periodic-overlap containment and cardinality
results can consume an actual theorem rather than an assumed proposition.

## Build

```bash
lake build
```
