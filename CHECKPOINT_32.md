# Checkpoint 32 — Periodic overlap coordinates

## Goal

Consume the Checkpoint-31 `Fin N` / natural-residue bridge in the explicit
periodic-range geometry introduced at Checkpoint 23.

## Result

`PeriodicOverlap.lean` proves that a shared point of two range-`R` cyclic
blocks, together with any point of the competing block, satisfies the
closed `CanonicalOverlapInThreeRRegion` conclusion under `3 * R < N`.

This is intentionally a coordinate theorem rather than a claim that every
overlapping range-`R` block is contained in the one-sided block
`cyclicBlock N (3 * R) start`.  The existing canonical theorem has a
forward-or-backward conclusion, so CP32 preserves exactly that statement
instead of strengthening it without proof.

## Build

```bash
lake build LeanGioia.PeriodicOverlap
```

If the target builds, add the module to the project/root import as appropriate
for the repository's existing module layout, then run the full build.

## Next checkpoint

Use the CP32 coordinate result to decide and formalize the correct geometric
interaction object for the periodic model: either prove the required
one-sided containment with the necessary orientation hypotheses, or define a
symmetric `3R` interaction region matching the forward-or-backward canonical
coordinate theorem.
