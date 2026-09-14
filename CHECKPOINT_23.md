# Checkpoint 23 — explicit periodic range blocks and the `3R < N` bound

The source uses contiguous finite-range supports on a one-dimensional
periodic chain.  Appendix C.1.a chooses a witness site far from a selected
range-`R` support, and a footnote states that `N > 3R` is sufficient for
the presented distance argument.

Checkpoint 23 introduces explicit cyclic blocks on `Fin N`.

## Added

`LeanGioia/PeriodicRange.lean`

with:

- `cyclicBlock`
- `cyclicBlock_card_le`
- `mem_cyclicBlock_iff`
- `PeriodicRangeCreationModel`
- `periodic_interaction_card_lt`
- `PeriodicRangeCreationModel.toFiniteRange`
- `all_higherCreationWitnessData_of_periodicRange`
- `corollary_one_from_periodicRange_creation_model`

## Cyclic support

A block beginning at `start` is constructed as

```text
{ (start + t) mod N | t < width }.
```

So the formal support passes through the PBC link directly.

Lean proves

```text
card (cyclicBlock N width start) ≤ width.
```

Therefore:

```text
3 * R < N
→ card (cyclicBlock N (3 * R) start) < N.
```

This discharges the abstract cardinality premise from Checkpoint 22.

## Current geometric boundary

`PeriodicRangeCreationModel` still carries one geometric statement:

```text
two range-R blocks overlap
→ competing block ⊆ selected 3R interaction block.
```

This is now the only modular-interval fact separating the model from a
fully constructed one-dimensional PBC range geometry.

The source supports this locality picture: basis sites lie in a contiguous
region of size at most `R`, PBC strings may cross the `N → 1` link, and the
Appendix-C distance argument may be taken with `N > 3R`.

## Next checkpoint

Checkpoint 24 should prove `overlap_localizes` directly for cyclic blocks.
That will let us construct `PeriodicRangeCreationModel` from only block
starts and creator-support containment.

## Build

```bash
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- cyclic PBC support is explicit;
- the `3R < N` hypothesis proves the interaction neighborhood is not the
  whole chain;
- Checkpoint 22's abstract cardinality assumption is removed.
