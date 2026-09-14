# Checkpoint 22 — derive higher-creation witness data from finite-range support geometry

Appendix C.1.a chooses a site `l` far from the selected range-`R`
pure-creation support.  A competing range-`R` term that contains `l`
cannot also overlap the selected support.  The paper notes that its
distance-based argument can be made with a fixed system-size/range
separation condition.

Checkpoint 22 replaces the per-coefficient `HigherCreationWitnessData`
assumption with one finite-range support model.

## Added

`LeanGioia/RangeLocality.lean`

with:

- `FiniteRangeCreationModel`
- `finiteRange_exists_witness_outside_interaction`
- `finiteRange_witness_outside_creators`
- `finiteRange_separatedLocalCompetitor`
- `higherCreationWitnessData_of_finiteRange`
- `all_higherCreationWitnessData_of_finiteRange`
- `corollary_one_from_finiteRange_creation_model`

## Model

For every higher pure-creation term the model stores:

```text
support i
interaction i
```

with the structural specifications:

```text
creator sites ⊆ support i
support i ⊆ interaction i

support k overlaps support i
→ support k ⊆ interaction i

card (interaction i) < N
```

The last condition guarantees a site outside the interaction neighborhood.

## Derived locality

Lean chooses

```text
l ∉ interaction i
```

and proves:

```text
l ∉ creators i
```

and, for every competing term `k`,

```text
l ∈ creators k
→ Disjoint (creators k) (creators i).
```

This is exactly `SeparatedLocalCompetitor`, the locality consequence that
was previously supplied manually in Checkpoints 14--17.

## Source alignment

The source assumes every creator list lies in a contiguous region of size
at most `R` and chooses `l` far from that region; it states that this
prevents cancellation by a different range-`R` term.  The paper notes
that `N > 3R` suffices for the presented distance arguments.

Checkpoint 22 formalizes the finite-neighborhood combinatorics behind that
step, but does not yet prove that a concrete cyclic contiguous range-`R`
interval has an interaction neighborhood of size at most `3R`.

## Remaining boundary

The remaining geometric specialization is now:

```text
periodic contiguous support of range ≤ R
N > 3R
---------------------------------------
FiniteRangeCreationModel
```

That is the natural target for Checkpoint 23.

## Build

```bash
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- `HigherCreationWitnessData` is generated from one support/locality model;
- the Corollary-1 assembly no longer receives per-term locality witnesses
  as independent hypotheses.
