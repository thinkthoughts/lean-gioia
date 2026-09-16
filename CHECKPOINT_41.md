# Checkpoint 41 — Propagate Reduced Family Support

## Status

**Target:** thread the Checkpoint-40 hypothesis reduction through the already
closed periodic-overlap Corollary-1 route.

**Artifact:** `LeanGioia/PeriodicOverlapReduced.lean`

## Purpose

Checkpoint 41 is the downstream payoff from Checkpoints 38–40. The closed
periodic-overlap theorem consumes

```lean
∀ k, 2 ≤ (higherCreators k).toFinset.card
```

as an explicit input. CP40 proves that this follows from

```lean
HigherCreationFamilyListSupport higherCreators
```

together with

```lean
∀ k, (higherCreators k).Nodup
```

CP41 propagates that reduction through the existing closed Corollary-1
assembly. It changes no periodic geometry and reproves no higher-creation
cancellation theorem.

## New theorem

`corollary_one_from_periodic_overlap_list_support`

derives the old `hatLeastTwo` input internally with

```lean
higherCreationFamily_toFinset_card_ge_two
```

and then invokes

```lean
corollary_one_from_periodic_overlap_closed
```

from Checkpoint 35.

## What CP41 closes

The finite-set support lower bound is no longer independent public
mathematical data on this route:

```text
higher-family structural classification
        ↓
HigherCreationFamilyListSupport
        ↓ + Nodup
CP40: creator support card ≥ 2
        ↓
CP41: closed periodic-overlap assembly
        ↓
Corollary 1
```

## What remains explicit

CP41 preserves the higher-family index type `κ`, the higher-family
eigenstate hypothesis, creator-set injectivity, periodic support placement,
`Nodup`, and creator/coefficient matching through
`PureCreationSectorBridge`.

CP41 therefore does not claim that the representation bridge has been
eliminated.

## Verification

If needed first:

```bash
lake build LeanGioia.PureCreationFamilySupport
```

Then:

```bash
lake env lean LeanGioia/PeriodicOverlapReduced.lean
```

A silent return is the CP41 file-level PASS reading point. After verification,
commit `CHECKPOINT_41.md` and `LeanGioia/PeriodicOverlapReduced.lean`
together.
