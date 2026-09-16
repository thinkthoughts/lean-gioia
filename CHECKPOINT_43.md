# Checkpoint 43 — Propagate Reduced Representation to Corollary 1

## Status

**Target:** propagate the Checkpoint-42 representation reduction through the
finite mixed-expansion Corollary-1 conclusion.

**Artifact:** `LeanGioia/PureCreationRepresentationCorollary.lean`

## Purpose

Checkpoint 42 replaced the classifier-and-coverage representation machinery
used by `PureCreationSectorBridge` with the narrower
`PureCreationRepresentationMatches` interface.

It proved:

```lean
mixedRowOneCondition_of_representation_matches
```

which derives `MixedRowOneCondition` using the intrinsic single-versus-higher
classification from CP38.

The existing mixed-expansion theorem

```lean
vacuum_eigenstate_of_mixedRowOne
```

already converts `MixedRowOneCondition` plus
`NonidentityNormalOrderedFamily` into the vacuum-eigenstate conclusion.

CP43 composes those two verified interfaces.

## New theorem

```lean
corollary_one_from_representation_matches
```

takes:

- the finite mixed expansion;
- its nonidentity condition;
- single- and higher-sector coefficient data;
- the already-established `TableIRowOneConclusion`;
- `PureCreationRepresentationMatches`.

It first derives

```lean
MixedRowOneCondition mixedCoeff term
```

with CP42 and then applies

```lean
vacuum_eigenstate_of_mixedRowOne
```

to conclude

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

## What CP43 closes

The reduced representation interface now reaches the Corollary-1 conclusion:

```text
CP38 intrinsic creator-list classification
              ↓
CP42 PureCreationRepresentationMatches
              ↓
      MixedRowOneCondition
              ↓
CP43 vacuum_eigenstate_of_mixedRowOne
              ↓
          Corollary 1
```

On this route, `PureCreationSectorBridge` is no longer required by the
Corollary-1 assembly itself.

## What remains explicit

CP43 deliberately accepts `TableIRowOneConclusion` as an input. It therefore
does not yet combine the reduced representation route with the closed
periodic-overlap/higher-creation machinery that proves the single- and
higher-sector coefficients vanish.

That composition is the natural next checkpoint.

The external higher-family indexing/matching fact exposed by CP42 also
remains explicit.

## Verification

Because this file imports CP42, build its Lake object if needed:

```bash
lake build LeanGioia.PureCreationRepresentation
```

Then run:

```bash
lake env lean LeanGioia/PureCreationRepresentationCorollary.lean
```

A silent return to the shell prompt is the CP43 file-level PASS reading
point.

After verification:

```bash
git add CHECKPOINT_43.md LeanGioia/PureCreationRepresentationCorollary.lean
git commit -m "Checkpoint 43: propagate reduced representation to Corollary 1"
git push
```
