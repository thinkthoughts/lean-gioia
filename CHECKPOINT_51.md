# Checkpoint 51 — Pure-Creation Aggregate Representation

## Status

**Target:** integrate the support-aggregate higher-creation conclusion with the
mixed normal-ordered representation boundary without restoring creator-support
injectivity.

**Artifact:** `LeanGioia/PureCreationAggregateRepresentation.lean`

## Purpose

Checkpoint 51 is an **integration checkpoint**.

The historical Row-1 route packages the higher-creation conclusion as

```lean
higherCoeff = 0
```

inside `TableIRowOneConclusion`.

That statement is appropriate for the earlier route where the map

```lean
k ↦ (higherCreators k).toFinset
```

is injective.

CP47--CP50 establish a different representation boundary. Equal finite creator
support identifies the same duplicate-free creation-string operator, so the
operator sees the sum of coefficients over a support fiber rather than an
arbitrary individual coefficient.

The natural higher-sector conclusion is therefore

```lean
higherCreationAggregateCoeff
  higherCoeff higherCreators S = 0
```

for the relevant finite creator support `S`.

CP51 transports that representation-invariant conclusion to the already
verified mixed Row-1 and Corollary-1 machinery.

## New representation interface

CP51 introduces

```lean
structure PureCreationAggregateRepresentationMatches ...
```

The single branch retains the CP42 match

```lean
mixedCoeff i = singleCoeff j
```

for a singleton creator list `[j]`.

The higher branch instead records

```lean
mixedCoeff i =
  higherCreationAggregateCoeff
    higherCoeff higherCreators
    (term i).creators.toFinset
```

for a structurally classified higher pure-creation term.

Thus the mixed expansion is matched to the coefficient actually visible after
support-fiber aggregation.

## Historical interface retained

CP51 does **not** modify:

```lean
TableIRowOneConclusion
```

or

```lean
PureCreationRepresentationMatches
```

Those remain valid interfaces for the earlier injective-support theorem chain.

The repository therefore retains both routes:

```text
historical route

higher support injectivity
        ↓
individual higherCoeff k = 0
        ↓
TableIRowOneConclusion
        ↓
PureCreationRepresentationMatches
        ↓
MixedRowOneCondition
        ↓
Corollary 1
```

and

```text
support-aggregate route

equal creator support
        ↓
creationString invariance
        ↓
support-fiber aggregation
        ↓
aggregate coefficient = 0
        ↓
PureCreationAggregateRepresentationMatches
        ↓
MixedRowOneCondition
        ↓
Corollary 1
```

## CP51 transport theorem

The theorem

```lean
mixedRowOneCondition_of_aggregate_representation_matches
```

combines:

1. zero single-creation coefficients;
2. zero higher support-aggregate coefficients;
3. the aggregate representation interface;

and derives the existing

```lean
MixedRowOneCondition mixedCoeff term
```

No modification of `MixedRowOneCondition` is required.

## CP51 Corollary-1 theorem

The theorem

```lean
corollary_one_from_aggregate_representation_matches
```

feeds the resulting mixed Row-1 condition directly into

```lean
vacuum_eigenstate_of_mixedRowOne
```

and concludes

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

The theorem contains no creator-support injectivity hypothesis.

## Important boundary

CP50 supplies aggregate-zero results at supports represented by the external
higher-creation family.

CP51 deliberately states the representation transport at the support level.

The remaining CP52 task is therefore narrow:

- instantiate the aggregate-zero premise required by the mixed representation
  from the actual higher-family support data;
- combine it with the existing single-creation zero theorem;
- connect the closed periodic-overlap model;
- state the final end-to-end theorem without `hinj`;
- perform the final build and axiom/interface audit.

CP51 should not introduce another independent mathematical construction.

## Verification

From the repository root:

```bash
lake env lean LeanGioia/PureCreationAggregateRepresentation.lean
```

A silent return to the shell prompt is the CP51 file-level PASS reading point.

Then:

```bash
lake build LeanGioia.PureCreationAggregateRepresentation
```

A successful Lake build freezes CP51.

## Next

**CP52 — final reduced periodic-overlap assembly and audit.**

The principal audit question is explicit:

```text
Does the final end-to-end theorem reach Corollary 1
without Function.Injective
  (fun k => (higherCreators k).toFinset)?
```

If yes, the CP47--CP52 reduction has closed the injectivity dependency at the
operator-visible support level.
