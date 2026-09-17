# Theorem Map

## Final public theorem

```lean
LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
```

File:

```text
LeanGioia/PeriodicOverlapAggregateClosed.lean
```

Conclusion:

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

## Source-to-formal boundary

The final theorem begins after a representation reading point:

```text
source extensive-local operator
        ↓
source / basis representation argument
        ↓
finite normal-ordered family
        ↓
mixedNormalOrderedOperator
```

The source-to-Lean map specifies this connection. The theorem map below begins
with the formal representation and its explicit hypotheses.

## Final dependency map

```text
hN3 : 3 ≤ N
hNR : 3 * R < N
block-containment / support data
        │
        ▼
periodicOverlapModel_closed
        │
        ▼
PeriodicOverlapCreationModel
        │
        ▼
all_higherCreationWitnessData_of_finiteRange
        │
        ▼
HigherCreationWitnessData
        │
        ▼
all_higherCreation_aggregate_coefficients_zero_of_eigenstate
        │
        ▼
aggregate zero on each represented higher support
        │
        ├── HigherCreationMixedSupportCovered
        ▼
aggregateZero_on_mixed_higher_support
        │
        ▼
aggregate zero on each mixed higher pure-creation support
        │
        ├── PureCreationAggregateRepresentationMatches
        ├── single_creation_coefficients_zero_of_eigenstate
        ▼
MixedRowOneCondition
        │
        ▼
vacuum_eigenstate_of_mixedRowOne
        │
        ▼
Corollary-1 vacuum eigenstate conclusion
```

## Representation bridge

The final transport has two named representation specifications.

### `HigherCreationMixedSupportCovered`

Specifies that each mixed higher pure-creation support is represented by at
least one support in the external higher-creation family.

### `PureCreationAggregateRepresentationMatches`

Specifies how mixed coefficients correspond to the single-creation
coefficients and higher support-fiber aggregate coefficients.

These are the substantive bridge between the external coefficient families and
the mixed normal-ordered expansion.

## Support-aggregation subchain

### CP47 — support fibers

`HigherCreationSupportFiber.lean`

Introduces support fibers and:

```lean
higherCreationAggregateCoeff
```

The aggregate coefficient sums externally indexed coefficients whose creator
lists carry the same finite support.

### CP48 — support representation

`CreationStringSupport.lean`

Key result:

```lean
creationString_eq_of_toFinset_eq
```

For duplicate-free creator lists, equality of finite support specifies equality
of the associated creation string.

### CP49 — operator aggregation

`HigherCreationSupportAggregation.lean`

Uses CP48 to rewrite contributions in one support fiber through the same
creation-string operator and factor their coefficient sum.

### CP50 — aggregate zero

`HigherCreationAggregateZero.lean`

Key result:

```lean
all_higherCreation_aggregate_coefficients_zero_of_eigenstate
```

The higher-sector conclusion is expressed directly through the aggregate
coefficient attached to a represented support.

### CP51 — aggregate representation

`PureCreationAggregateRepresentation.lean`

Introduces:

```lean
PureCreationAggregateRepresentationMatches
```

and transports support-aggregate coefficient information into the existing
mixed Row-One / vacuum-eigenstate machinery.

### CP52 — final assembly

`PeriodicOverlapAggregateClosed.lean`

Introduces:

```lean
HigherCreationMixedSupportCovered
aggregateZero_on_mixed_higher_support
corollary_one_from_periodic_overlap_aggregate_closed
```

This closes the reduced route.

## Representation refinement

The earlier end-to-end route proceeds through individual external higher
coefficients and support injectivity.

The CP47–CP52 route specifies the mathematical quantity at the representation
boundary as the coefficient aggregate visible to the common creation-string
operator.

Accordingly, the final route uses support **coverage**: each mixed higher
support has a representative in the external higher family. Shared supports
are collected through their aggregate coefficient.
