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

## Final dependency map

```text
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

## Support-aggregation subchain

### CP47

`HigherCreationSupportFiber.lean`

Introduces support fibers and:

```lean
higherCreationAggregateCoeff
```

The aggregate coefficient is the sum of externally indexed coefficients whose
creator lists have the same finite support.

### CP48

`CreationStringSupport.lean`

Key result:

```lean
creationString_eq_of_toFinset_eq
```

For duplicate-free creator lists, equality of finite support is sufficient for
equality of the associated creation string.

### CP49

`HigherCreationSupportAggregation.lean`

Uses CP48 to rewrite all contributions in one support fiber through the same
creation-string operator and factor their coefficient sum.

### CP50

`HigherCreationAggregateZero.lean`

Key result:

```lean
all_higherCreation_aggregate_coefficients_zero_of_eigenstate
```

This is the replacement for the earlier pointwise higher-coefficient-zero step.
It does not require support-map injectivity.

### CP51

`PureCreationAggregateRepresentation.lean`

Introduces:

```lean
PureCreationAggregateRepresentationMatches
```

and transports support-aggregate coefficient information into the existing
mixed Row-One / vacuum-eigenstate machinery.

### CP52

`PeriodicOverlapAggregateClosed.lean`

Introduces:

```lean
HigherCreationMixedSupportCovered
aggregateZero_on_mixed_higher_support
corollary_one_from_periodic_overlap_aggregate_closed
```

This closes the reduced route.

## Historical comparison

The historical end-to-end theorem remains useful because it records the earlier
proof architecture. Its higher branch proves individual external coefficients
zero and therefore requires injectivity of:

```lean
fun k => (higherCreators k).toFinset
```

The CP47–CP52 route changes the mathematical quantity at the representation
boundary from an arbitrary individual coefficient to the coefficient aggregate
visible to the common creation-string operator.

That is why support coverage remains in the final theorem while support
injectivity disappears.
