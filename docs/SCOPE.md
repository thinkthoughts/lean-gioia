# Scope: Formal Statements, Supplied Specifications, and Physical Comparison

This document records the interpretation boundary of the repository in
affirmative terms.

## Formalized statements

The repository contains Lean-checked definitions and theorem chains for:

- W-state and support constructions;
- operator and eigenstate layers used by the argument;
- pure-creation and creation-string constructions;
- single-creation and higher-creation coefficient constraints under stated
  eigenstate hypotheses;
- cyclic/periodic overlap geometry and witness construction;
- mixed normal-ordered Row-One reasoning;
- support fibers for higher-creation families;
- invariance of duplicate-free creation strings under equality of finite
  creator support;
- aggregation of coefficients over equal-support fibers;
- vanishing of represented-support aggregate coefficients under stated
  hypotheses;
- transport of aggregate results into the mixed expansion;
- the final CP52 vacuum-eigenstate conclusion.

The theorem signature provides the authoritative reading point for each checked
implication.

## Normal-ordered representation specification

The final CP52 theorem works with the operator represented as a finite
normal-ordered family:

```lean
mixedNormalOrderedOperator Ω mixedCoeff term
```

This representation is a supplied starting specification for the checked
CP52 route.

The source-to-Lean comparison can therefore record explicitly:

```text
source extensive-local operator
        ↓
source / basis representation argument
        ↓
finite normal-ordered family
        ↓
mixedNormalOrderedOperator
```

This named boundary keeps the source operator language and the Lean operator
representation visible as distinct reading points connected by an explicit
representation specification.

## Geometry and separation specifications

The final theorem includes:

```lean
hN3 : 3 ≤ N
hNR : 3 * R < N
```

These numeric hypotheses specify the finite-size and separation regime used by
the periodic-overlap geometry and witness construction.

The final route also receives periodic-overlap placement/support data through
the supplied `start` map and block-containment hypothesis:

```lean
∀ k : κ,
  (higherCreators k).toFinset ⊆ cyclicBlock N R (start k)
```

Together these specifications provide the geometry used to construct the
higher-creation witness data.

## Representation bridge

Two supplied specifications carry the main representation content of the
CP47–CP52 transport.

### Mixed-support coverage

```lean
HigherCreationMixedSupportCovered term higherCreators
```

For every higher pure-creation term in the mixed expansion, this supplies a
representative external higher-creation index with the same finite creator
support.

This is an existence/coverage specification.

### Aggregate representation matching

```lean
PureCreationAggregateRepresentationMatches
  mixedCoeff term singleCoeff higherCoeff higherCreators
```

This connects mixed-expansion coefficients to:

- the corresponding single-creation coefficient for singleton creator terms;
- the support-fiber aggregate coefficient for higher pure-creation terms.

Together, coverage and aggregate representation matching specify the bridge
from the external single/higher families into the mixed normal-ordered
expansion.

## Additional supplied specifications

The final theorem also works from explicit specifications including:

- the single-creation eigenstate hypothesis;
- the higher-creation-family eigenstate hypothesis;
- `HigherCreationFamilyListSupport`;
- duplicate-free (`Nodup`) higher creator lists;
- `NonidentityNormalOrderedFamily`.

These specifications define the remaining admissible inputs to the final
checked derivation.

## CP47–CP52 representation result

The CP47–CP52 route organizes higher-creation terms by finite creator support.

For a support `S`, the operator-visible coefficient is represented by:

```lean
higherCreationAggregateCoeff higherCoeff higherCreators S
```

Equal duplicate-free creator supports specify the same creation-string
operator, and their externally indexed coefficients are collected in the
support-fiber aggregate.

The final route therefore places the aggregate coefficient at the operator
representation boundary and uses support coverage to connect mixed
higher-creation terms to represented supports.

## Physical comparison layer

Physical application supplies additional reading points connecting the formal
objects and hypotheses to a measured or modeled system.

Relevant evidence can specify:

- which experimental state corresponds to the formal state object;
- which measured or modeled transformation corresponds to a formal operator;
- the source basis argument supporting the finite normal-ordered
  representation;
- parameter values and measurement intervals;
- experimental uncertainties and calibration;
- the physical basis for locality or overlap specifications;
- the mapping between source notation and Lean representation;
- implementation or device-level observables associated with the theorem's
  quantities.

These reading points provide the comparison layer between a checked formal
implication and a particular physical application.

## Evidence chain

The repository can be read through the following specification flow:

```text
source specification
    → normal-ordered representation specification
    → engineering / mathematical objects
    → measurable or formal states

geometry / separation specifications
    → PeriodicOverlapCreationModel
    → HigherCreationWitnessData
    → checked support-fiber aggregate-zero result
    → representation bridge
    → MixedRowOneCondition
    → checked vacuum-eigenstate conclusion
    → physical comparison at specified reading points
```

Leading specifications constrain admissible generalizations.

Admissible generalizations trail leading specifications.
