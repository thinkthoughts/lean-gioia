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

## Supplied specifications in the final CP52 theorem

The final theorem works from explicit specifications including:

- the size and spacing inequalities in the theorem signature;
- the single-creation eigenstate hypothesis;
- the higher-creation-family eigenstate hypothesis;
- periodic-overlap placement and support data;
- `HigherCreationFamilyListSupport`;
- duplicate-free (`Nodup`) higher creator lists;
- `HigherCreationMixedSupportCovered`;
- `PureCreationAggregateRepresentationMatches`;
- `NonidentityNormalOrderedFamily`.

These specifications define the admissible inputs to the final checked
derivation.

## CP47–CP52 representation result

The CP47–CP52 route organizes higher-creation terms by finite creator support.

For a support `S`, the operator-visible coefficient is represented by:

```lean
higherCreationAggregateCoeff higherCoeff higherCreators S
```

Equal duplicate-free creator supports specify the same creation-string
operator, and their externally indexed coefficients are collected in the
support-fiber aggregate.

The final theorem therefore uses:

```lean
HigherCreationMixedSupportCovered term higherCreators
```

as its representation bridge: each higher pure-creation support in the mixed
expansion has a representative in the external higher family.

This distinguishes **support coverage** from **support uniqueness** and places
the aggregate coefficient at the operator representation boundary.

## Physical comparison layer

Physical application supplies additional reading points connecting the formal
objects and hypotheses to a measured or modeled system.

Relevant evidence can specify:

- which experimental state corresponds to the formal state object;
- which measured or modeled transformation corresponds to a formal operator;
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
    → engineering / mathematical objects
    → measurable or formal states
    → explicit hypotheses
    → checked derivation
    → theorem conclusion
    → physical comparison at specified reading points
```

Leading specifications constrain admissible generalizations.

Admissible generalizations trail leading specifications.
