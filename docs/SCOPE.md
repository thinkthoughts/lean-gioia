# Scope: Formalized, Assumed, and Out of Scope

This file is a guardrail for interpreting the repository.

## Formalized

The repository contains Lean-checked definitions and theorem chains for the
mathematical model used in the project, including:

- W-state and support constructions;
- operator/eigenstate layers used by the argument;
- pure-creation and creation-string constructions;
- single-creation and higher-creation coefficient constraints under the stated
  eigenstate hypotheses;
- cyclic/periodic overlap geometry and witness construction;
- mixed normal-ordered Row-One reasoning;
- support fibers for higher-creation families;
- invariance of duplicate-free creation strings under equality of finite
  creator support;
- aggregation of coefficients over equal-support fibers;
- vanishing of represented-support aggregate coefficients under the stated
  hypotheses;
- transport of those aggregate results into the mixed expansion;
- the final CP52 vacuum-eigenstate conclusion.

The authoritative scope is always the theorem signature.

## Assumed in the final CP52 theorem

The final theorem takes explicit hypotheses rather than deriving every premise
from physics.

These include, in particular:

- the size/spacing inequalities appearing in the theorem;
- the single-creation eigenstate hypothesis;
- the higher-creation-family eigenstate hypothesis;
- the supplied periodic-overlap placement/support data;
- `HigherCreationFamilyListSupport`;
- duplicate-free (`Nodup`) higher creator lists;
- `HigherCreationMixedSupportCovered`;
- `PureCreationAggregateRepresentationMatches`;
- `NonidentityNormalOrderedFamily`.

The formal proof establishes the conclusion **conditional on these
specifications**.

## What CP47–CP52 removes

The final reduced theorem does not assume:

```lean
Function.Injective
  (fun k => (higherCreators k).toFinset)
```

The proof instead uses support-fiber aggregate coefficients.

This is a reduction of a representation/indexing assumption. It should not be
described as experimental evidence about a physical system.

## Out of scope

Unless separately supplied and verified elsewhere, the repository does not by
itself establish:

- that a particular experimental material or device satisfies the formal
  hypotheses;
- that the chosen operator model is uniquely forced by a physical system;
- measured parameter values;
- experimental error bars or calibration;
- microscopic causal mechanisms;
- implementation performance;
- a claim that formal derivability substitutes for empirical validation;
- a complete formalization of all content in the source seminar or related
  research program.

## Interpretation rule

Use the following reading discipline:

```text
specified measurement ≠ specified cause
formal theorem ≠ experimental validation
representation coverage ≠ physical identification
mathematical closure ≠ empirical closure
```

The project is strongest where its boundaries remain explicit: Lean checks the
formal implication; experiments and source evidence determine where the
hypotheses apply.
