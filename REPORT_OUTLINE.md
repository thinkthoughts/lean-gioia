# Report Outline

## Provisional title

**Formalizing the W-State Locality Obstruction in Lean 4**

### Alternative working titles

- **A Lean 4 Formalization of the W-State Locality Obstruction**
- **From Locality to Vacuum Eigenstates: Formalizing a W-State Corollary in Lean 4**
- **Support-Fiber Aggregation in a Lean 4 Formalization of the W-State Locality Obstruction**

The first title is the preferred working title. The support-fiber result can emerge as the formalization contribution rather than being required in the title.

---

## Report purpose

This report documents a Lean 4 formalization of the operator-basis and locality mechanism underlying Corollary 1 of Gioia–Moudgalya–Motrunich:

> If the W state is an eigenstate of an extensive-local operator, then the vacuum state is also an eigenstate.

The report has three connected purposes:

1. **Reproduce the source mechanism** at a specified formal reading point.
2. **Expose the assumptions and representation bridge** required for a kernel-checked derivation.
3. **Document the representation refinement** from externally indexed coefficients to support-fiber aggregate coefficients as the operator-visible higher pure-creation quantity.

The report should distinguish source statements, formal specifications, checked derivations, and physical comparison throughout.

---

# 1. Introduction

## 1.1 Problem

Introduce the source setting:

- finite one-dimensional periodic qubit chain;
- W state;
- extensive-local operator;
- finite interaction range;
- W state specified as an eigenstate;
- Corollary-1 conclusion that the vacuum is also an eigenstate.

State why this is a useful formalization target: the source proof combines operator representation, locality, spatial separation, coefficient cancellation, and an eigenstate conclusion in a compact argument.

## 1.2 Formalization question

Frame the report around:

> What specifications are sufficient to reproduce the pure-creation obstruction and vacuum-eigenstate conclusion in Lean 4?

This turns the source argument into explicit formal objects and hypotheses rather than treating the prose proof as a single indivisible step.

## 1.3 Main formal result

Introduce the final theorem:

```lean
corollary_one_from_periodic_overlap_aggregate_closed
```

with conclusion:

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

State that the theorem closes the represented Corollary-1 route from finite-range geometry, W-eigenstate, support, and representation specifications.

## 1.4 Formalization contribution

Preview the central representation result:

> Equal duplicate-free creator supports specify the same creation-string operator, so an externally indexed higher-creation family is observed through the aggregate coefficient over the corresponding support fiber.

Explain that this permits the final route to use support coverage and aggregate coefficients rather than an injective indexing specification.

## 1.5 Evidence discipline

Introduce the report's recurring distinction:

```text
source statement
    → source representation
    → Lean specification
    → checked derivation
    → physical comparison
```

Reference `SPECIFICATION.md` and `docs/SOURCE_TO_LEAN.md` as the authoritative specification and source map.

---

# 2. Source Result and Corollary 1

## 2.1 W state and vacuum

Present the source W state:

\[
|W\rangle =
\frac{1}{\sqrt N}
\sum_j s_j^\dagger |\bar 0\rangle
\]

and the vacuum:

\[
|\bar 0\rangle = |0\rangle^{\otimes N}.
\]

Describe the one-excitation character of the W state relevant to the operator analysis.

## 2.2 Extensive-local operator

Introduce the source extensive-local form and bounded finite-range terms.

Keep the physical/source definition separate from the later Lean normal-ordered representation.

## 2.3 Corollary 1

State the source result:

> If \(|W\rangle\) is an eigenstate of an extensive-local operator, then \(|\bar 0\rangle\) is also an eigenstate.

Note that the primary source statement permits the operator to be non-Hermitian.

## 2.4 Why the pure-creation sector controls the corollary

Explain the source mechanism:

```text
normal-ordered nonidentity term
        ↓
pure creation
    OR
contains annihilation
```

Terms containing annihilation annihilate the vacuum.

Therefore the key source task is to constrain the pure-creation sector to zero.

---

# 3. Source Operator Representation

## 3.1 Definition 1

Describe the finite-range hard-core-boson operator-string basis.

Introduce the local ingredients:

```text
identity
creation
annihilation
number / creation-annihilation
```

## 3.2 Normal ordering

Present the generic string:

\[
s^\dagger_{j_1}\cdots s^\dagger_{j_n}
s_{k_1}\cdots s_{k_m}.
\]

Explain why its normal-ordered character relative to the vacuum is useful.

## 3.3 Eq. (16): W eigenstate relation

Introduce:

\[
G|W\rangle = \lambda |W\rangle.
\]

## 3.4 Eq. (17): operator expansion

Present the expansion over distinct finite-range basis strings.

## 3.5 Source-to-Lean representation reading point

Make the bridge explicit:

```text
extensive-local source operator
        ↓
finite-range operator-string basis
        ↓
normal-ordered expansion
        ↓
Lean mixed normal-ordered representation
```

State that the paper itself supplies the source-side basis rewriting; the Lean theorem then operates on the represented finite mixed expansion.

---

# 4. Formal Specification

## 4.1 State objects

Summarize the formal layers for:

- qubits;
- basis configurations;
- vacuum;
- single excitation;
- W state.

## 4.2 Operator objects

Summarize:

- linear operators;
- eigenstate relation;
- creation and annihilation operators;
- creation strings;
- normal-ordered terms;
- mixed normal-ordered operator.

## 4.3 Pure-creation operator families

Introduce the separate formal operators used to analyze:

- single creation;
- higher creation.

Explain why the source Table-I row is decomposed into these two proof branches.

## 4.4 Leading theorem specifications

List and explain the role of:

```lean
hN3 : 3 ≤ N
hNR : 3 * R < N
hSingleEig
hHigherEig
hcreators
hsupport
hNodup
hcovered
hrep
hnonid
```

Avoid presenting these as a flat list of technical assumptions. Group them into:

```text
geometry
eigenstate
support
representation
normal-ordered family
```

## 4.5 Specification grammar

Use the report's specification discipline:

```text
leading constraints
    → engineering / mathematical objects
    → measurable or formal states
    → admissible generalizations
```

Admissible generalizations trail leading specifications.

---

# 5. Finite-Range Cyclic Geometry

## 5.1 Source separation argument

Explain Appendix C's use of a site outside the finite creator region.

Record the detailed Appendix-C reading point:

\[
N > 3R
\]

as a sufficient condition for the separation arguments presented there.

## 5.2 Cyclic blocks

Introduce the formal cyclic-block representation of a finite-range creator region.

Use:

```lean
cyclicBlock N R (start k)
```

and:

```lean
(higherCreators k).toFinset ⊆
  cyclicBlock N R (start k)
```

## 5.3 Periodic-overlap model

Explain:

```lean
PeriodicOverlapCreationModel
```

as the formal geometry object collecting the required finite-range separation structure.

## 5.4 Witness construction

Introduce:

```lean
HigherCreationWitnessData
```

with:

```text
witnessSite
atLeastTwo
nodup
witnessOutside
locality
```

Connect each field to the source cancellation argument.

## 5.5 Reading point

Conclude the section with:

```text
finite interaction range
    + cyclic separation
        ↓
explicit witness configuration
```

This converts the source's spatial reasoning into reusable theorem data.

---

# 6. Pure-Creation Obstruction

## 6.1 Table I, Row 1

State the source condition:

```text
n ≥ 1
m = 0
    ↓
pure-creation coefficient = 0
```

## 6.2 Single-creation case

Explain the source's special `n = 1` cancellation argument.

Describe the third separated site used in Appendix C.

Map this to:

```lean
single_creation_coefficients_zero_of_eigenstate
```

and:

```lean
singleCoeff = 0
```

## 6.3 Higher-creation case

Explain the `n ≥ 2` source argument: application to the W state creates a higher-particle product state whose distant component cannot be cancelled by another finite-range term.

Map this to the witness-based Lean route.

## 6.4 Why locality is load-bearing

Emphasize that the coefficient conclusion comes from the combination:

```text
W eigenstate
    +
finite-range support
    +
separated witness
    ↓
observable higher-particle component
    ↓
coefficient constraint
```

This is the mathematical core of the locality obstruction.

---

# 7. Support-Fiber Aggregation

## 7.1 Representation problem exposed by formalization

Explain that an external family index can contain multiple creator lists representing the same duplicate-free finite support.

A coefficient attached to an external index is therefore not automatically an operator-distinguishable coefficient.

## 7.2 Equal support, equal creation-string operator

Present:

```lean
creationString_eq_of_toFinset_eq
```

and its meaning:

```text
Nodup xs
Nodup ys
xs.toFinset = ys.toFinset
        ↓
creationString xs = creationString ys
```

## 7.3 Support fibers

Define conceptually:

```lean
higherCreationSupportFiber creators S
```

as all external family indices representing support `S`.

## 7.4 Aggregate coefficient

Introduce:

```lean
higherCreationAggregateCoeff coeff creators S
```

as the coefficient sum over the support fiber.

## 7.5 Operator-visible quantity

State the report's central representation reading point:

> The operator-visible higher pure-creation quantity is the support-fiber aggregate coefficient carried by a common finite creator support.

## 7.6 Aggregate-zero theorem

Present:

```lean
all_higherCreation_aggregate_coefficients_zero_of_eigenstate
```

and explain how geometry + witnesses + W eigenstate yield zero aggregate coefficient on every represented higher support.

## 7.7 Relation to source notation

Distinguish:

```text
SOURCE
linearly independent basis-string coefficient

LEAN REPRESENTED FAMILY
support-fiber aggregate coefficient
```

Explain that the formal refinement identifies the coefficient object appropriate to the representation used by the Lean operator.

---

# 8. Representation Bridge

## 8.1 Why a bridge is required

The isolated single/higher operator analyses must be connected to the coefficients of the mixed normal-ordered representation.

## 8.2 `HigherCreationMixedSupportCovered`

Explain the coverage specification:

> Every higher pure-creation support appearing in the mixed representation has a representative in the higher-creation family.

Show the transport:

```text
represented-support aggregate zero
        ↓
mixed-support coverage
        ↓
aggregate zero on mixed higher supports
```

## 8.3 `PureCreationAggregateRepresentationMatches`

Explain the two correspondence rules.

Single creator:

```text
mixed coefficient = single coefficient
```

Higher creator:

```text
mixed coefficient =
support-fiber aggregate coefficient
```

## 8.4 Representation versus derivation

Make explicit that coverage and coefficient matching are leading representation specifications; the zero results transported through them are checked consequences.

This distinction should remain visible in theorem statements and diagrams.

---

# 9. End-to-End Corollary 1 Theorem

## 9.1 Constructing `MixedRowOneCondition`

Show the case split:

```text
pure-creation mixed term
        ↓
single
    OR
higher
```

Single branch:

```text
single coefficient zero
    + representation match
        ↓
mixed coefficient zero
```

Higher branch:

```text
mixed-support aggregate zero
    + representation match
        ↓
mixed coefficient zero
```

Therefore:

```lean
MixedRowOneCondition mixedCoeff term
```

## 9.2 Vacuum theorem

Present:

```lean
vacuum_eigenstate_of_mixedRowOne
```

and explain that every nonidentity contributing term now contains an annihilation operator.

## 9.3 Final theorem

Present:

```lean
corollary_one_from_periodic_overlap_aggregate_closed
```

and its conclusion.

## 9.4 Full dependency diagram

Use the final branched architecture:

```text
SOURCE NORMAL-ORDERED REPRESENTATION
                ↓
       mixedNormalOrderedOperator

hN3 + single W eigenstate
                ↓
        singleCoeff = 0
                │
                │
hNR + cyclic-block containment
                ↓
PeriodicOverlapCreationModel
                ↓
HigherCreationWitnessData
        + higher W eigenstate
                ↓
represented-support aggregate zero
                ↓
HigherCreationMixedSupportCovered
                ↓
mixed higher aggregate zero
                │
                │
single zero + higher aggregate zero
        + representation match
                ↓
MixedRowOneCondition
                ↓
vacuum_eigenstate_of_mixedRowOne
                ↓
COROLLARY 1
```

---

# 10. Verification and Reproducibility

## 10.1 Kernel verification

Record:

```text
File-level Lean check                 PASS
Target Lake build                     PASS
Full repository build                PASS
Final theorem printed                 PASS
Creator-support injectivity input     ABSENT
Project-specific axioms               ABSENT
sorry / admit                         NONE
```

## 10.2 Foundational axioms

Record the reported axioms:

```text
propext
Classical.choice
Quot.sound
```

## 10.3 Frozen reading point

Record CP52 commit:

```text
dd903c7
```

## 10.4 Reproduction

Refer to:

```text
docs/REPRODUCIBILITY.md
```

for exact commands.

---

# 11. Source-to-Formal Comparison

## 11.1 Source statements reproduced

Compare:

- W state;
- vacuum;
- finite-range normal-ordered basis;
- W eigenstate relation;
- Table-I pure-creation obstruction;
- locality/separation mechanism;
- vacuum eigenstate conclusion.

## 11.2 Representation specifications made explicit

Discuss:

- cyclic block containment;
- isolated single/higher eigenstate specifications;
- `Nodup`;
- mixed-support coverage;
- aggregate representation matching;
- nonidentity mixed-family structure.

## 11.3 Representation refinement

Explain the distinction between source coefficient notation and Lean's operator-visible support-fiber aggregate.

This section should avoid presenting the refinement as a correction of the source. It arises from the formal representation used in the development.

## 11.4 Reading-point discipline

Use:

```text
specified source statement
    ≠
unspecified physical generalization
```

and:

```text
specified representation
    → checked theorem
    → admissible comparison
```

---

# 12. Discussion

## 12.1 What formalization exposed

Discuss how the proof development separated:

- geometry from coefficient reasoning;
- external indexing from operator identity;
- support equality from list equality;
- representation assumptions from derived constraints;
- source physics from formal theorem signatures.

## 12.2 Aggregate coefficients as a reusable pattern

Discuss the broader mathematical pattern:

> Where multiple external descriptions specify the same formal operator object, the observable coefficient may be a fiber aggregate rather than an individual externally indexed coefficient.

Keep this as a formalization lesson unless additional applications are independently established.

## 12.3 Locality as explicit proof data

Discuss the benefit of turning informal "choose a sufficiently distant site" reasoning into a finite cyclic geometry object and witness structure.

## 12.4 Source fidelity

Explain how `SOURCE_TO_LEAN.md` supports line-by-line comparison between the source argument and the formal theorem route.

## 12.5 Formal reading point

State precisely what the final theorem establishes from its named hypotheses.

Avoid collapsing the represented normal-ordered theorem into a stronger unqualified physical claim.

---

# 13. Subsequent Work

Treat these as independent specifications rather than unfinished pieces of Specification 001.

Possible next formalization targets include:

- ground-state obstruction;
- full parent-Hamiltonian decomposition;
- type I / II / III classification;
- asymptotic QMBS results;
- momentum-related results;
- RG, symmetry, and anomaly results;
- additional seminar-to-Lean source mappings.

Each should begin from a new source statement and explicit leading specifications.

---

# 14. Conclusion

The conclusion should make three claims, each at its own evidence level.

### Source result

Gioia–Moudgalya–Motrunich derive a locality-based pure-creation obstruction leading to Corollary 1 for the W state and vacuum.

### Formal result

`lean-gioia` provides a kernel-checked route from explicit finite-range, eigenstate, support, and representation specifications to the corresponding vacuum eigenstate conclusion.

### Representation result

The formalization identifies the support-fiber aggregate coefficient as the operator-visible quantity for higher pure-creation families where multiple external indices can represent a common finite creator support.

Close with the durable specification statement:

> Admissible generalizations trail leading specifications.

---

# Proposed figures

## Figure 1 — Source-to-Lean architecture

```text
extensive-local source operator
        ↓
normal-ordered finite-range basis
        ↓
Lean representation
        ↓
geometry + eigenstate specifications
        ↓
pure-creation coefficient constraints
        ↓
MixedRowOneCondition
        ↓
vacuum eigenstate
```

## Figure 2 — Finite-range witness geometry

Show:

- periodic chain;
- creator support inside a cyclic block;
- witness site outside the support;
- finite-range locality exclusion.

This figure should be derived from the formal geometry rather than drawn as an unconstrained physical cartoon.

## Figure 3 — Support-fiber aggregation

```text
external indices
 k₁  k₂  k₃
  \   |   /
   \  |  /
 common finite support S
        ↓
common creationString
        ↓
Σ coefficients over fiber(S)
```

This is likely the report's most distinctive formalization figure.

## Figure 4 — Final theorem dependency map

Use the branched CP52 dependency diagram from Sec. 9.4.

---

# Proposed theorem/code excerpts

Keep code excerpts short and use theorem signatures rather than long proof bodies.

Recommended excerpts:

1. `creationString_eq_of_toFinset_eq`
2. `higherCreationAggregateCoeff`
3. `all_higherCreation_aggregate_coefficients_zero_of_eigenstate`
4. `HigherCreationMixedSupportCovered`
5. `PureCreationAggregateRepresentationMatches`
6. `corollary_one_from_periodic_overlap_aggregate_closed`

The report should point to repository files for full proofs.

---

# Supporting repository documents

The report should be written against the frozen documentation set:

```text
SPECIFICATION.md
README.md
docs/
  CHECKPOINT_INDEX.md
  THEOREM_MAP.md
  REPRODUCIBILITY.md
  SCOPE.md
  SOURCE_TO_LEAN.md
```

These documents specify the authoritative reading points for source comparison, theorem dependencies, verification, and scope.

---

# Drafting order

Recommended writing order:

```text
§2  Source Result
§3  Source Operator Representation
§5  Finite-Range Cyclic Geometry
§6  Pure-Creation Obstruction
§7  Support-Fiber Aggregation
§8  Representation Bridge
§9  End-to-End Theorem
§4  Formal Specification
§10 Verification
§11 Source-to-Formal Comparison
§12 Discussion
§1  Introduction
§14 Conclusion
```

Writing the technical center first should keep the introduction and conclusion constrained by the actual checked result.

---

## Outline reading point

This outline specifies the first public technical report for Formalization Specification 001.

The report's center is not the existence of a Lean translation alone. Its center is the checked route:

```text
source locality
    → explicit finite geometry
    → witness construction
    → operator-visible aggregate coefficient
    → representation bridge
    → Table-I Row-1 condition
    → vacuum eigenstate
```

That route provides the structure for the report, figures, theorem excerpts, and eventual publication decision.
