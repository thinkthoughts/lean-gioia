# Formalization Specification 001

## Status

**Closed specification reading point: CP52**

This document is the authoritative specification for the first `lean-gioia` formalization target. It replaces the earlier `SPEC.md`.

The specification records the scientific target, source representation, formal objects, leading assumptions, representation bridge, checked theorem route, and completion criteria established through CP52.

---

## Source

Lei Gioia, Sanjay Moudgalya, and Olexei I. Motrunich,

**Distinct Types of Parent Hamiltonians for Quantum States: Insights from the W State as a Quantum Many-Body Scar**

arXiv:2510.24713v3.

Primary source locations for this specification:

- Sec. III.B — operator basis and constraints;
- Definition 1 — finite-range hard-core-boson operator-string basis;
- Eqs. (16)–(17) — W-state eigenvalue relation and operator expansion;
- Table I — coefficient constraints;
- Sec. III.C — Corollary 1;
- Appendix C — proof of Theorem 1 and the pure-creation obstruction.

Detailed source mapping is recorded in:

```text
docs/SOURCE_TO_LEAN.md
```

---

## Scientific target

For a finite one-dimensional periodic qubit chain, formalize the operator-basis and locality argument underlying the following source result:

> If the W state is an eigenstate of an extensive-local operator, then the vacuum state is also an eigenstate.

The formal target is the Corollary-1 route through the normal-ordered finite-range operator representation used by the source.

---

## Source representation specification

The source begins with an extensive-local operator and introduces a finite-range hard-core-boson operator-string basis.

The relevant normal-ordered strings have the form

\[
s^\dagger_{j_1}\cdots s^\dagger_{j_n}
s_{k_1}\cdots s_{k_m}.
\]

Definition 1 supplies the finite-range operator basis, and Eq. (17) expands the extensive-local operator over distinct basis strings.

Appendix C states that an operator initially supplied in an undetermined extensive-local basis can be rewritten in this creation/annihilation basis.

The source-to-formal representation reading point is therefore:

```text
extensive-local source operator
        ↓
finite-range hard-core-boson basis
        ↓
normal-ordered creation / annihilation strings
        ↓
finite mixed normal-ordered representation
        ↓
mixedNormalOrderedOperator
```

The Lean development begins its Corollary-1 derivation at this represented normal-ordered reading point.

---

## Source coefficient specification

The source assumes

\[
G|W\rangle=\lambda|W\rangle.
\]

Table I classifies the resulting constraints by:

- `n` — number of creation operators;
- `m` — number of annihilation operators.

The decisive Corollary-1 sector is:

```text
n ≥ 1
m = 0
pure creation
coefficient = 0
```

Once the pure-creation contribution is zero, every contributing nonidentity normal-ordered term contains an annihilation operator and therefore annihilates the vacuum.

The identity term supplies the vacuum eigenvalue.

---

## Leading formal objects

The formalization specifies:

- finite qubit configurations;
- vacuum configurations and the vacuum ket;
- single-excitation configurations;
- the W state;
- linear operators and eigenstate relations;
- creation and annihilation operators;
- creation strings;
- normal-ordered terms;
- mixed normal-ordered operators;
- single-creation operators;
- higher-creation operator families;
- cyclic finite-range geometry;
- finite creator supports;
- support witnesses;
- support fibers;
- support-fiber aggregate coefficients.

These objects separate state, operator, geometry, coefficient, and representation specifications.

---

## Leading assumptions

The closed CP52 theorem carries explicit assumptions corresponding to the represented Corollary-1 route.

### Finite geometry

```lean
hN3 : 3 ≤ N
```

and

```lean
hNR : 3 * R < N
```

The latter follows the explicit sufficient separation bound used in the detailed Appendix C argument.

### Single-creation eigenstate specification

```lean
hSingleEig :
  IsEigenstate
    (singleCreationOperator singleCoeff)
    (wState N) singleEig
```

### Higher-creation eigenstate specification

```lean
hHigherEig :
  IsEigenstate
    (higherCreationFamilyOperator
      higherCoeff higherCreators)
    (wState N) higherEig
```

### Finite-range support specification

```lean
hcreators :
  ∀ k : κ,
    (higherCreators k).toFinset ⊆
      cyclicBlock N R (start k)
```

### Higher-creation family support

```lean
hsupport :
  HigherCreationFamilyListSupport higherCreators
```

### Duplicate-free creator lists

```lean
hNodup :
  ∀ k : κ,
    (higherCreators k).Nodup
```

### Mixed-support coverage

```lean
hcovered :
  HigherCreationMixedSupportCovered
    term higherCreators
```

### Aggregate representation match

```lean
hrep :
  PureCreationAggregateRepresentationMatches
    mixedCoeff term
    singleCoeff higherCoeff higherCreators
```

### Nonidentity mixed-family specification

```lean
hnonid :
  NonidentityNormalOrderedFamily term
```

Hermiticity is not required for this primary result.

---

## Geometry specification

The source Appendix C uses finite interaction range and spatial separation to isolate product-state contributions that competing local terms cannot cancel.

The Lean development represents this with cyclic blocks and explicit witness data.

The geometry route is:

```text
hNR : 3 * R < N
        +
creator support ⊆ cyclicBlock N R
        ↓
PeriodicOverlapCreationModel
        ↓
HigherCreationWitnessData
```

`HigherCreationWitnessData` records:

```text
witnessSite
atLeastTwo
nodup
witnessOutside
locality
```

This is the formal separation layer used by the higher-creation coefficient argument.

---

## Pure-creation decomposition

The formal route divides the source Table-I pure-creation row into two proof branches.

### Single creator

```text
hN3
    +
single-creation W eigenstate
    ↓
single_creation_coefficients_zero_of_eigenstate
    ↓
singleCoeff = 0
```

### Two or more creators

```text
finite-range geometry
    ↓
witness data
    +
higher-creation W eigenstate
    ↓
support-fiber aggregate coefficient = 0
```

The branches are recombined at the mixed normal-ordered representation.

---

## Representation refinement

The source writes the pure-creation constraint coefficient-by-coefficient in a linearly independent operator-string basis.

The Lean higher-creation family permits an external index to present creator lists. Equal duplicate-free finite creator supports specify the same creation-string operator.

The checked theorem

```lean
creationString_eq_of_toFinset_eq
```

establishes the relevant representation equality.

Accordingly, define:

```lean
higherCreationSupportFiber creators S
```

and:

```lean
higherCreationAggregateCoeff coeff creators S
```

The operator-visible coefficient associated with a common support is the sum over its support fiber.

The formal reading point is:

```text
external family indices
        ↓
duplicate-free finite creator support
        ↓
common creation-string operator
        ↓
support-fiber aggregate coefficient
```

Thus the higher-creation result is stated at the operator-visible level:

```text
represented support
        ↓
aggregate coefficient = 0
```

rather than requiring injective external support indexing.

---

## Representation bridge

Two specifications connect the isolated pure-creation analyses to the mixed normal-ordered operator.

### `HigherCreationMixedSupportCovered`

Every higher pure-creation support appearing in the mixed representation is represented by the higher-creation family.

This supports the transport:

```text
aggregate zero on represented supports
        ↓
aggregate zero on mixed higher supports
```

### `PureCreationAggregateRepresentationMatches`

This specifies the coefficient correspondence.

For one creator:

```text
mixed coefficient
    =
single-creation coefficient
```

For two or more creators:

```text
mixed coefficient
    =
support-fiber aggregate coefficient
```

These are leading representation specifications for the final mixed-operator theorem.

---

## Table-I Row-1 formal reading point

The single and higher branches combine to derive:

```lean
MixedRowOneCondition mixedCoeff term
```

The construction is:

```text
pure-creation mixed term
        ↓
single creator OR two-or-more creators

single:
singleCoeff = 0
        ↓
mixed coefficient = 0

higher:
mixed-support aggregate zero
        ↓
mixed coefficient = 0
```

`MixedRowOneCondition` is the formal reading point corresponding to the pure-creation row of Table I for the represented mixed operator.

---

## Vacuum eigenstate route

Once `MixedRowOneCondition` is established, the final operator argument is:

```text
MixedRowOneCondition
        +
NonidentityNormalOrderedFamily
        ↓
vacuum_eigenstate_of_mixedRowOne
        ↓
vacuum eigenstate
```

The checked conclusion is:

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

This mirrors the source mechanism: nonidentity contributing terms contain annihilation and annihilate the vacuum; the identity contribution specifies eigenvalue `Ω`.

---

## Final theorem

The closed end-to-end theorem is:

```lean
corollary_one_from_periodic_overlap_aggregate_closed
```

Its conclusion is:

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

The theorem route uses support coverage plus support-fiber aggregate coefficients as the operator-visible representation of the higher pure-creation sector.

---

## Checked derivation

The CP52 dependency route is:

```text
SOURCE REPRESENTATION
extensive-local operator
        ↓
normal-ordered finite-range basis
        ↓
mixedNormalOrderedOperator

SINGLE BRANCH
hN3 + single W eigenstate
        ↓
singleCoeff = 0

HIGHER BRANCH
hNR + cyclic-block containment
        ↓
PeriodicOverlapCreationModel
        ↓
HigherCreationWitnessData
        +
higher W eigenstate
        ↓
represented-support aggregate zero
        ↓
HigherCreationMixedSupportCovered
        ↓
mixed-support aggregate zero

REPRESENTATION BRIDGE
single zero
    +
mixed higher aggregate zero
    +
PureCreationAggregateRepresentationMatches
        ↓
MixedRowOneCondition
        ↓
vacuum_eigenstate_of_mixedRowOne
        ↓
COROLLARY 1 READING POINT
```

---

## Success criteria

Specification 001 is complete at a reading point where:

- the source operator-basis route is identified;
- the source Table-I pure-creation condition is represented explicitly;
- the source finite-range separation mechanism has a formal cyclic-geometry counterpart;
- single-creation coefficient zero is checked;
- higher-creation support witnesses are checked;
- equal duplicate-free supports specify equal creation-string operators;
- support-fiber aggregation is formalized;
- higher aggregate coefficients are proved zero without an injective support-index specification;
- aggregate zero is transported to mixed higher supports;
- `MixedRowOneCondition` is derived;
- the vacuum eigenstate conclusion is kernel-checked;
- the final theorem contains no `sorry` or `admit`;
- the final theorem uses no project-specific axioms;
- the repository builds successfully.

These criteria were satisfied at CP52.

---

## Verification reading point

At the CP52 freeze:

```text
File-level Lean check                 PASS
Target Lake build                     PASS
Full repository build                PASS
Final theorem printed                 PASS
Creator-support injectivity input     ABSENT
Project-specific axioms               ABSENT
sorry / admit                         NONE
```

The final theorem's reported foundational axioms are:

```text
propext
Classical.choice
Quot.sound
```

The frozen CP52 repository reading point is commit:

```text
dd903c7
```

Reproduction commands and audit details are recorded in:

```text
docs/REPRODUCIBILITY.md
```

---

## Evidence discipline

### Source-supported

The source supplies:

- the extensive-local starting operator;
- the finite-range hard-core-boson basis;
- the normal-ordered creation/annihilation expansion;
- the W-state eigenvalue condition;
- Table I's pure-creation constraint;
- the Appendix C locality/separation argument;
- Corollary 1.

### Lean-specified

The formal route supplies explicit:

- cyclic geometry;
- finite creator supports;
- duplicate-free creator lists;
- isolated pure-creation eigenstate hypotheses;
- mixed-support coverage;
- aggregate representation matching;
- nonidentity normal-ordered family structure.

### Lean-derived

The checked route derives:

- single-creation zero;
- finite-range witness data;
- support equality of creation strings;
- support-fiber aggregation;
- aggregate coefficient zero;
- mixed-support aggregate zero;
- `MixedRowOneCondition`;
- the vacuum eigenstate conclusion.

Admissible generalizations trail these leading specifications.

---

## Physical comparison layer

Physical comparison proceeds from specified source and formal reading points.

Relevant evidence includes:

- the paper's extensive-local operator definition;
- its finite-range hard-core-boson representation;
- its locality and separation construction;
- its Table-I coefficient constraints;
- the Lean theorem signatures and checked dependency route.

The formal result can therefore be compared to the source at the levels of operator representation, geometry, coefficient constraints, and eigenstate conclusion.

Specified formal measurement and representation remain distinct from specified physical cause.

---

## Subsequent formalization targets

Specification 001 establishes the Corollary-1 route.

Further specifications can independently target:

- the ground-state obstruction;
- the full parent-Hamiltonian decomposition;
- type I / II / III classification;
- asymptotic QMBS results;
- momentum-related results;
- RG, symmetry, and anomaly results;
- additional source-to-Lean bridges from the seminar and related papers.

Each subsequent target should begin with its own source statement, leading specifications, formal objects, measurable or formal states, and success criterion.

---

## Repository reading point

The documentation set for Specification 001 is:

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

`SPECIFICATION.md` is the authoritative specification.

`SOURCE_TO_LEAN.md` records the source comparison.

`THEOREM_MAP.md` records the checked dependency structure.

`REPRODUCIBILITY.md` records the build and theorem audit.

`CHECKPOINT_INDEX.md` records the proof-development reading points.

`SCOPE.md` records the formal, representation, geometry, and physical-comparison layers.

---

## Closure

**Formalization Specification 001 closes at CP52.**

The scientific target is represented by a source-supported normal-ordered operator basis and a checked Lean route from explicit finite-range, eigenstate, support, and representation specifications to the vacuum eigenstate conclusion.

The principal representation refinement established during formalization is:

> The operator-visible higher pure-creation quantity is the support-fiber aggregate coefficient carried by a common finite creator support.

This refinement supports the closed Corollary-1 theorem without requiring injective indexing of higher-creation supports.
