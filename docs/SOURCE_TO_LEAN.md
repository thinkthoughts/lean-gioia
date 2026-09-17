# Source to Lean

## Reading point

This document maps the source argument behind Corollary 1 of Lei Gioia, Sanjay Moudgalya, and Olexei I. Motrunich, *Distinct Types of Parent Hamiltonians for Quantum States: Insights from the W State as a Quantum Many-Body Scar* (arXiv:2510.24713v3), to the checked Lean development in `lean-gioia`.

The mapping distinguishes **source statement → source representation → Lean specification → checked derivation → physical comparison**.

The central reading point is:

> An extensive-local operator is represented in the paper by a finite-range, normal-ordered hard-core-boson operator-string basis. In Lean, the corresponding mixed normal-ordered representation is supplied together with explicit geometry, support, eigenstate, and representation specifications. The checked route derives the vacuum eigenstate conclusion using support-fiber aggregate coefficients.

## 1. Source target: Corollary 1

The source target is Sec. III.C:

> **Corollary 1.** If |W⟩ is an eigenstate of an extensive-local operator, then |0̄⟩ is also an eigenstate.

The paper routes this conclusion through Appendix C and Table I. Pure-creation terms have zero amplitudes; consequently the nonidentity normal-ordered basis terms that contribute contain at least one annihilation operator. Those terms annihilate |0̄⟩, while the identity contribution supplies the vacuum eigenvalue.

The Lean endpoint is:

```lean
corollary_one_from_periodic_overlap_aggregate_closed
```

with conclusion

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

This is the formal Corollary-1 reading point for the represented operator family.

## 2. Source operator specification

The paper begins from an extensive-local operator of the form

\[
H = \sum_j h^{[j]},
\]

where the local terms have bounded norm and finite spatial support.

Sec. III.B introduces a basis for finite-range local operators on an N-qubit periodic chain. The on-site ingredients are identity, hard-core-boson creation `s†`, annihilation `s`, and `s†s`. The resulting strings have normal-ordered form

\[
s^\dagger_{j_1}\cdots s^\dagger_{j_n}s_{k_1}\cdots s_{k_m}.
\]

The paper identifies this as a valid full basis and emphasizes its normal-ordered character with respect to |0̄⟩. It expands an extensive-local G satisfying `G|W⟩ = λ|W⟩` as a sum over distinct finite-range operator strings.

### Source-to-representation bridge

```text
extensive-local operator
        ↓
Definition 1: finite-range local operator basis
        ↓
normal-ordered creation / annihilation strings
        ↓
Eq. (17): expansion of G
```

Appendix C further states that a Hamiltonian initially written in an undetermined basis, such as the original extensive-local form, can be rewritten in the creation/annihilation basis of Definition 1.

Thus the normal-ordered representation is a specified source representation of the extensive-local operator.

## 3. Source W state and vacuum

The paper uses

\[
|Wangle = rac{1}{\sqrt N}\sum_{j=1}^{N}s_j^\dagger|ar0angle,
\qquad
|ar0angle=|0angle^{\otimes N}.
\]

The corresponding Lean layer is organized around qubit/basis states, vacuum, single-excitation states, and `wState`.

## 4. Table I: central source specification

Table I classifies constraints imposed by `G|W⟩ = λ|W⟩` according to creation number n and annihilation number m.

For Corollary 1, the decisive row is:

```text
n ≥ 1
m = 0
pure creation
coefficient = 0
```

The Lean development isolates this pure-creation sector because the vacuum conclusion follows once its operator-visible contribution is zero.

## 5. Appendix C locality argument

Appendix C proves that pure-creation terms are forbidden for a finite-range extensive-local operator having |W⟩ as an eigenstate.

For n ≥ 2, applying a pure-creation string to |W⟩ creates an (n+1)-particle state. A site is chosen sufficiently far from the finite creator support; locality prevents another range-R term from cancelling that product state.

For n = 1, a second cancellation can initially be contemplated, so the proof introduces a third sufficiently separated site. The resulting product state forces the coefficient to zero.

The paper records the sufficient geometric bound

\[
N > 3R.
\]

This is the direct source counterpart of:

```lean
hNR : 3 * R < N
```

The final Lean theorem also carries:

```lean
hN3 : 3 ≤ N
```

for the single-creation coefficient argument.

## 6. Lean geometry and witness layer

The higher-creation support is constrained by:

```lean
hcreators :
  ∀ k : κ,
    (higherCreators k).toFinset ⊆
      cyclicBlock N R (start k)
```

together with `hNR : 3 * R < N`.

These specifications construct:

```text
PeriodicOverlapCreationModel
        ↓
HigherCreationWitnessData
```

A witness records `witnessSite`, `atLeastTwo`, `nodup`, `witnessOutside`, and `locality`. This formalizes the source move of selecting a site outside the finite creator region and excluding cancellation by competing local terms.

## 7. Single-creation branch

Inputs include:

```lean
hN3 : 3 ≤ N

hSingleEig :
  IsEigenstate
    (singleCreationOperator singleCoeff)
    (wState N) singleEig
```

The checked theorem

```lean
single_creation_coefficients_zero_of_eigenstate
```

yields `singleCoeff = 0`.

This corresponds to the special n = 1 part of Appendix C's pure-creation argument.

## 8. Higher-creation branch

The higher branch uses:

```lean
hHigherEig :
  IsEigenstate
    (higherCreationFamilyOperator higherCoeff higherCreators)
    (wState N) higherEig
```

plus finite-range geometry, support, and `Nodup` specifications.

Witness construction feeds:

```lean
all_higherCreation_aggregate_coefficients_zero_of_eigenstate
```

and yields zero support-fiber aggregate coefficient on every represented higher-creation support.

## 9. Representation refinement: coefficient → support-fiber aggregate

The paper writes Table I in a linearly independent operator-string basis and states the pure-creation condition coefficient-by-coefficient.

The Lean development exposed a representation issue whenever an external family index can present the same duplicate-free finite creator support more than once. Equal duplicate-free creator supports specify the same formal creation-string operator:

```lean
creationString_eq_of_toFinset_eq
```

Therefore the represented operator sees the sum of coefficients over all external indices carrying that support.

The formal definitions are:

```lean
higherCreationSupportFiber creators S
higherCreationAggregateCoeff coeff creators S
```

giving:

```text
external coefficient labels
        ↓
finite creator support
        ↓
common creation-string operator
        ↓
support-fiber aggregate coefficient
```

Accordingly, CP47–CP52 replace an indexing-level injectivity condition with an operator-level aggregate statement.

```text
source:
linearly independent basis-string coefficient = 0

Lean represented family:
operator-visible support-fiber aggregate coefficient = 0
```

This is a representation refinement of the source statement at the level where the formal operator is evaluated.

## 10. Representation bridge into the mixed expansion

### `HigherCreationMixedSupportCovered`

This specifies that every higher pure-creation support in the mixed normal-ordered representation is represented by the higher-creation family.

It transports aggregate-zero from represented supports to the higher pure-creation supports actually appearing in the mixed expansion.

### `PureCreationAggregateRepresentationMatches`

This specifies the coefficient correspondence:

```text
single creator:
mixed coefficient = single coefficient

two or more creators:
mixed coefficient = support-fiber aggregate coefficient
```

These are substantive representation specifications connecting the source-style normal-ordered mixed expansion to the isolated Lean coefficient proofs.

## 11. Construction of `MixedRowOneCondition`

CP52 splits each pure-creation mixed term into:

```text
single creator
    or
two-or-more creators
```

The single branch uses `singleCoeff = 0`. The higher branch uses aggregate zero on the mixed higher support together with `PureCreationAggregateRepresentationMatches`.

The result is:

```lean
MixedRowOneCondition mixedCoeff term
```

This is the formal Table-I Row-1 reading point for the supplied mixed normal-ordered representation.

## 12. Vacuum conclusion

The final step is:

```lean
vacuum_eigenstate_of_mixedRowOne
```

using the derived `MixedRowOneCondition` and:

```lean
hnonid : NonidentityNormalOrderedFamily term
```

to obtain:

```lean
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

This mirrors the source argument: after the pure-creation sector is eliminated, each nonidentity contributing normal-ordered term contains an annihilation operator and annihilates the vacuum; the identity contribution specifies the eigenvalue.

## 13. End-to-end source-to-Lean map

```text
SOURCE

extensive-local operator H = Σ_j h^[j]
        ↓
Definition 1
finite-range hard-core-boson operator-string basis
        ↓
normal-ordered strings (s† ... s†)(s ... s)
        ↓
Eq. (17): G as sum of distinct basis strings
        ↓
G|W⟩ = λ|W⟩
        ↓
Table I / Appendix C
pure-creation sector constrained to zero
        │
        │ source locality geometry: N > 3R
        ↓

LEAN

mixedNormalOrderedOperator
        │
        ├── single branch
        │     hN3 + single eigenstate
        │              ↓
        │       singleCoeff = 0
        │
        └── higher branch
              hNR + cyclic-block containment
              + family support + Nodup
                       ↓
              PeriodicOverlapCreationModel
                       ↓
              HigherCreationWitnessData
                       ↓
              represented-support aggregate zero
                       ↓
              HigherCreationMixedSupportCovered
                       ↓
              aggregate zero on mixed higher supports

single zero
 + higher aggregate zero
 + PureCreationAggregateRepresentationMatches
        ↓
MixedRowOneCondition
        ↓
vacuum_eigenstate_of_mixedRowOne
        ↓
vacuum eigenstate conclusion
        ↓
COROLLARY 1 READING POINT
```

## 14. Source / specification / checked-result ledger

| Layer | Item | Reading point |
|---|---|---|
| Source | Extensive-local operator | Paper specification |
| Source | Finite-range hard-core-boson basis | Definition 1 |
| Source | Normal-ordered strings | Eqs. (10)–(15) |
| Source | Extensive-local expansion | Eq. (17) |
| Source | W eigenstate relation | Eq. (16) |
| Source | Pure-creation coefficients vanish | Table I / Appendix C |
| Source | Separation scale | Appendix C: N > 3R sufficient |
| Source | Vacuum eigenstate | Corollary 1 |
| Lean | W-state / vacuum objects | Formalized |
| Lean | Normal-ordered term/operator layer | Formalized |
| Lean | Single-creation zero | Checked |
| Lean | Cyclic finite-range geometry | Checked |
| Lean | Higher-creation witness construction | Checked |
| Lean | Creation string determined by duplicate-free support | Checked |
| Lean | Support-fiber aggregation | Checked |
| Lean | Represented-support aggregate zero | Checked |
| Lean | Mixed-support coverage transport | Checked |
| Lean | Aggregate representation match | Explicit specification |
| Lean | `MixedRowOneCondition` | Derived |
| Lean | Vacuum eigenstate conclusion | Checked |
| Comparison | Source basis ↔ Lean mixed representation | Source-to-Lean reading point |
| Comparison | Source coefficient ↔ Lean aggregate coefficient | Representation refinement |

## 15. Evidence discipline

### Source-supported

The paper supplies the extensive-local starting operator, finite-range operator-string basis, normal-ordered expansion, W-state eigenvalue condition, Table I pure-creation constraint, finite-range separation argument, and Corollary 1.

### Lean-specified

The formal route makes explicit cyclic block geometry, finite creator lists and duplicate-free support, eigenstate hypotheses for isolated pure-creation families, mixed-support coverage, coefficient correspondence, and the nonidentity normal-ordered family specification.

### Lean-derived

The checked development derives single-creation coefficient zero, finite-range witness data, equality of creation strings on equal duplicate-free support, support-fiber aggregation, aggregate coefficient zero without support-map injectivity, aggregate zero on mixed higher supports, `MixedRowOneCondition`, and the vacuum eigenstate conclusion.

## 16. Seminar reading point

The CU seminar materials place Gioia's work in a broader program around renormalization, symmetries, anomalies, stable critical quantum phases, and quantum-state preparation.

That seminar framing supplies research context. The W-state parent-Hamiltonian paper supplies the direct mathematical source for the CP52 Corollary-1 route.

```text
seminar
    → research context / motivation

W-state parent-Hamiltonian paper
    → direct source specification

lean-gioia
    → formal representation + checked derivation
```

## 17. Current reading point

At CP52, the proof architecture closes with:

```lean
corollary_one_from_periodic_overlap_aggregate_closed
```

The end-to-end formal route from the stated periodic-overlap, eigenstate, support, and representation hypotheses to the Corollary-1 vacuum eigenstate conclusion uses **support coverage plus support-fiber aggregate coefficients** as the operator-visible representation of the higher pure-creation sector.

The source-to-Lean comparison is now:

```text
extensive-local source operator
        ↓
source-supported normal-ordered basis
        ↓
explicit Lean representation specifications
        ↓
finite-range geometry and witness construction
        ↓
operator-visible aggregate coefficient constraints
        ↓
MixedRowOneCondition
        ↓
checked vacuum eigenstate conclusion
```

This is the repository's source-to-formal reading point after CP52.
