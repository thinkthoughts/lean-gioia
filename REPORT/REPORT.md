# A Formalization of the W-State Locality Obstruction

**Status:** Draft v0.1  
**Formal reading point:** Checkpoint 52  
**Report page:** `labreports.app/gioia`

## Abstract

This report presents a Lean 4 formalization of the W-state locality obstruction developed from Lei Gioia's seminar material and the corresponding source result. The source argument considers an extensive-local operator on a periodic qubit chain and constrains its normal-ordered pure-creation terms under the assumption that the W state is an eigenstate. The formal development separates the single-creation and higher-creation sectors, encodes finite-range cyclic geometry and witness constructions, and closes the higher-creation route using support-fiber aggregate coefficients rather than injective indexing of external terms. The resulting end-to-end theorem derives the vacuum-eigenstate conclusion for a mixed normal-ordered operator from explicit periodic-overlap, eigenstate, support, coverage, and representation hypotheses. The repository closes this proof architecture at Checkpoint 52 and records the source-to-formal boundary, theorem dependencies, reproducibility commands, and a workflow for using the formalization as a checked research reading point.

---

## 1. Introduction

A mathematical argument in a research paper can contain several layers at once: a physical setting, an operator representation, locality assumptions, algebraic relations, and a conclusion that depends on how those ingredients are assembled. Formalization makes that dependency route explicit.

The result studied here concerns the W state on a periodic qubit chain. In the source argument, an extensive-local operator is expressed in a normal-ordered hard-core-boson basis. If the W state is an eigenstate, the coefficients of nontrivial pure-creation terms are constrained. Once those terms are removed, the remaining nonidentity normal-ordered terms contain annihilation operators and annihilate the vacuum. The vacuum therefore inherits an eigenstate relation for the full operator, with the identity contribution supplying its eigenvalue.

The Lean development reconstructs this route as a sequence of explicit specifications. It distinguishes the source operator representation from the formal theorem that consumes that representation, separates the \(n=1\) and \(n\ge2\) pure-creation arguments, formalizes the finite-range witness geometry, and records the representation bridge needed to reach the mixed normal-ordered operator.

The final refinement concerns representation itself. Distinct external indices can specify the same duplicate-free creator support and therefore the same creation-string operator. The coefficient visible to that operator is consequently the sum over the corresponding support fiber. Checkpoints 47–52 replace an earlier support-injectivity route with support coverage and support-fiber aggregation. This produces an end-to-end Corollary-1 route without requiring injective indexing of higher-creation supports.

![Figure A. Diagram of the source-to-formal route for the W-state locality obstruction. An extensive-local finite-range operator and W-state eigenstate relation branch into the single-creation and higher-creation sectors. The single branch yields a zero single-creation coefficient. The higher branch uses cyclic locality and witness construction to obtain a zero support-fiber aggregate coefficient. Support coverage and coefficient matching join the branches in the representation bridge, yielding the mixed Row-One condition and the checked vacuum-eigenstate conclusion.](Figure_A.png)

**Figure A. Source locality to checked vacuum eigenstate.** The source reading point supplies an extensive-local operator with bounded interaction range and a W-state eigenstate relation, with a Hermiticity assumption excluded. The formal derivation separates the pure-creation sector into single-creation and higher-creation branches. Support coverage and coefficient matching reconnect those results to the mixed normal-ordered representation, yielding `MixedRowOneCondition` and the checked vacuum-eigenstate conclusion.

---

## 2. Source result and Corollary 1

The source uses a normal-ordered operator basis built from on-site hard-core-boson operators: identity, creation, annihilation, and number operators. Nontrivial strings can be written schematically as

\[
s^\dagger_{j_1}\cdots s^\dagger_{j_n}
s_{k_1}\cdots s_{k_m}.
\]

The pure-creation sector has \(m=0\). The relevant first row of the source classification states that the coefficient of a pure-creation string is zero for \(n\ge1\) under the W-state eigenstate condition and the locality hypotheses used in the argument.

The source then obtains Corollary 1: if the W state is an eigenstate of the extensive-local operator, the vacuum is also an eigenstate. After the pure-creation coefficients equal zero, every remaining nonidentity normal-ordered term contains an annihilation operator. Such terms annihilate the vacuum, leaving only the identity contribution.

The source argument does not require Hermiticity for this conclusion. The formal route therefore records:

> **Hermiticity assumption excluded.**

The detailed Appendix C argument supplies the separation geometry used for the pure-creation terms. Its stated sufficient chain-size condition is

\[
N>3R,
\]

where \(N\) is the periodic chain size and \(R\) is the finite interaction range. The final Lean route represents this as:

```lean
hNR : 3 * R < N
```

This \(3R\) condition belongs to the witness/separation argument. Other range statements used for representing cyclic strings have distinct roles and are kept separate in the source-to-formal map.

---

## 3. Source operator representation

The source supplies an operator-basis bridge from extensive-local operators to finite normal-ordered creation/annihilation strings. The Lean end-to-end theorem begins after this bridge has been represented as a finite mixed family:

```lean
mixedNormalOrderedOperator Ω mixedCoeff term
```

This gives a deliberate source-to-formal boundary:

```text
source extensive-local operator
        ↓
normal-ordered representation specification
        ↓
mixedNormalOrderedOperator
```

Lean checks consequences from the represented family and its explicit hypotheses. The source-to-Lean documentation separately records why this representation is supported by the source argument.

This distinction matters because a checked implication and the evidence supplying its hypotheses are different parts of the research record. The theorem signature specifies exactly what the formal proof consumes.

---

## 4. Formal specification

The formalization organizes the source argument around explicit objects and relations:

- a periodic chain of \(N\) sites;
- a W state `wState N`;
- linear operators and eigenstate relations;
- single-creation and higher-creation operator families;
- finite creator lists and their finite supports;
- cyclic blocks describing finite-range locality;
- witness data specifying separated configurations;
- support-fiber aggregate coefficients;
- a mixed normal-ordered representation;
- coverage and coefficient-matching relations connecting the pure-creation analysis to that mixed representation.

The final route also assumes \(3\le N\), duplicate-free higher-creation lists, finite-range support, and the relevant eigenstate hypotheses. These prerequisites are visible in the final theorem signature rather than hidden in prose.

The specification distinguishes supplied prerequisites from derived statements. In particular, locality and representation conditions are supplied to the theorem; coefficient equalities and the final vacuum-eigenstate relation are derived from them.

---

## 5. Finite-range cyclic geometry

The periodic geometry formalizes the finite-range separation used by the source proof. Each higher-creation support is contained in a range-\(R\) cyclic block. Under the global condition \(3R<N\), the development constructs witness data that separate the selected creator support from an additional excitation site.

For a higher-creation family, the central witness structure is:

```lean
HigherCreationWitnessData creators i
```

It records a witness site, a creator support containing at least two sites, duplicate-free creators, the witness outside the selected support, and a locality condition comparing that selected support with competing supports.

The single-creation argument uses its own geometry. A creator site \(j\), a separated excitation site \(\ell\), and a third site \(p\) provide the separation needed to isolate the relevant product-state component.

![Figure B. Periodic-chain diagrams for the single-creation and higher-creation witness constructions. A global chain-size condition N greater than 3R enables separated local regions. In the single-creation sector, a creator site, separated excitation site, and third site supply the Appendix C witness geometry and a zero single-creation coefficient. In the higher-creation sector, finite creator support lies in a range-R cyclic block and a witness site outside the support supplies HigherCreationWitnessData and a zero aggregate coefficient for the represented support.](Figure_B.png)

**Figure B. Finite-range witness geometry.** The condition \(N>3R\) supplies the separation used by the Appendix C witness constructions. The single-creation branch uses a third-site witness geometry. The higher-creation branch packages finite-support separation as `HigherCreationWitnessData`.

---

## 6. Pure-creation obstruction

### 6.1 Single creation

The \(n=1\) sector requires a separate argument. A second creation term can initially contribute to the same type of state, so the source introduces a third site separated from both relevant local regions. The resulting product-state component isolates the coefficient under consideration.

The formal branch derives:

\[
\text{singleCoeff}=0.
\]

This is an equality of the complete single-creation coefficient function, not merely a statement about one selected site.

### 6.2 Higher creation

For \(n\ge2\), finite creator support supplies a witness configuration outside that support. The W-state eigenstate relation constrains the coefficient visible to the resulting creation-string operator.

An earlier formal route associated this conclusion with each external family index and therefore required injectivity of the support map. That condition was stronger than the operator representation required. The final route instead asks which coefficient is visible to a common creation-string operator.

This leads to support-fiber aggregation.

---

## 7. Support-fiber aggregation

Let the external higher-creation family be indexed by \(i\), with coefficient `coeff i` and duplicate-free creator list `creators i`. Its operator-visible support is

\[
S_i=(\mathrm{creators}\ i).\mathrm{toFinset}.
\]

For a finite support \(S\), define the support fiber schematically by

\[
F_S=\{i\mid S_i=S\}.
\]

The corresponding aggregate coefficient is

\[
C(S)=\sum_{i\in F_S}\mathrm{coeff}(i).
\]

The key operator fact is that equal duplicate-free creator supports specify the same creation-string operator. In Lean, the relevant result is:

```lean
theorem creationString_eq_of_toFinset_eq
    {N : Nat}
    {xs ys : List (Fin N)}
    (hx : xs.Nodup)
    (hy : ys.Nodup)
    (hsupport : xs.toFinset = ys.toFinset) :
    creationString xs = creationString ys
```

Thus external index and operator identity are distinct. Multiple external indices can contribute to one common operator, and the coefficient carried by that operator is their support-fiber aggregate.

The final higher-creation theorem derives aggregate coefficient zero for the represented supports under the W-state eigenstate relation and the witness hypotheses:

\[
C(S)=0.
\]

![Figure C. Four-stage diagram showing support-fiber aggregation in the higher-creation sector. External indices map to duplicate-free creator supports. Equal supports specify the same creation-string operator. Indices with common support S form the support fiber F sub S, and their coefficients sum to the aggregate C of S. The W-state eigenstate relation and finite-range witness data specify C of S as zero for each represented support.](Figure_C.png)

**Figure C. Support-fiber aggregation.** Equal duplicate-free supports specify a common creation-string operator. The coefficient visible to that operator is the sum over its support fiber. The W-state eigenstate relation and finite-range witness data derive aggregate coefficient zero for each represented higher-creation support.

This is the central CP47–CP52 representation refinement. The end-to-end route uses support coverage plus support-fiber aggregate coefficients rather than injective indexing of higher-creation supports.

---

## 8. Representation bridge

The mixed normal-ordered representation and the separately analyzed pure-creation families must be connected explicitly.

For the higher-creation sector, the final route uses:

```lean
HigherCreationMixedSupportCovered term higherCreators
```

This states that every higher pure-creation support appearing in the mixed expansion is represented by the external higher-creation family. It requires coverage rather than a one-to-one indexing relation.

Coefficient correspondence is supplied by:

```lean
PureCreationAggregateRepresentationMatches
    mixedCoeff term
    singleCoeff higherCoeff higherCreators
```

Its single-creation component matches the mixed coefficient to the single-creation coefficient. Its higher-creation component matches the mixed coefficient to the support-fiber aggregate coefficient on the represented creator support.

The single-creation equality and the higher-creation aggregate equalities can therefore be transported into the mixed representation. Together they establish:

```lean
MixedRowOneCondition mixedCoeff term
```

The existing mixed-expansion theorem then gives:

```lean
vacuum_eigenstate_of_mixedRowOne
```

which states that the vacuum is an eigenstate of the mixed normal-ordered operator with eigenvalue supplied by its identity coefficient \(\Omega\).

---

## 9. End-to-end Corollary 1 theorem

The closed theorem at Checkpoint 52 is:

```lean
LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
```

in:

```text
LeanGioia/PeriodicOverlapAggregateClosed.lean
```

Its dependency route is:

```text
periodic-overlap geometry
        ↓
HigherCreationWitnessData
        ↓
support-fiber aggregation
        ↓
aggregate coefficient zero
        ↓
mixed-support coverage
        ↓
PureCreationAggregateRepresentationMatches
        ↓
MixedRowOneCondition
        ↓
vacuum_eigenstate_of_mixedRowOne
        ↓
Corollary 1
```

In substantive terms:

> The end-to-end formal route from the stated periodic-overlap, eigenstate, support, and representation hypotheses to the Corollary-1 vacuum eigenstate conclusion uses support coverage plus support-fiber aggregate coefficients rather than injective indexing of higher-creation supports.

The final theorem retains explicit hypotheses for chain size, periodic range, the single- and higher-creation eigenstate relations, higher-support containment, family support, duplicate-free creator lists, mixed-support coverage, representation matching, and the nonidentity normal-ordered family condition. These hypotheses specify the formal reading point.

---

## 10. Verification and reproducibility

From the repository root, the project can be built with:

```bash
lake update
lake build
```

The final module can be checked directly:

```bash
lake env lean LeanGioia/PeriodicOverlapAggregateClosed.lean
lake build LeanGioia.PeriodicOverlapAggregateClosed
```

The theorem and axiom audit is:

```bash
cat > /tmp/cp52_audit.lean <<'EOF'
import LeanGioia.PeriodicOverlapAggregateClosed

#print LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
#print axioms LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
EOF

lake env lean /tmp/cp52_audit.lean
```

At the CP52 reading point, the reported foundations are:

```text
propext
Classical.choice
Quot.sound
```

A placeholder audit is:

```bash
grep -R -n -E '\bsorry\b|\badmit\b' \
  LeanGioia --include='*.lean'
```

At the closed CP52 reading point, this returns an empty result.

The repository additionally records the proof-development map, theorem dependencies, reproducibility commands, scope, formal specification, and source-to-Lean correspondence.

---

## 11. Source-to-formal comparison

The formalization separates three kinds of statement.

**Source-supported prerequisites** include the normal-ordered representation, the finite-range setting, the W-state eigenstate relation, and the separation argument used to constrain pure-creation terms.

**Formal engineering specifications** include the precise Lean structures used to represent cyclic blocks, support coverage, witness data, support fibers, aggregate coefficients, and correspondence between separately analyzed pure-creation families and the mixed expansion.

**Checked consequences** include the single-creation coefficient equality, higher-creation support-fiber aggregate equalities, `MixedRowOneCondition`, and the final vacuum-eigenstate relation.

This separation prevents a formal theorem from being read as supplying its own physical premises. The theorem checks an implication from explicit hypotheses. Source evidence, representation choices, and physical interpretation remain visible parts of the complete evidence chain.

The theorem signatures provide the authoritative reading point for the formalized claims.

---

## 12. Discussion

The support-fiber refinement illustrates why formalization can expose a useful representation question even after the underlying source argument is understood. An externally indexed expansion can contain several terms that become the same operator once duplicate-free creator support is taken into account. Requiring those external indices to be injective over support would make the indexing convention part of the theorem. Aggregating coefficients over common supports instead places the theorem at the operator-visible level.

This refinement changes the formal dependency route without changing the source conclusion. The higher-creation obstruction constrains the coefficient of the common creation-string operator; support-fiber aggregation specifies that coefficient independently of how many external indices represent it.

The repository also provides a reusable workflow for another leading researcher. A reading point can be selected from a paper, seminar, measurement, or existing formal result. Leading specifications identify the objects, prerequisites, constraints, scope, and excluded assumptions. AI-assisted engineering can help translate those specifications into formal objects, theorem signatures, proof checkpoints, and source maps. Lean then checks the resulting formal implications. The checked result returns to the researcher as a new reading point from which the next specification can be selected.

![Figure D. Research workflow led by the researcher. A reading point leads to leading specifications, AI-assisted engineering, a formal check in Lean, and a checked reading point, with an iteration arrow returning checked results to new reading points. A lower Gioia example applies the same workflow from source reading point through the W-state locality formalization to the checked vacuum-eigenstate result.](Figure_D.png)

**Figure D. Research workflow from reading point to checked specification.** The leading researcher selects, specifies, compares, and interprets. AI assists the engineering of the formal route; Lean supplies the formal check; and the checked result returns to the researcher for source comparison, interpretation, and selection of what follows now.

> **Admissible generalizations follow leading specifications.**

---

## 13. Subsequent work

The CP52 proof architecture is closed. Subsequent work can proceed from the checked reading point rather than extending the checkpoint sequence by default.

Useful next targets include:

- comparison of the completed theorem against additional source formulations or special cases;
- reusable abstractions for support-fiber aggregation in other operator expansions;
- formalizations of further results whose source prerequisites can be stated at compatible reading points;
- publication of the report and its source-to-formal evidence map.

A new formal checkpoint is warranted where a new specification introduces a genuinely new theorem dependency, representation layer, or source result.

---

## 14. Conclusion

The `lean-gioia` development formalizes the W-state locality obstruction through an explicit route from finite-range cyclic geometry and W-state eigenstate hypotheses to the vacuum-eigenstate conclusion. The completed architecture separates the single-creation and higher-creation sectors, reconstructs the witness geometry, and closes the higher-creation representation through support-fiber aggregate coefficients.

The final CP52 theorem uses support coverage rather than support injectivity. Equal duplicate-free creator supports specify a common creation-string operator, and the coefficient visible to that operator is the aggregate over its support fiber. The W-state eigenstate relation and witness data derive that aggregate coefficient as zero on represented higher-creation supports. The representation bridge then establishes the mixed Row-One condition and the vacuum-eigenstate conclusion.

The result is both a checked formal implication and a documented research reading point: source evidence supplies the prerequisites, leading specifications constrain the formal route, AI can assist its engineering, Lean checks its consequences, and the researcher determines what follows now.

---

## Repository documentation

- [`README.md`](../README.md) — repository entry point
- [`README.md`](README.md) — illustrated report guide and figure captions
- [`../SPECIFICATION.md`](../SPECIFICATION.md) — closed CP52 specification
- [`../docs/SOURCE_TO_LEAN.md`](../docs/SOURCE_TO_LEAN.md) — source-to-formal correspondence
- [`../docs/THEOREM_MAP.md`](../docs/THEOREM_MAP.md) — principal theorem dependencies
- [`../docs/REPRODUCIBILITY.md`](../docs/REPRODUCIBILITY.md) — build and audit commands
- [`../docs/SCOPE.md`](../docs/SCOPE.md) — formal and interpretive scope
