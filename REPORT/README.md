# A Formalization of the W-State Locality Obstruction

**Report page:** `labreports.app/gioia`

This page collects the report figures for Formalization Specification 001. The figures move from the complete source-to-formal route, to the finite-range witness geometry, to the support-fiber representation refinement.

---

## Figure A — Source locality to checked vacuum eigenstate

![Figure A. Diagram of the source-to-formal route for the W-state locality obstruction. An extensive-local finite-range operator and W-state eigenstate relation branch into the single-creation and higher-creation sectors. The single branch yields a zero single-creation coefficient. The higher branch uses cyclic locality and witness construction to obtain a zero support-fiber aggregate coefficient. Support coverage and coefficient matching join the branches in the representation bridge, yielding the mixed Row-One condition and the checked vacuum-eigenstate conclusion.](Figure_A.png)

**Caption.** **Figure A. Source locality to checked vacuum eigenstate.** The source reading point supplies an extensive-local operator with bounded interaction range and a W-state eigenstate relation, with a Hermiticity assumption excluded. The formal derivation separates the pure-creation sector into the single-creation branch and the higher-creation branch. The single branch specifies the single-creation coefficient as zero. In the higher branch, cyclic locality supplies witness data, and the W-state eigenstate relation together with those witnesses specifies the support-fiber aggregate coefficient as zero. Support coverage and coefficient matching connect these results to the mixed normal-ordered representation, yielding `MixedRowOneCondition` and the checked vacuum-eigenstate conclusion.

**Alt text.** Three-band flow diagram labeled Source Reading Point, Formal Derivation, and Checked Conclusion. An extensive-local finite-range operator and W-state eigenstate relation feed two branches. The single-creation branch ends at single-creation coefficient equals zero. The higher-creation branch passes through cyclic locality, witness construction, common creator support, and support-fiber aggregate coefficient equals zero. The branches rejoin through a representation bridge using support coverage and coefficient matching, then pass through `MixedRowOneCondition` to the conclusion that the vacuum is an eigenstate.

---

## Figure B — Finite-range witness geometry

![Figure B. Periodic-chain diagrams for the single-creation and higher-creation witness constructions. A global chain-size condition N greater than 3R enables separated local regions. In the single-creation sector, a creator site, separated excitation site, and third site supply the Appendix C witness geometry and a zero single-creation coefficient. In the higher-creation sector, finite creator support lies in a range-R cyclic block and a witness site outside the support supplies HigherCreationWitnessData and a zero aggregate coefficient for the represented support.](Figure_B.png)

**Caption.** **Figure B. Finite-range witness geometry.** A periodic chain with finite interaction range \(R\) supplies the locality setting, while the Appendix C condition \(N>3R\) supplies the separation used by the witness constructions. In the single-creation sector \((n=1)\), a creator site \(j\), a separated excitation site \(\ell\), and a third site \(p\) produce an isolated product-state component and specify the single-creation coefficient as zero. In the higher-creation sector \((n\ge2)\), finite creator support \(S\) is supported by a range-\(R\) cyclic block; a witness site \(\ell\) outside \(S\), together with the locality condition, supplies `HigherCreationWitnessData`. The W-state eigenstate relation and witness data then specify the aggregate coefficient for the represented support \(S\) as zero.

**Alt text.** Two periodic-chain diagrams beneath a geometric setup. The setup states that the chain has \(N\) cyclic sites, finite interaction range \(R\), and the global separation condition \(N>3R\). The left panel shows the single-creation sector: creator site \(j\) lies in a local range-\(R\) region, excitation site \(\ell\) lies in a separated region, and third site \(p\) is separated from both local regions; the result is single-creation coefficient equals zero. The right panel shows the higher-creation sector: finite creator support \(S\) lies in a range-\(R\) cyclic block and witness site \(\ell\) lies outside \(S\); this supplies `HigherCreationWitnessData` and aggregate coefficient for support \(S\) equals zero.

---

## Figure C — Support-fiber aggregation

![Figure C. Four-stage diagram showing support-fiber aggregation in the higher-creation sector. External indices map to duplicate-free creator supports. Equal supports specify the same creation-string operator. Indices with common support S form the support fiber F sub S, and their coefficients sum to the aggregate C of S. The W-state eigenstate relation and finite-range witness data specify C of S as zero for each represented support.](Figure_C.png)

**Caption.** **Figure C. Support-fiber aggregation.** In the externally indexed higher-creation family, each index \(j\) carries a finite duplicate-free creator support \(S_j\). Equal duplicate-free supports specify the same creation-string operator, shared across those external indices. For a represented support \(S\), the support fiber \(F_S=\{j\mid S_j=S\}\) collects all corresponding external indices, and the operator-visible coefficient is the aggregate \(C(S)=\sum_{j\in F_S}\mathrm{coeff}(j)\). The W-state eigenstate relation and finite-range witness data specify \(C(S)=0\) for each represented support in the higher-creation sector. Thus operator identity follows creator support, while the coefficient carried by that common operator is the support-fiber aggregate.

**Alt text.** Four-stage flow diagram for the higher-creation sector. Stage one shows external family indices \(j_1,j_2,j_3,\ldots\), each mapped to a finite creator support. Stage two shows several equal duplicate-free supports \(S_{j_1}=S_{j_2}=\cdots=S\), which specify a common creation-string operator shared across those indices. Stage three groups the indices into the support fiber \(F_S=\{j\mid S_j=S\}\) and defines the aggregate coefficient \(C(S)\) as the sum of their coefficients. Stage four combines the W-state eigenstate relation with finite-range witness geometry and concludes \(C(S)=0\) for each represented support \(S\) with \(n\ge2\).

---

## Figure sequence

Figure A gives the complete source-to-formal architecture. Figure B isolates the finite-range geometry that supplies the witness data. Figure C isolates the representation refinement that maps multiple external indices with a common creator support to one operator-visible support-fiber aggregate coefficient.
