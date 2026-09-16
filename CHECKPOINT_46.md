# Checkpoint 46 — Higher-Creation Index Uniqueness Boundary

## Status

**Target:** determine whether the higher-family injectivity hypothesis

```lean
Function.Injective
  (fun i => (creators i).toFinset)
```

is a removable representation artifact or a substantive premise of the current
coefficient-isolation proof.

**Checkpoint type:** audit / specification-boundary reading point.

CP46 intentionally introduces no new Lean theorem. It records the exact proof
role of `hinj` before any attempt to replace the higher-family indexing model.

## Context

Checkpoint 45 audited the remaining public hypotheses of

```lean
corollary_one_from_periodic_overlap_representation_closed
```

and selected higher-family creator-set injectivity as the next reduction
candidate.

The relevant dependency is localized to the higher-creation / Table-I-Row-1
branch:

```text
higherCreationFamilyOperator
        ↓
higher-creation coefficient isolation
        ↓
TableIRowOneConclusion
        ↓
CP42/43 reduced representation route
        ↓
Corollary 1
```

The periodic-overlap geometry itself does not use `hinj`.

## Audited hypothesis

The current higher family is externally indexed by a finite type `ι` (or `κ`
at later interfaces):

```lean
coeff    : ι → ℂ
creators : ι → List (Fin N)
```

The family operator is a sum over those external indices:

```lean
∑ i : ι, coeff i • creationString (creators i)
```

The relevant uniqueness hypothesis is:

```lean
hinj :
  Function.Injective
    (fun i : ι => (creators i).toFinset)
```

Thus two distinct family indices are prohibited from representing the same
finite creator support.

## Exact proof role of `hinj`

The key use occurs in the competing-term argument of
`HigherCreationComplete.lean`.

At a witness configuration selected for an index `i₀`, the locality argument
shows that any competing family member with nonzero amplitude must have the
same creator support as the selected term:

```text
nonzero competing amplitude
        ↓
locality / separated-competitor argument
        ↓
(creators i).toFinset = (creators i₀).toFinset
```

At that point, equality of supports alone does not imply equality of the
external indices.

`hinj` supplies precisely that conversion:

```text
(creators i).toFinset = (creators i₀).toFinset
        ↓  hinj
i = i₀
```

For a competitor carrying the assumption `i ≠ i₀`, this is a contradiction.
Therefore every differently indexed competing term has zero amplitude at the
selected witness.

That is the step that permits the finite family sum at the witness to isolate
the selected coefficient.

## Why CP46 does not remove `hinj`

The audit does **not** show that `hinj` is redundant.

Suppose instead that two distinct indices satisfy

```lean
i ≠ j
```

but

```lean
(creators i).toFinset = (creators j).toFinset.
```

The locality argument can identify the support, but it cannot distinguish the
two external labels merely from that support equality.

Consequently, the present proof cannot conclude that every differently
indexed term vanishes at the selected witness.

The current coefficient-isolation theorem therefore has a genuine dependence
on uniqueness of the external support labels.

## Coefficient-wise zero versus support-wise zero

This exposes an important specification distinction.

The current Table-I higher-sector conclusion is coefficient-wise:

```lean
higherCoeff = 0
```

or equivalently every externally indexed coefficient vanishes.

That statement is natural where creator support identifies a unique family
index.

Without injective support indexing, repeated representations of the same
support can contribute to the same operator component. The quantity naturally
visible to the operator may then be an aggregate over all indices representing
that support, schematically:

```text
aggregateCoeff(S)
  = Σ i with (creators i).toFinset = S, coeff i
```

The present CP16/CP17 proof is not formulated in terms of this aggregate.
Therefore removing `hinj` while retaining the same coefficient-wise theorem
would skip a required representation step.

CP46 makes no claim yet that the aggregate formulation is the final or
source-faithful formulation. It identifies it as the mathematically motivated
route to investigate.

## Classification of `hinj`

CP46 classifies

```lean
Function.Injective
  (fun i => (creators i).toFinset)
```

as a **representation/index-uniqueness premise of the current
coefficient-isolation theorem**.

It is:

- not part of the periodic geometry;
- not supplied by `3 * R < N`;
- not implied by creator-list `Nodup`;
- not implied by the CP38 single-versus-higher classification;
- not removed by `PureCreationRepresentationMatches`;
- used to pass from creator-support equality to external-index equality.

Therefore CP46 does not artificially weaken or rename the hypothesis.

## Why a renamed predicate is not introduced

A wrapper such as

```lean
def HigherCreationSupportInjective ... : Prop := ...
```

would currently only rename

```lean
Function.Injective
  (fun i => (creators i).toFinset)
```

without changing the mathematical interface.

CP46 therefore leaves the Lean API unchanged. A new abstraction should be
introduced only if a later support-indexed or aggregate-coefficient
formalization gives it additional mathematical content.

## Relationship to CP44 and CP45

The CP44 end-to-end theorem remains the current closed theorem:

```lean
corollary_one_from_periodic_overlap_representation_closed
```

CP45 established that its remaining assumptions are visible and that its axiom
dependencies are:

```text
[propext, Classical.choice, Quot.sound]
```

CP46 refines that audit by resolving one open classification question:

```text
Is hinj merely temporary?
        ↓
No, not for the current coefficient-wise proof.
```

This is a specification result about the existing formal route, not a claim
that injective external indexing is the only possible formulation.

## CP46 reading point

The higher-creation proof currently has the logical form

```text
selected index i₀
        ↓
selected creator support S₀
        ↓
witness configuration
        ↓
nonzero competitor i
        ↓
creator support of i = S₀
        ↓  support injectivity
i = i₀
        ↓
all differently indexed competitors vanish
        ↓
selected family coefficient is isolated
        ↓
higherCoeff i₀ = 0
```

The bold boundary for subsequent work is therefore:

```text
same creator support ≠ same external index
```

unless support-index uniqueness is specified.

## CP47 target — Canonical Support / Aggregate Coefficients

CP47 should investigate an alternative higher-family representation where
duplicate external indices are handled structurally rather than forbidden.

The first target is to determine whether the higher-creation operator can be
factored through finite creator support.

Candidate conceptual route:

```text
external family indices
        ↓
creator-support map
        ↓
fibers of equal support
        ↓
aggregate coefficients on support
        ↓
support-indexed higher-creation operator
```

A candidate aggregate has the schematic form

```text
S ↦ Σ i in fiber(S), coeff i
```

where the fiber contains the external indices whose creator lists determine
support `S`.

The intended question for CP47 is:

> Can the higher-creation coefficient-isolation theorem be stated for
> canonical creator supports or aggregate support coefficients, so that
> duplicate external labels no longer require global `Function.Injective`?

CP47 should first formalize only the smallest algebraic/representation lemma
needed to answer that question. It should not immediately rewrite the entire
Corollary-1 chain.

## CP47 constraints

The next checkpoint should preserve the evidence discipline established here:

1. Do not delete `hinj` from the existing theorem before a replacement theorem
   proves the required statement.
2. Do not claim individual duplicate coefficients vanish if the operator only
   determines their aggregate.
3. Keep list representation and finite creator support distinct.
4. Preserve `Nodup` where list-level creation-string semantics require it.
5. Compare any new support-indexed theorem explicitly with the current
   coefficient-wise Table-I conclusion.
6. Leave the CP44 theorem intact as a verified baseline while the alternative
   representation is developed.

## Reproduction / audit commands

The CP46 source boundary can be inspected with:

```bash
sed -n '1,260p' LeanGioia/HigherCreationComplete.lean
sed -n '1,190p' LeanGioia/TableIRowOne.lean

grep -R -n -B20 -A70 \
  "Function.Injective" \
  LeanGioia/HigherCreationComplete.lean \
  LeanGioia/TableIRowOne.lean

grep -R -n -B20 -A70 \
  "higher_creation.*zero\|higherCreation.*zero\|higherCoeff.*0" \
  LeanGioia/HigherCreationComplete.lean \
  LeanGioia/TableIRowOne.lean
```

No Lake build is required solely for this documentation checkpoint because
CP46 changes no Lean source. The verified CP44/CP45 state remains the baseline.

## Checkpoint result

**CP46 PASS — higher-creation index uniqueness boundary identified.**

`hinj` is retained in the existing coefficient-wise theorem because it
performs a specific proof step: equality of creator supports is lifted to
equality of external family indices.

The next admissible reduction is not to erase that premise. It is to
investigate a support-indexed or aggregate-coefficient formulation where
duplicate external labels are represented explicitly.

**Next: CP47 — Canonical Support / Aggregate Coefficients.**
