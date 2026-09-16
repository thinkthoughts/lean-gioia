# Checkpoint 47 — Higher-Creation Support Fibers

## Status

**Target:** formalize the representation object identified by CP46: the fiber
of external higher-creation indices sharing one finite creator support, and the
coefficient aggregated over that fiber.

**Artifact:** `LeanGioia/HigherCreationSupportFiber.lean`

**Checkpoint type:** focused representation checkpoint.

CP47 does **not** remove `hinj` from the existing coefficient-isolation theorem.
It establishes the algebraic representation needed to investigate such a
reformulation safely.

## Source boundary from CP46

`higherCreationFamilyOperator` is currently defined by an external finite
index family:

```lean
∑ i : ι, coeff i • creationString (creators i)
```

The existing proof uses

```lean
hinj :
  Function.Injective
    (fun i => (creators i).toFinset)
```

after locality has shown that a nonzero competitor has the same creator
support as the selected term.

CP46 therefore identified:

```text
same creator support ≠ same external index
```

as the next representation boundary.

## New object: support fiber

CP47 defines

```lean
higherCreationSupportFiber creators S
```

as

```lean
Finset.univ.filter fun i =>
  (creators i).toFinset = S
```

This makes duplicate external labels explicit rather than prohibiting them.

For a support `S`, the fiber contains exactly those external family indices
whose creator lists determine `S`.

## New object: aggregate coefficient

CP47 defines

```lean
higherCreationAggregateCoeff coeff creators S
```

as the finite sum of coefficients over the support fiber:

```lean
∑ i ∈ higherCreationSupportFiber creators S, coeff i
```

This is the quantity suggested by the CP46 audit for a future formulation in
which multiple external indices may represent the same creator support.

CP47 does not yet claim that this aggregate is sufficient to replace the
existing higher-family operator in full generality. In particular, equality of
`List.toFinset` alone must not silently be treated as equality of
`creationString` without the required list/order semantics being proved.

## New lemmas

### Self-membership

```lean
mem_higherCreationSupportFiber_self
```

Every family index belongs to the fiber over its own creator support.

### Singleton fiber under the existing injectivity premise

```lean
higherCreationSupportFiber_eq_singleton_of_injective
```

proves:

```lean
Function.Injective
  (fun i => (creators i).toFinset)
→
higherCreationSupportFiber creators (creators i).toFinset = {i}
```

This makes the current representation assumption concrete: injective support
indexing means every realized support fiber is a singleton.

### Aggregate reduces to the individual coefficient

```lean
higherCreationAggregateCoeff_eq_of_injective
```

then proves:

```lean
higherCreationAggregateCoeff
  coeff creators (creators i).toFinset
=
coeff i
```

under the same support-injectivity premise.

## CP47 result

The current coefficient-wise higher-creation formulation is now related
formally to a support-aggregated formulation:

```text
external indices
        ↓
creator-support fiber
        ↓
aggregate coefficient
        ↓
support injectivity
        ↓
fiber = singleton
        ↓
aggregate coefficient = individual coefficient
```

This is a representation theorem, not yet a replacement for the CP16
coefficient-isolation theorem.

## Why CP47 stops here

The source definition is:

```lean
higherCreationFamilyOperator coeff creators
  = ∑ i, coeff i • creationString (creators i)
```

The CP46 audit showed that the witness/locality proof identifies
`(creators i).toFinset`, while the operator itself acts through the full
`List (Fin N)` passed to `creationString`.

Therefore the next step must establish what equivalence of creator lists is
actually sufficient to regroup operator terms.

CP47 deliberately does **not** assume:

```text
same toFinset → same creationString
```

because that requires proof and may depend on creator ordering, duplication,
or commutation properties.

## Verification

If the imported object is not currently built:

```bash
lake build LeanGioia.HigherCreationComplete
```

Then:

```bash
lake env lean LeanGioia/HigherCreationSupportFiber.lean
```

A silent return to the shell prompt is the CP47 file-level PASS reading point.

For a Lake-built object:

```bash
lake build LeanGioia.HigherCreationSupportFiber
```

## CP48 target

**Determine the operator semantics of equal creator supports.**

The next audit/proof should inspect `creationString`, `createAt`, and the
available commutation lemmas and answer:

> Under the higher-sector `Nodup` conditions, when two creator lists have equal
> `toFinset`, do their `creationString` operators agree?

Possible outcomes:

```text
A. equality follows from support equality + Nodup
   → prove a permutation/support invariance theorem
   → regroup the family operator by support fibers

B. list order remains semantically relevant
   → aggregate by a finer canonical key than Finset support

C. equality requires an additional commuting-creation theorem
   → formalize that theorem before regrouping
```

The existing injective CP44 theorem remains unchanged as the verified
baseline.

## Checkpoint result

**CP47 target:** support fibers and aggregate coefficients, with the existing
injective formulation proved to be the singleton-fiber specialization.

No claim is made yet that `hinj` can be removed from Table-I Row 1.
