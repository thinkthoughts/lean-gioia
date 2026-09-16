# Checkpoint 48 — Creation-String Support Invariance

## Status

**Target:** prove the representation-semantics fact deliberately left open by
CP47: under `List.Nodup`, equal finite creator support gives equal
`creationString` operators.

**Artifact:** `LeanGioia/CreationStringSupport.lean`

**Checkpoint type:** focused representation-semantics checkpoint.

CP48 is not a new end-to-end Corollary-1 theorem and does not yet remove the
existing higher-family injectivity hypothesis.

## Why CP48 follows CP47

CP47 introduced the support fiber

```lean
higherCreationSupportFiber creators S
```

and aggregate coefficient

```lean
higherCreationAggregateCoeff coeff creators S
```

for external higher-family indices sharing the same finite creator support.

That checkpoint intentionally stopped before treating

```lean
(creators i).toFinset = (creators j).toFinset
```

as sufficient to identify their operators.  The missing statement was:

```text
same finite creator support
        +
duplicate-free creator lists
        ↓
same creationString operator
```

CP48 isolates and proves that semantic bridge.

## Existing definition used

The repository defines creation strings recursively:

```lean
def creationString : List (Fin N) → Operator N
  | [] => identityOperator N
  | j :: js => composeOperator (createAt j) (creationString js)
```

Thus equal `toFinset` support is not definitionally equal to equal
`creationString`: list order remains visible in the syntax.  A commutation
argument is required.

## Proof ladder

CP48 uses the following route:

```text
distinct sites j ≠ k
        ↓
createAt j and createAt k commute
        ↓
adjacent distinct creators may be swapped
        ↓
Nodup + List.Perm
        ↓
creationString permutation invariance
        ↓
Nodup xs + Nodup ys + xs.toFinset = ys.toFinset
        ↓
creationString xs = creationString ys
```

The final theorem is intended to be:

```lean
theorem creationString_eq_of_toFinset_eq
    {xs ys : List (Fin N)}
    (hx : xs.Nodup)
    (hy : ys.Nodup)
    (hsupport : xs.toFinset = ys.toFinset) :
    creationString xs = creationString ys
```

## What CP48 closes

CP48 closes the representation warning recorded in CP47:

```text
equal List.toFinset support
```

may now be used to identify the corresponding `creationString` operators,
provided both creator lists satisfy `Nodup`.

This is exactly the semantic fact needed before a higher-creation family can
safely be regrouped by finite creator support.

## What CP48 deliberately leaves open

CP48 does **not** yet:

- rewrite `higherCreationFamilyOperator` as a sum over support fibers;
- prove that the support-fiber aggregate coefficient is the observable
  coefficient of the regrouped operator;
- remove `hinj` from the existing coefficient-isolation theorem;
- claim that individual duplicate external coefficients vanish;
- modify the CP44/CP45 end-to-end Corollary-1 theorem.

Those are later aggregation and theorem-replacement steps.

## Verification

First make sure the imported CP47 module has a Lake object:

```bash
lake build LeanGioia.HigherCreationSupportFiber
```

Then check CP48 directly:

```bash
lake env lean LeanGioia/CreationStringSupport.lean
```

A silent return to the shell prompt is the CP48 file-level PASS reading point.

If successful, build its object for the next checkpoint:

```bash
lake build LeanGioia.CreationStringSupport
```

## Failure discipline

The first theorem is intentionally the local `createAt` commutation result.
If the current `createAt` implementation exposes a mismatch in simplification
or operator-composition syntax, stop at that theorem and repair the local proof
rather than weakening or assuming the final support-invariance result.

Likewise, if the installed mathlib uses a different name for the standard
`Nodup` + equal-`toFinset` → `List.Perm` lemma, resolve that library interface
locally.  Do not replace the missing step with an axiom or assumption.

## Next reading point

After CP48 passes, CP49 can return to the CP47 support fibers and prove the
actual operator regrouping step:

```text
external higher-family sum
        ↓
partition by finite creator support
        ↓
aggregate coefficient on each support
        ↓
support-indexed higher-creation operator
```

Only after that regrouping theorem is kernel-checked should we attempt to
replace the existing `hinj` premise in the higher-creation coefficient route.
