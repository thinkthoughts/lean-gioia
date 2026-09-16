# Checkpoint 48 — Creation-String Support Invariance

## Status

**Target:** close the representation-semantics boundary left open by CP47.

**Artifact:** `LeanGioia/CreationStringSupport.lean`

**Checkpoint type:** focused representation-invariance checkpoint.

CP48 proves that, for duplicate-free creator lists, finite creator support
specifies the corresponding `creationString` operator.

It does **not** yet regroup the higher-creation family operator or remove the
existing creator-support injectivity hypothesis.

## Reading point from CP47

CP47 introduced

```lean
higherCreationSupportFiber creators S
```

and

```lean
higherCreationAggregateCoeff coeff creators S
```

for external higher-family indices sharing one finite creator support.

That construction was intentionally only bookkeeping until the following
semantic implication was proved:

```text
xs.Nodup
ys.Nodup
xs.toFinset = ys.toFinset
        ↓
creationString xs = creationString ys
```

CP48 proves exactly this implication.

## Concrete source semantics

The repository defines

```lean
def setBit (b : Bitstring N) (j : Fin N) (v : Bool) : Bitstring N :=
  Function.update b j v
```

and the hard-core creation operator reads the target bit and, where occupied,
evaluates the state after setting that bit to `false`.

Creation strings are recursively composed:

```lean
def creationString : List (Fin N) → Operator N
  | [] => identityOperator N
  | j :: js => composeOperator (createAt j) (creationString js)
```

Thus support invariance is not definitional.  It requires a proof that
distinct-site creation operations commute.

## CP48 proof ladder

```text
Function.update_comm
        ↓
setBit_comm
        ↓
distinct-site createAt commutation
        ↓
adjacent creationString swap
        ↓
List.Perm invariance under Nodup
        ↓
Nodup + equal toFinset
        ↓
creationString equality
```

## New lemmas

### `setBit_comm`

For `j ≠ k`:

```lean
setBit (setBit b j v) k w =
  setBit (setBit b k w) j v
```

This is the repository-level wrapper around `Function.update_comm`.

### `setBit_apply_of_ne`

For `j ≠ k`:

```lean
setBit b j v k = b k
```

This makes the distinct-coordinate reading fact explicit for the
`createAt` proof.

### `createAt_comp_comm_of_ne`

For distinct sites:

```lean
composeOperator (createAt j) (createAt k) =
  composeOperator (createAt k) (createAt j)
```

This is the local hard-core creation semantic fact needed by the remainder of
the checkpoint.

### `composeOperator_assoc`

The repository's `composeOperator` is associative.

This is packaged locally so the adjacent-swap proof does not depend on an
unrelated composition rewrite API.

### `creationString_swap_adjacent`

Distinct adjacent creator sites may be exchanged without changing the
creation-string operator.

### `creationString_eq_of_perm_of_nodup`

A permutation of a duplicate-free creator list determines the same
creation-string operator.

### `creationString_eq_of_toFinset_eq`

The checkpoint endpoint:

```lean
theorem creationString_eq_of_toFinset_eq
    (hx : xs.Nodup)
    (hy : ys.Nodup)
    (hsupport : xs.toFinset = ys.toFinset) :
    creationString xs = creationString ys
```

The final list-theoretic bridge uses the available mathlib theorem

```lean
List.perm_of_nodup_nodup_toFinset_eq
```

rather than introducing a new representation assumption.

## What CP48 closes

Before CP48:

```text
equal support
    ↓
same external support class
```

was established by CP47, but identifying the corresponding operators remained
open.

After CP48:

```text
equal support + Nodup
        ↓
same creationString operator
```

is kernel-visible once this checkpoint passes.

This makes `Finset (Fin N)` support an admissible canonical key for
duplicate-free creation strings.

## What CP48 deliberately leaves open

CP48 does **not** yet:

- regroup `higherCreationFamilyOperator` by support fibers;
- prove an operator identity involving `higherCreationAggregateCoeff`;
- replace individual higher-family coefficients by aggregate coefficients in
  Table-I Row 1;
- remove `hinj` from the existing coefficient-isolation theorem;
- modify the CP44/CP45 end-to-end theorem.

Those are aggregation and theorem-reduction steps that now have a justified
representation invariant to build on.

## Verification

Make sure CP47 has a Lake-built object:

```bash
lake build LeanGioia.HigherCreationSupportFiber
```

Then:

```bash
lake env lean LeanGioia/CreationStringSupport.lean
```

A silent return to the shell prompt is the CP48 file-level PASS reading point.

After a file-level pass:

```bash
lake build LeanGioia.CreationStringSupport
```

## Failure discipline

If CP48 fails, repair the smallest failing lemma rather than weakening the
checkpoint endpoint.

In particular:

- failures in `createAt_comp_comm_of_ne` are local bit-update proof issues;
- failures in `creationString_swap_adjacent` are composition-rewrite issues;
- failures in `creationString_eq_of_perm_of_nodup` are `List.Perm` induction
  interface issues;
- the final support theorem should remain unchanged unless the preceding
  semantic lemmas reveal a genuine counterexample.

No axiom or additional representation hypothesis should be introduced to make
the endpoint pass.

## CP49 target

Once CP48 passes, CP49 can use CP47 + CP48 together to prove the first actual
support-regrouping result:

```text
external higher-family sum
        ↓
group indices by creator support
        ↓
equal-support creationString terms identified by CP48
        ↓
sum coefficients within each support fiber
        ↓
support-aggregated operator representation
```

Only after that operator identity is kernel-checked should the repo attempt to
replace the existing `hinj` premise in the higher-creation coefficient route.

## Checkpoint result

**CP48 target:** duplicate-free `creationString` operators are determined by
finite creator support.

The CP44/CP45 injective route remains the verified end-to-end baseline while
this representation reduction proceeds.
