# Checkpoint 2 — operators and eigenstates

This checkpoint adds only the operator/eigenstate infrastructure required
before locality is formalized.

## Added

- `LeanGioia/Operator.lean`
  - `Operator N := State N →ₗ[ℂ] State N`
  - `IsEigenstate A ψ λ := A ψ = λ • ψ`
  - identity and zero sanity checks
  - coefficientwise form of the eigenvalue equation
  - vacuum/W-state identity-operator checks

## Updated

- `LeanGioia.lean` imports `LeanGioia.Operator`.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- the finite-state representation from Checkpoint 1 remains unchanged;
- the eigenvalue equation can be stated and checked coefficientwise.

## Deliberately deferred

This checkpoint does **not** yet claim Corollary 1.

Checkpoint 3 should add only the operator-string/locality machinery needed
for the paper's argument:

1. creation/annihilation action on computational basis states;
2. normal-ordered operator strings;
3. a finite-support / bounded-range descriptor;
4. the lemma that any normal-ordered term containing an annihilation
   operator kills the vacuum;
5. only then, the W-eigenstate coefficient constraints used by Corollary 1.
