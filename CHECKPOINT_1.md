# Checkpoint 1

Replace/update:

- `LeanGioia/Basic.lean`
- `LeanGioia/WState.lean`
- `LeanGioia.lean`

Then run:

```text
lake build
```

This checkpoint intentionally stops before locality/operators.

Success criterion:
- the project builds with no `sorry`;
- vacuum and one-excitation basis states are defined;
- the W state is represented with coefficient `1 / sqrt(N)`;
- basic basis-state separation lemmas compile.

Next checkpoint:
- define the finite-range operator basis required by Corollary 1;
- state the eigenvector predicate in the chosen representation;
- prove the first locality lemma.
