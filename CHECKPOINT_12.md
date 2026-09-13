# Checkpoint 12 — complete the `n = 1, m = 0` case

Checkpoint 11 reduced the remaining gap to site existence:

for a selected site `j`, choose two further pairwise-distinct sites `l,p`.

Checkpoint 12 proves that this is always possible when `N ≥ 3`, then feeds
those sites into the end-to-end result from Checkpoint 11.

## Added

`LeanGioia/SingleCreationComplete.lean`

with:

- `exists_two_other_sites`
- `all_single_creation_coefficients_zero_of_eigenstate`
- `single_creation_coefficients_zero_of_eigenstate`
- `single_creation_forbidden_of_eigenstate`

## End-to-end result

For the explicit single-creation operator

```text
G_c = ∑_j c_j s†_j
```

Lean now proves:

```text
3 ≤ N
G_c |W⟩ = eig |W⟩
------------------
c = 0
```

with no witness hypotheses remaining.

## Scope

This closes the paper's special `n = 1, m = 0` pure-creation case for the
explicit single-creation sector.

The first row of Table I also contains the `n ≥ 2, m = 0` case.  That case
uses the unique higher-particle witness/locality argument developed in
Checkpoints 5–7 and should be packaged next.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- every single-creation coefficient is proved zero from the W-eigenstate
  condition and `N ≥ 3`, with no remaining witness assumptions.
