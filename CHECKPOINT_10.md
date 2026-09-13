# Checkpoint 10 — assemble the single-creation obstruction

The first row of Table I in the source paper states that pure-creation
coefficients vanish. Appendix C.1.a treats the `n = 1, m = 0` case with a
three-site argument.

Checkpoints 8 and 9 established:

1. the two-particle witness amplitude structure;
2. the three-site coefficient consistency obstruction.

Checkpoint 10 assembles those into the paper-facing coefficient statement
for the single-creation sector.

## Added

`LeanGioia/SingleCreation.lean`

with:

- `ThreeSiteWitnessEquations`
- `single_creation_coefficient_zero`
- `all_single_creation_coefficients_zero`
- `single_creation_coefficients_eq_zero`
- `SingleCreationForbidden`
- `single_creation_forbidden_of_three_site_witnesses`

## Formal boundary

This checkpoint intentionally keeps one remaining bridge explicit:

```text
finite-range locality + W eigenstate
              ↓
three witness-amplitude equations for each j
```

The coefficient conclusion below that bridge is now fully formalized:

```text
three witness-amplitude equations
              ↓
             c_j = 0
```

for every selected site `j`.

This avoids claiming that the repository has already formalized the complete
extensive-local operator expansion of Eq. (17).

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- given the paper's three witness-amplitude equations, Lean proves that all
  `n = 1, m = 0` coefficients vanish.

## Next checkpoint

Checkpoint 11 should formalize the remaining bridge from a concrete
finite-range single-creation expansion and the W-eigenstate equation to
`ThreeSiteWitnessEquations`.

After that, the `n = 1, m = 0` row is closed end-to-end. The `n ≥ 2, m = 0`
case can then be packaged using the unique higher-particle witness machinery
from Checkpoints 5–7.
