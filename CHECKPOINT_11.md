# Checkpoint 11 — derive witness equations from the explicit operator

Checkpoint 10 proved the coefficient obstruction assuming the three
two-particle witness equations.  Checkpoint 11 derives those equations from
an explicit single-creation operator

```text
G_c = ∑_j c_j s†_j
```

and the W-eigenstate equation.

## Added

`LeanGioia/SingleCreationOperator.lean`

with:

- `singleCreationOperator`
- `wState_twoExcitation_zero`
- `singleCreationOperator_twoExcitation`
- `pair_witness_equation_of_eigenstate`
- `threeSiteWitnessEquations_of_eigenstate`
- `single_creation_coefficient_zero_of_eigenstate`

## Verified chain

For distinct `j,l`:

```text
G_c |W⟩ = eig |W⟩
          ↓
W({j,l}) = 0
          ↓
G_c|W⟩({j,l}) = 0
          ↓
(c_j + c_l) * wCoefficient N = 0
```

For three pairwise distinct sites `j,l,p`, the three pair equations feed
directly into Checkpoint 10 and force `c_j = 0`.

## Formal boundary

This closes the algebraic `n = 1, m = 0` argument for an explicit
single-creation operator once three pairwise distinct sites are supplied.

The remaining geometric wrapper is now small: derive suitable `l,p` for
each selected `j` from the chain-size/locality assumptions.  For the
single-site creation sector this is a finite-site existence statement.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- the three witness equations are derived from `IsEigenstate`;
- a selected coefficient is forced to zero end-to-end.

## Next checkpoint

Checkpoint 12 should discharge the remaining site-existence assumption and
prove that every coefficient of `singleCreationOperator c` is zero under
the appropriate system-size hypothesis.  That will close the
`n = 1, m = 0` case end-to-end with no witness hypotheses remaining.
