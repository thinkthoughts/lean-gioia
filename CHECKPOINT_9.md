# Checkpoint 9 — three-site consistency obstruction

Appendix C.1.a treats the `n = 1, m = 0` pure-creation case by choosing
three sufficiently separated sites `j`, `l`, and `p`.

Checkpoint 8 established the pair-amplitude structure: at the two-particle
basis state `{a,b}`, only the creation terms at `a` and `b` can contribute.

Therefore cancellation at the three witnesses gives

```text
c_j + c_l = 0
c_j + c_p = 0
c_l + c_p = 0
```

and these three equations force `c_j = 0` (indeed all three coefficients
vanish).

## Added

`LeanGioia/ThreeSite.lean`

with:

- `PairCancellation`
- `three_site_consistency_forces_zero`
- `three_site_consistency_forces_all_zero`
- `pairCancellation_of_scaled_amplitude_zero`
- `three_site_scaled_amplitudes_force_zero`

## Formal boundary

This checkpoint formalizes the coefficient algebra of the paper's
three-site argument.  It does not yet derive all three pair-amplitude
equations from a single finite-range extensive-local operator expansion.

That remaining assembly step is what connects the local geometry and
amplitude lemmas to the paper-level statement that every `n = 1, m = 0`
coefficient vanishes.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- Lean verifies the three-site coefficient obstruction;
- the result is also available directly in the scaled W-amplitude form.

## Next checkpoint

Checkpoint 10 should assemble the locality, pair-amplitude, and three-site
lemmas into the paper-level single-creation coefficient theorem.  In
parallel, the simpler `n ≥ 2, m = 0` case can be packaged from the unique
higher-particle witness argument.  Together these give the first row of
Table I: all pure-creation coefficients vanish.
