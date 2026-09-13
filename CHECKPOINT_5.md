# Checkpoint 5 — uncancellable-witness lemma

A closer reading of Appendix C.1.a shows that the source proof contains two
separable formal tasks:

1. **Cancellation logic:** if a higher-particle basis configuration receives
   nonzero amplitude from one selected pure-creation contribution and zero
   amplitude from every other contribution, the W-eigenstate equation forces
   that selected coefficient to vanish.
2. **Periodic locality geometry:** for a range-`R` pure-creation term on a
   sufficiently large periodic chain, construct such a basis configuration by
   choosing an extra occupied site sufficiently far from the local support.

Checkpoint 5 formalizes task 1 exactly.

The paper supplies task 2 informally in Appendix C.1.a. It considers a site
outside the range-`R` region and states that `N > 3R` is sufficient for the
presented separation arguments.

## Added

`LeanGioia/Cancellation.lean`

with:

- `IsOutsideWSector`
- `UncancellableWitness`
- `coefficient_zero_of_uncancellable_witness`
- `coefficient_zero_of_unique_amplitude`

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- Lean verifies the coefficient-cancellation step used in Appendix C.1.a.

## Next checkpoint

Checkpoint 6 should encode the periodic-chain range geometry and derive an
`UncancellableWitness` from the paper's locality assumptions.  Once that is
kernel-checked, the pure-creation coefficient theorem can be stated at the
paper level and combined with Checkpoint 3 to assemble Corollary 1.
