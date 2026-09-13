# Checkpoint 7 — concrete support witness

Checkpoint 7 connects the abstract geometry of Checkpoint 6 to the actual
kind of higher-particle basis configuration used in Appendix C.1.a.

The source proof takes a selected pure-creation support `A`, chooses a site
`l` sufficiently far from `A`, and considers the product state with the
support sites and `l` occupied.  That configuration lies outside the
one-particle W sector.

## Added

`LeanGioia/SupportWitness.lean`

with:

- `BufferedSupport`
- `BufferedSupport.excluded`
- `BufferedSupport.toExclusionRegion`
- `BufferedSupport.chooseSeparated`
- `occupiedBits`
- `BufferedSupport.witnessBits`
- occupancy lemmas for the core and separated site
- `BufferedSupport.witness_ne_singleExcitation`
- `BufferedSupport.wState_witness_zero`

## Formal boundary

This checkpoint proves:

```text
nonempty local support
+ separated site
----------------------
witness has at least two distinct occupied sites
----------------------
W amplitude at witness = 0
```

It does not yet prove the two operator-amplitude facts needed for the full
Appendix C cancellation result:

1. the selected pure-creation term contributes nonzero amplitude at the
   witness;
2. every competing range-R local term contributes zero amplitude there.

Those are the target for Checkpoint 8.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- the concrete separated witness is proved to lie outside the W sector.
