# Checkpoint 17 — package Table I Row 1

The source paper's first row of Table I gives the pure-creation condition

```text
n ≥ 1, m = 0  →  c_{j1...jn} = 0.
```

The formalization now has both branches:

```text
n = 1
```

closed end-to-end in Checkpoint 12, and

```text
n ≥ 2
```

closed at coefficient level in Checkpoint 16 under explicit
separated-witness/locality hypotheses.

Checkpoint 17 packages those two branches into one paper-facing result.

## Added

`LeanGioia/TableIRowOne.lean`

with:

- `HigherCreationWitnessData`
- `all_higher_creation_coefficients_zero_of_eigenstate`
- `higher_creation_coefficients_eq_zero_of_eigenstate`
- `TableIRowOneConclusion`
- `tableI_row_one_pure_creation_coefficients_zero`

## Verified package

Lean now packages:

```text
single-creation sector:
    G₁ |W⟩ = λ₁ |W⟩
    3 ≤ N
    ----------------
    all c_j = 0

higher-creation sector:
    G≥2 |W⟩ = λ≥2 |W⟩
    per-term separated-witness locality data
    unique creator-set labels
    ----------------------------------------
    all c_{j1...jn} = 0
```

## Important formal boundary

This is a **sector-level packaging** of the first Table I row.

It does not yet formalize one complete mixed extensive-local operator
containing all `n,m` sectors simultaneously, nor derive every
`HigherCreationWitnessData` instance from a concrete periodic range-`R`
operator-expansion type.

That distinction matters: the paper's Table I statement is about one
general extensive-local operator expansion, while the current Lean result
packages the two pure-creation sectors that have been verified separately.

## Why this checkpoint matters for Corollary 1

Once pure-creation terms are excluded, every remaining nonidentity
normal-ordered basis term contains at least one annihilation operator.

Checkpoint 3 already proves:

```text
normal-ordered string with an annihilator
→ annihilates the vacuum.
```

Therefore the next checkpoint can package the formal route toward
Corollary 1 at the same explicit boundary.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- both pure-creation branches are packaged as zero coefficient functions;
- the higher-creation locality boundary remains explicit rather than being
  silently hidden.
