# Checkpoint 20 — finite mixed expansion: Table I Row 1 → Corollary 1

Checkpoint 19 proved directly from normal-ordered syntax:

```text
annihilators ≠ []
→ term |0̄⟩ = 0.
```

Checkpoint 20 now introduces one finite mixed expansion

```text
G = Ω 1 + Σᵢ cᵢ Tᵢ
```

where each `Tᵢ` is a `NormalOrderedTerm`.

## Added

`LeanGioia/MixedExpansion.lean`

with:

- `MixedRowOneCondition`
- `NonidentityNormalOrderedFamily`
- `mixedNormalOrderedRemainder`
- `mixedNormalOrderedOperator`
- `mixedNormalOrdered_summand_vacuum_zero`
- `mixedNormalOrderedRemainder_vacuum_zero`
- `vacuum_eigenstate_of_mixedRowOne`
- `MixedCorollaryOneData`
- `corollary_one_for_finite_mixed_expansion`

## Mixed form of Table I Row 1

The coefficient condition is stated directly as

```text
annihilators = []
creators ≠ []
----------------
coefficient = 0
```

for every term in the mixed expansion.

Because the identity term is represented separately by `Ω`, every indexed
term is required to be nonidentity:

```text
creators ≠ [] ∨ annihilators ≠ [].
```

## Verified chain

For each nonidentity mixed term:

```text
annihilators = []
    ↓
creators ≠ []
    ↓
Table I Row 1: coefficient = 0
```

or

```text
annihilators ≠ []
    ↓
Checkpoint 19: term |0̄⟩ = 0.
```

Therefore every summand of the nonidentity remainder vanishes on the
vacuum, and Lean proves

```text
G |0̄⟩ = Ω |0̄⟩.
```

## Source alignment

This is the structural argument stated for Corollary 1 in the paper:
pure-creation terms cannot contribute, so every remaining nonidentity
normal-ordered term contains at least one annihilation operator and
annihilates the vacuum.  The identity coefficient alone determines the
vacuum eigenvalue.

## Remaining formal boundary

`MixedRowOneCondition` is now the mixed-expansion statement of Table I
Row 1, but Checkpoint 20 does not yet derive that condition automatically
from the separate Checkpoint-17 single-creation and higher-creation
sector theorems.

That final identification requires an embedding from the creator-only
terms of `NormalOrderedTerm` into the two pure-creation sector
representations already proved.

## Build

```bash
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- one finite mixed expansion is represented explicitly;
- Row-1 exclusion plus nonidentity syntax forces every remainder summand
  to vanish on the vacuum;
- the vacuum is proved an eigenstate with eigenvalue `Ω`.
