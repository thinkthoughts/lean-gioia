# Checkpoint 21 — derive mixed Table I Row 1 from verified sectors

Checkpoint 20 proved Corollary 1 for one finite mixed normal-ordered
expansion once `MixedRowOneCondition` is available.

Checkpoint 21 removes that condition as a free assumption.

## Added

`LeanGioia/PureCreationBridge.lean`

with:

- `PureCreationSector`
- `PureCreationSector.creatorList`
- `PureCreationSector.coefficient`
- `PureCreationSectorBridge`
- `mixedRowOneCondition_of_sector_conclusion`
- `mixedRowOneCondition_of_verified_pure_creation_sectors`
- `corollary_one_from_verified_pure_creation_sectors`

## Representation bridge

Every mixed pure-creation term

```text
annihilators = []
creators ≠ []
```

is classified as either

```text
single j
```

or

```text
higher k.
```

The bridge requires that this classification preserve both:

```text
creator list
coefficient.
```

This prevents the sector identification from being merely a label.

## Verified chain

```text
single-creation W-eigenstate theorem
             +
higher-creation W-eigenstate theorem
             ↓
Checkpoint 17: both pure-creation coefficient functions = 0
             ↓
PureCreationSectorBridge
             ↓
MixedRowOneCondition
             ↓
Checkpoint 20
             ↓
G |0̄⟩ = Ω |0̄⟩
```

## Formal boundary

The higher-creation sector still carries the explicit locality/separated
witness assumptions collected in `HigherCreationWitnessData`.

Checkpoint 21 does not hide that boundary.  It closes the representation
gap between the already-proved sector results and the mixed
normal-ordered expansion.

## Build

```bash
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- `MixedRowOneCondition` is derived from the Checkpoint-17 sector theorem;
- the finite mixed Corollary-1 theorem no longer assumes Row 1 separately;
- the only substantive remaining boundary is the higher-creation locality
  data itself.
