# Checkpoint 39 — Pure-creation support cardinality

## Goal

Bridge Checkpoint 38's intrinsic list-level classification to the support
cardinality required by the verified higher-creation machinery.

Checkpoint 38 gives the higher branch as

```lean
2 ≤ creators.length
```

while the higher-creation sector uses

```lean
2 ≤ creators.toFinset.card
```

Checkpoint 39 closes exactly that representation step under the existing
`Nodup` condition.

## Result

Mathlib provides:

```lean
List.toFinset_card_of_nodup
```

with the equality

```lean
xs.toFinset.card = xs.length
```

for `xs.Nodup`.

The checkpoint packages this fact for creator lists and proves that

```lean
xs.Nodup → 2 ≤ xs.length → 2 ≤ xs.toFinset.card
```

It then combines CP38 and CP39 to obtain the structural dichotomy for a
duplicate-free nonempty pure-creation term:

```lean
(∃ j : Fin N, t.creators = [j]) ∨
  2 ≤ t.creators.toFinset.card
```

## Why this checkpoint matters

The mixed normal-ordered syntax stores creators as a `List (Fin N)`,
whereas the higher-creation cancellation machinery reasons about creator
support using `toFinset`.

`Nodup` is therefore the exact condition under which the list-level
classification can be transferred to support cardinality without losing
creator multiplicity information.

No new indexing scheme or coefficient aggregation is introduced here.

## Remaining boundary

The remaining representation problem is no longer the
single-versus-higher classification or the higher support-cardinality
condition.

What remains is to identify each higher pure-creation mixed term with the
indexed higher-creation family used by `PureCreationSectorBridge`, while
preserving:

- its creator list;
- its coefficient;
- the family-level creator-support injectivity required by the existing
  higher-creation cancellation theorem.

That is the target to inspect for Checkpoint 40.

## File

`LeanGioia/PureCreationSupport.lean`

## Verification

Run:

```bash
lake env lean LeanGioia/PureCreationSupport.lean
```

After this succeeds, CP39 can be recorded as verified.
