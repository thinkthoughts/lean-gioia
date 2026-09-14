# Checkpoint 31 — close the Fin/Nat relative-offset bridge

Checkpoint 30 reduced the remaining modular representation issue to

```text
FinRelativeOffsetValueBridge N
```

meaning

```text
(a + d - b).val
=
(a.val + N + d.val - b.val) % N.
```

Checkpoint 31 proves that value identity and therefore obtains
`CanonicalOffsetComposition` and `CanonicalOverlapInThreeRRegion`
without additional arithmetic assumptions.

## Added

`LeanGioia/FinRelativeOffset.lean`

with:

- `fin_add_sub_val_eq_relativeOverlapOffset`
- `finRelativeOffsetValueBridge`
- `canonicalOffsetComposition_closed`
- `canonicalOverlapInThreeRRegion_closed`

## Remaining boundary

The group/Nat representation bridge is closed.

The next checkpoint should translate the already-proved region dichotomy

```text
cyclicOffset < 2R
∨
N - R ≤ cyclicOffset
```

into `InThreeRCoverByOffset`, i.e. actual membership in the forward
`2R` or backward `R` component of the explicit interaction cover.

## Build

```bash
lake build
```
