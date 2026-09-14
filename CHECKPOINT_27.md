# Checkpoint 27 — canonical cyclic-offset arithmetic

Checkpoint 26 isolated the final PBC statement as `OverlapOffsetBound`.

Checkpoint 27 introduces a canonical clockwise distance:

```text
cyclicOffset N start x = (x + N - start) mod N.
```

and proves the basic equivalence

```text
x ∈ cyclicBlock N width start
↔
cyclicOffset N start x < width
```

for `width ≤ N`.

This is the arithmetic normalization needed before proving the overlap
bound: the remaining problem can now be expressed using inequalities
between offsets rather than repeated modular equalities.

## Added

`LeanGioia/CyclicOffset.lean`

with:

- `cyclicOffset`
- `cyclicOffset_lt`
- `cyclicOffset_self`
- `cyclicOffset_spec`
- `cyclicOffset_lt_of_mem_cyclicBlock`
- `mem_cyclicBlock_of_cyclicOffset_lt`
- `mem_cyclicBlock_iff_cyclicOffset_lt`

## Next checkpoint

Checkpoint 28 can use these lemmas to prove the triangle/overlap inequality
for cyclic offsets and then discharge `OverlapOffsetBound`.

## Build

```bash
lake build
```
