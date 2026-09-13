# Checkpoint 3 — first source-proof checkpoint

This checkpoint begins formalizing the actual mechanism used in the source
paper's proof of Corollary 1.

## Source-proof boundary

The paper writes extensive-local operators in a normal-ordered basis of
hard-core creation and annihilation operators. Its explanation of Corollary 1
uses two steps:

1. the W-eigenstate condition plus locality excludes nonzero pure-creation
   terms;
2. every remaining nonidentity normal-ordered term contains an annihilation
   operator and therefore annihilates the vacuum.

Checkpoint 3 proves step 2.

## Added

`LeanGioia/LocalOperators.lean`

with:

- `setBit`
- `annihilateAt`
- `createAt`
- `annihilateAt_vacuum`
- operator composition
- creation strings
- annihilation strings
- normal-ordered strings
- `normalOrderedString_vacuum_of_annihilator`

## Updated

`LeanGioia.lean` imports `LeanGioia.LocalOperators`.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- a normal-ordered string with at least one annihilator is kernel-checked
  to annihilate the vacuum.

## Next checkpoint

Formalize the missing source step:

`W eigenstate + finite-range/local normal-ordered expansion`
→ `pure-creation coefficients vanish`.

That is the coefficient constraint needed to assemble Corollary 1 itself.
