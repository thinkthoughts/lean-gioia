# Checkpoint 14 — locality uniqueness for the higher-creation witness

This checkpoint formalizes the combinatorial uniqueness step in the
`n ≥ 2, m = 0` argument from Appendix C.1.a.

The selected creator set is `A`, and the distant witness site is `l`.
A competing pure-creation term with creator set `B` can reach the same
higher-particle witness only if some single W-input site `q` satisfies

```text
insert q B = insert l A.
```

For `|A| ≥ 2`, locality/separation gives:

```text
if l ∈ B, then B is disjoint from A.
```

From these facts Lean proves that necessarily

```text
B = A.
```

## Added

`LeanGioia/HigherCreationUniqueness.lean`

with:

- `SeparatedLocalCompetitor`
- `RepresentsHigherCreationWitness`
- `higherCreationWitness_creatorSet_unique`
- `higherCreationWitness_creatorList_toFinset_unique`

## Source-proof meaning

The proof mirrors the paper's statement that the distant `(n+1)`-particle
configuration cannot be produced by a different range-`R` pure-creation
term.

The locality consequence is kept explicit as

```text
l ∈ B → Disjoint B A
```

rather than claiming that periodic range geometry has already been fully
encoded for arbitrary competing terms.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- any local competing creator set representing the same distant witness is
  proved equal to the selected creator set.

## Next checkpoint

Checkpoint 15 should connect a nonzero amplitude of a competing creation
string at the selected witness to a
`RepresentsHigherCreationWitness` statement.

Then Checkpoint 14 will imply that every contributing competing term has
the same creator set as the selected term, allowing Checkpoint 5's
uncancellable-witness lemma to force the selected coefficient to zero.
