# Checkpoint 40 — Pure-Creation Family Support

## Status

**Target:** reduce a higher-family support hypothesis from finite-set cardinality
to the structural list-level classification established by the preceding
checkpoints.

**Artifact:** `LeanGioia/PureCreationFamilySupport.lean`

## Purpose

Checkpoint 40 is a **hypothesis-reduction checkpoint**. It is intentionally
not another large end-to-end Corollary-1 theorem.

The existing periodic-overlap route consumes the family hypothesis

```lean
∀ k, 2 ≤ (higherCreators k).toFinset.card
```

while the structural classification of a higher pure-creation term naturally
produces the list-level statement

```lean
2 ≤ (higherCreators k).length
```

Under `List.Nodup`, these are connected by
`List.toFinset_card_of_nodup`.

## New interface

The checkpoint introduces

```lean
def HigherCreationFamilyListSupport
    (higherCreators : κ → List (Fin N)) : Prop :=
  ∀ k, 2 ≤ (higherCreators k).length
```

and proves the family-level reduction

```lean
theorem higherCreationFamily_toFinset_card_ge_two
    (higherCreators : κ → List (Fin N))
    (hsupport : HigherCreationFamilyListSupport higherCreators)
    (hnodup : ∀ k, (higherCreators k).Nodup) :
    ∀ k, 2 ≤ (higherCreators k).toFinset.card
```

A one-list helper theorem makes the representation step explicit.

## What CP40 closes

CP40 removes the need to treat `toFinset.card ≥ 2` as independent mathematical
data once the higher family has already been structurally classified and its
creator lists are nodup.

The intended chain is now:

```text
higher pure-creation classification
        ↓
list length ≥ 2
        ↓  + Nodup
CP40: toFinset.card ≥ 2
        ↓
periodic-overlap witness machinery
        ↓
HigherCreationWitnessData
```

## What CP40 deliberately leaves open

This checkpoint does **not** eliminate or reconstruct:

- the higher-family index type `κ`;
- the higher-family eigenstate hypothesis;
- injectivity of `k ↦ (higherCreators k).toFinset`;
- creator/coefficient matching between the mixed expansion and higher family;
- `PureCreationSectorBridge`.

Those are representation/indexing questions rather than support-cardinality
questions and should remain visible for subsequent checkpoints.

## Verification

From the repository root:

```bash
lake env lean LeanGioia/PureCreationFamilySupport.lean
```

A silent return to the shell prompt is the CP40 file-level PASS reading point.

For a Lake-built object if needed by the next checkpoint:

```bash
lake build LeanGioia.PureCreationFamilySupport
```
