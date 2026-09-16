# Checkpoint 42 — Reduce the Pure-Creation Representation Bridge

## Status

**Target:** use CP38's intrinsic single-versus-higher classification to remove
classifier/coverage machinery from the mixed Row-1 representation step.

**Artifact:** `LeanGioia/PureCreationRepresentation.lean`

## Purpose

`PureCreationSectorBridge` combines two tasks: intrinsic creator-list shape
classification and external matching to the single/higher families. CP38
already closes the first task.

CP42 introduces `PureCreationRepresentationMatches`, containing only:

```lean
single_match :
  creators = [j] → mixedCoeff i = singleCoeff j

higher_match :
  2 ≤ creators.length →
  ∃ k, creators = higherCreators k ∧ mixedCoeff i = higherCoeff k
```

(with the pure-creation annihilator hypothesis retained in both fields).

There is no `classify : ι → Option ...` and no separate `coverage` field.

## New theorem

`mixedRowOneCondition_of_representation_matches` uses
`pureCreationTerm_single_or_length_ge_two` from CP38 to select the intrinsic
branch, then the corresponding representation match, and finally the existing
`TableIRowOneConclusion` to prove the mixed coefficient is zero.

```text
nonempty pure-creation mixed term
        ↓
CP38 intrinsic classification
       / \
 singleton  length ≥ 2
    ↓          ↓
single_match  higher_match
       \      /
        matched coefficient
              ↓
       Table-I-Row-1 zero
              ↓
      MixedRowOneCondition
```

## What remains external

CP42 does not claim that list shape identifies an element of an arbitrary
higher-family index type `κ`. The higher branch still requires the genuine
representation fact

```lean
∃ k,
  (term i).creators = higherCreators k ∧
  mixedCoeff i = higherCoeff k
```

Higher-family eigenstate data, creator-set injectivity, periodic support
placement, and closed periodic geometry remain unchanged.

## Verification

If needed:

```bash
lake build LeanGioia.PureCreationClassification
```

Then:

```bash
lake env lean LeanGioia/PureCreationRepresentation.lean
```

A silent return is the CP42 file-level PASS reading point.

After verification:

```bash
git add CHECKPOINT_42.md LeanGioia/PureCreationRepresentation.lean
git commit -m "Checkpoint 42: reduce pure-creation representation bridge"
git push
```
