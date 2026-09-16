# Checkpoint 50 — Higher-Creation Aggregate Coefficient Zero

## Status

**Target:** replace creator-support injectivity and per-external-index
coefficient isolation with support-fiber aggregate coefficient isolation.

**Artifacts**
- `LeanGioia/HigherCreationAggregateZero.lean`
- `CHECKPOINT_50.md`

CP50 is the **reduced higher-creation coefficient checkpoint**.

## Why CP50 exists

The pre-CP50 proof route was:

```text
selected witness
    ↓
nonzero competitor
    ↓ locality uniqueness
same creator support
    ↓ support-map injectivity
same external index
    ↓
selected coefficient = 0
```

The audit shows that locality already forces equality of creator supports for
any nonzero competitor. The old `hinj` hypothesis is used afterward to turn
that support equality into equality of external indices.

CP47--49 give a representation-invariant alternative:

```text
same creator support
    ↓ CP48
same creationString
    ↓ CP49
fiber contributions aggregate
    ↓
aggregate coefficient
```

Therefore CP50 asks the eigenstate equation to isolate the coefficient of the
**support fiber**, rather than an arbitrary external label.

## New outside-fiber lemma

```lean
higherCreation_amplitude_zero_of_not_mem_supportFiber
```

states that a term outside the selected support fiber has zero amplitude on
the selected higher-creation witness.

The proof retains the existing locality argument. If such a term had nonzero
amplitude, locality uniqueness would force its creator support to equal the
selected support, contradicting its exclusion from the fiber.

No creator-support injectivity hypothesis is needed.

## Selected-witness aggregation

```lean
higherCreationFamilyOperator_selected_witness_aggregate
```

proves

```text
family amplitude at selected witness
=
aggregate coefficient of selected support
*
representative creationString amplitude
```

under family-level `Nodup`.

Outside-fiber terms vanish by locality. Inside-fiber terms have the same
creation-string operator by CP48 and combine by support aggregation.

## Main CP50 theorem

```lean
higherCreation_aggregate_coefficient_zero_of_eigenstate
```

concludes

```lean
higherCreationAggregateCoeff
  coeff creators (creators i₀).toFinset = 0
```

from:

- `0 < N`;
- the W-state eigenstate hypothesis;
- family-level duplicate-free creator lists;
- at least two distinct sites in the selected support;
- a witness site outside the selected creator list;
- the existing separated-local-competitor hypothesis.

There is **no**

```lean
Function.Injective (fun i => (creators i).toFinset)
```

hypothesis.

## Why the conclusion is aggregate zero

CP50 deliberately does not claim that each external coefficient vanishes
where multiple indices represent the same support.

The operator can distinguish the combined contribution

```text
(sum of coefficients in the support fiber) • creationString
```

but it need not distinguish how that scalar was split among duplicate
external labels.

Thus the representation-invariant conclusion is aggregate coefficient zero.

The old individual-coefficient theorem is recovered conceptually in the
singleton-fiber case supplied by support-map injectivity.

## Family-level form

```lean
all_higherCreation_aggregate_coefficients_zero_of_eigenstate
```

states that every support represented by the external family has aggregate
coefficient zero, given witness data for each selected family member.

## What CP50 closes

CP50 removes support-map injectivity from the higher-creation
coefficient-isolation argument at the correct representation level:

```text
external labels
    ↓ group by creator support
support fibers
    ↓
aggregate coefficients
    ↓ eigenstate + witness/locality
aggregate coefficients = 0
```

This is the intended payoff of CP47--49.

## What CP50 leaves open

CP50 does not yet:

- change the existing `TableIRowOneConclusion`;
- globally quotient/reindex the higher family by support;
- delete or rewrite the older injective CP16/CP17 theorems;
- propagate aggregate-zero through the mixed-expansion representation bridge;
- produce a reduced end-to-end Corollary-1 theorem.

The existing verified route remains intact.

## Next checkpoint

**CP51 — reduced downstream integration.**

The next task is to expose the CP50 support-aggregate conclusion through the
smallest useful paper-facing/mixed-representation interface, without
redesigning the repository.

## Verification

From the repository root:

```bash
lake env lean LeanGioia/HigherCreationAggregateZero.lean
```

A silent return is the CP50 file-level PASS reading point.

Then:

```bash
lake build LeanGioia.HigherCreationAggregateZero
```

If both pass, freeze CP50 before beginning CP51.
