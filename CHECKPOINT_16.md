# Checkpoint 16 — assemble the `n ≥ 2, m = 0` obstruction

Checkpoint 16 combines the higher-creation work from Checkpoints 13–15.

For a finite family

```text
G = ∑ᵢ cᵢ creationString(jsᵢ)
```

select a term `i₀` whose creator set contains at least two sites, and choose
a distant witness site `l`.

## Added

`LeanGioia/HigherCreationComplete.lean`

with:

- `higherCreationFamilyOperator`
- `competing_higherCreation_amplitude_zero`
- `higherCreationFamilyOperator_selected_witness`
- `selected_higherCreation_witness_wState_zero`
- `higher_creation_coefficient_zero_of_eigenstate`

## Verified chain

```text
selected string has nonzero witness amplitude          [Checkpoint 13]
                    ↓
nonzero competitor gives same witness representation  [Checkpoint 15]
                    ↓
locality uniqueness gives same creator set             [Checkpoint 14]
                    ↓
injective creator-set labels give same family index
                    ↓
all other family terms vanish at selected witness
                    ↓
W eigenstate equation + W(witness)=0
                    ↓
selected coefficient = 0
```

## Formal boundary

The locality condition is still represented by

```text
SeparatedLocalCompetitor A l B
```

which means that a local competitor containing the distant site `l` is
disjoint from the selected local support `A`.

Thus this checkpoint closes the `n ≥ 2, m = 0` coefficient argument once
that locality consequence and a separated witness site are supplied.  It
does not yet derive those hypotheses from a complete periodic range-`R`
operator-expansion structure.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- the selected coefficient in the `n ≥ 2` pure-creation family is forced
  to zero from the W-eigenstate equation and locality-uniqueness hypotheses.

## Next checkpoint

Checkpoint 17 can package the two branches of the first Table I row:

- `n = 1, m = 0`: closed end-to-end in Checkpoint 12;
- `n ≥ 2, m = 0`: closed at coefficient level here under the explicit
  locality/separated-witness hypotheses.

The remaining improvement would be to derive the Checkpoint-16 locality
hypotheses directly from a concrete periodic range-`R` expansion.
