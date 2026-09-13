# Checkpoint 13 — selected higher-creation witness amplitude

This begins the other half of the first row of Table I: the source paper's
`n ≥ 2, m = 0` pure-creation case.

Appendix C.1.a writes

```text
s†_{j1} ... s†_{jn} |W⟩
  = (1/√N) ∑_l s†_{j1} ... s†_{jn} s†_l |0̄⟩
```

and then chooses `l` far from the local creator support.

Checkpoint 13 formalizes the selected-term part of that statement.

## Added

`LeanGioia/HigherCreation.lean`

with:

- `higherCreationWitnessBits`
- occupancy lemmas
- `higherCreationWitnessBits_nil`
- `setBit_higherCreationWitness_head_false`
- `creationString_wState_higherCreationWitness`
- `wState_higherCreationWitness_zero`
- `creationString_higherCreationWitness_nonzero`

## Verified statement

For a duplicate-free list `js` of creator sites and an extra site
`l ∉ js`:

```text
creationString js |W⟩
```

has amplitude exactly `wCoefficient N` on the basis configuration occupying

```text
js ∪ {l}.
```

For a nonempty creator list, that witness has zero W amplitude.

## Formal boundary

The paper's decisive locality statement is still the next step:

```text
selected range-R creation string
+ distant l
--------------------------------
no different range-R term can contribute to the same witness
```

Once that uniqueness statement is formalized, Checkpoint 5's
`coefficient_zero_of_uncancellable_witness` can force the selected
`n ≥ 2` coefficient to vanish.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- the selected pure-creation string is proved nonzero at its
  higher-particle witness;
- the witness is proved outside the W sector.
