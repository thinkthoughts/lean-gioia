# Checkpoint 18 — Corollary 1 vacuum-eigenstate assembly

The paper states:

```text
Corollary 1.
If |W⟩ is an eigenstate of an extensive-local operator,
then |0̄⟩ is also an eigenstate.
```

The source derives this from Table I: pure-creation terms are forbidden, so
every remaining nonidentity normal-ordered term contains at least one
annihilation operator and therefore annihilates the vacuum.

Checkpoint 18 packages the final operator-level implication.

## Added

`LeanGioia/CorollaryOne.lean`

with:

- `vacuumKet`
- `VacuumAnnihilating`
- `vacuumAnnihilatingFamilyOperator`
- `vacuumAnnihilatingFamilyOperator_apply_vacuum`
- `corollaryOneOperator`
- `vacuum_eigenstate_of_no_pure_creation_remainder`
- `CorollaryOneExpansion`
- `corollary_one_at_expansion_boundary`

## Verified statement

For

```text
G = Ω 1 + ∑ᵢ cᵢ Tᵢ
```

where every remaining nonidentity term satisfies

```text
Tᵢ |0̄⟩ = 0,
```

Lean proves

```text
G |0̄⟩ = Ω |0̄⟩.
```

The packaging also carries the verified Table-I-Row-1 conclusion that the
pure-creation coefficient functions are zero.

## Formal boundary

This is the Corollary 1 theorem **at the current expansion boundary**.

The remaining unformalized bridge to the source's full statement is:

```text
one general finite-range normal-ordered expansion
+ Table I Row 1
-----------------------------------------------
every remaining nonidentity term has ≥ 1 annihilator
-----------------------------------------------
VacuumAnnihilating
```

The source supports exactly this argument.  The repository has already
proved the pure-creation exclusion sector-by-sector and has the earlier
local-operator machinery for annihilation behavior, but it does not yet
encode the entire mixed `n,m` expansion as a single datatype.

## Build

```text
lake build
```

## Success criterion

- build succeeds;
- no `sorry`;
- a finite sum of vacuum-annihilating terms is proved to annihilate vacuum;
- adding an identity coefficient `Ω` makes vacuum an eigenstate with
  eigenvalue `Ω`;
- Table I Row 1 is explicitly carried in the Corollary-1 expansion package.

## Next checkpoint

Checkpoint 19 should close the remaining basis bridge by introducing a
single normal-ordered term datatype with explicit creator and annihilator
lists, and prove:

```text
annihilator list nonempty
→ term annihilates vacuum.
```

Then Table I Row 1 can eliminate the `annihilator list = []`,
`creator list ≠ []` case in one mixed expansion.
