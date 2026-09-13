# lean-gioia

Lean formalizations of results from Lei Gioia's research, developed from seminar and paper specifications.

## Initial formalization

The first target comes from Gioia–Moudgalya–Motrunich, *Distinct Types of Parent Hamiltonians for Quantum States: Insights from the W State as a Quantum Many-Body Scar*.

The initial scientific boundary is:

> If the W state is an eigenstate of an extensive-local operator, then the vacuum state is also an eigenstate.

See [`SPEC.md`](SPEC.md) for the controlling formalization specification.

## Repository structure

```text
LeanGioia/
  Basic.lean
  WState.lean
docs/
  CU_Seminar_260911/
sources/
SPEC.md
LeanGioia.lean
lakefile.toml
lean-toolchain
```

- `LeanGioia/Basic.lean` — shared definitions introduced only as required by the source specification.
- `LeanGioia/WState.lean` — Formalization 001.
- `docs/CU_Seminar_260911/` — seminar context and reading-point documentation.
- `sources/` — source papers used to define formalization boundaries.
- `SPEC.md` — scientific and formal boundary for the current Lean target.

## Workflow

Seminar → source paper → stated result → formalization specification → Lean verification → next specification

## Build

```text
lake update
lake build
```

The project currently follows the same Lean/mathlib revision used by `lean-perovskite`:

```text
leanprover/lean4:v4.34.0-rc2
mathlib v4.34.0-rc2
```

## Current next step

Choose the smallest faithful Lean representation of:

- a finite `N`-qubit state space,
- the vacuum state,
- the W state,
- extensive locality / bounded interaction range,
- the eigenstate relation,

then formalize the operator-basis argument underlying the W-state → vacuum-state eigenstate obstruction.

## Deferred

- W-state ground-state obstruction
- full parent-Hamiltonian decomposition
- type I / II / III classification
- asymptotic QMBS results
- nonzero-momentum circuit obstruction
- RG / anomaly generalizations
