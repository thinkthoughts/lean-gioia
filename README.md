# lean-gioia

Lean 4 formalization developed from specifications extracted from Lei Gioia's seminar material and related mathematical structure.

The repository separates three things deliberately:

1. **formalized mathematical statements** checked by Lean;
2. **explicit hypotheses / representation choices** supplied to those statements;
3. **physical interpretation**, which is not inferred merely from a successful formal proof.

The current proof architecture closes at **Checkpoint 52**.

## Main result of the CP47–CP52 reduction

The final theorem is

```lean
LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
```

in:

```text
LeanGioia/PeriodicOverlapAggregateClosed.lean
```

It derives the vacuum eigenstate conclusion for the mixed normal-ordered
operator from the stated periodic-overlap, eigenstate, support, and
representation hypotheses.

The important reduction relative to the earlier route is:

```text
historical route:
support injectivity
    → individual higher coefficient zero
    → mixed Row One
    → Corollary 1

reduced route:
support coverage
    → support-fiber aggregate coefficient zero
    → mixed Row One
    → Corollary 1
```

The final theorem therefore has **no hypothesis**

```lean
Function.Injective
  (fun k => (higherCreators k).toFinset)
```

The remaining representation condition is support **coverage**:

```lean
HigherCreationMixedSupportCovered term higherCreators
```

Existence of a represented support remains required; uniqueness of the external
index representing that support does not.

## Final checked route

```text
periodic-overlap geometry
        ↓
HigherCreationWitnessData
        ↓
support-fiber aggregation
        ↓
aggregate coefficient zero
        ↓
mixed-support coverage
        ↓
PureCreationAggregateRepresentationMatches
        ↓
MixedRowOneCondition
        ↓
vacuum_eigenstate_of_mixedRowOne
        ↓
Corollary 1
```

## Verification

From the repository root:

```bash
lake update
lake build
```

The CP52 theorem can be checked directly with:

```bash
lake env lean LeanGioia/PeriodicOverlapAggregateClosed.lean
lake build LeanGioia.PeriodicOverlapAggregateClosed
```

For the theorem and axiom audit:

```bash
cat > /tmp/cp52_audit.lean <<'EOF'
import LeanGioia.PeriodicOverlapAggregateClosed

#print LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
#print axioms LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
EOF

lake env lean /tmp/cp52_audit.lean
```

At the CP52 reading point, the theorem audit reports only the standard
Lean/mathlib axioms:

```text
propext
Classical.choice
Quot.sound
```

No project-specific axiom appears in that theorem's dependency report.

Placeholder audit:

```bash
grep -R -n -E '\bsorry\b|\badmit\b' \
  LeanGioia --include='*.lean'
```

At the CP52 reading point this returns no matches.

## Documentation

- [`docs/CHECKPOINT_INDEX.md`](docs/CHECKPOINT_INDEX.md) — proof-development map
- [`docs/THEOREM_MAP.md`](docs/THEOREM_MAP.md) — principal theorem dependencies
- [`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md) — build and audit commands
- [`docs/SCOPE.md`](docs/SCOPE.md) — formalized / assumed / out-of-scope boundary

Individual `CHECKPOINT_*.md` files remain the detailed development record.

## Evidence discipline

A Lean theorem establishes its conclusion from its stated hypotheses in the
formal model. It does not by itself establish that a physical system satisfies
those hypotheses.

In particular:

```text
formal derivation ≠ experimental validation
representation choice ≠ measured physical cause
specified mathematical relation ≠ established implementation
```

The theorem signatures are the authoritative statement of what has actually
been proved.
