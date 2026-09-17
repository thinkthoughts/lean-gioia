# lean-gioia

Lean 4 formalization of the W-state locality obstruction developed from Lei
Gioia's seminar material and the corresponding source result.

**Start with the illustrated report:** [`REPORT/README.md`](REPORT/README.md)  
**Report page:** `labreports.app/gioia`

The report gives a visual route from the source reading point through
finite-range witness geometry and support-fiber aggregation to the checked
vacuum-eigenstate conclusion. Figure D also shows how a leading researcher can
use this repository from a reading point to a checked specification.

For the formal development, this repository organizes:

1. **formalized mathematical statements** checked by Lean;
2. **explicit hypotheses and representation choices** supplied to those statements;
3. **source-to-formal comparison and physical interpretation** at specified reading points.

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

CP47–CP52 refine the higher-creation representation from individual external
indices to the aggregate coefficient carried by a common finite creator
support.

**The operator-visible quantity is the aggregate coefficient carried by a
common finite creator support.**

```text
earlier route:
support injectivity
    → individual higher coefficient zero
    → mixed Row One
    → Corollary 1

CP47–CP52 route:
support coverage
    → support-fiber aggregate coefficient zero
    → mixed Row One
    → Corollary 1
```

The final representation condition uses support **coverage**:

```lean
HigherCreationMixedSupportCovered term higherCreators
```

Each higher pure-creation support appearing in the mixed expansion is
represented in the external higher-creation family. Multiple external indices
may share that support, with their coefficients collected by the support-fiber
aggregate.

## Representation reading point

The checked CP52 route begins with a finite family of normal-ordered
creation/annihilation terms represented by:

```lean
mixedNormalOrderedOperator Ω mixedCoeff term
```

The source-to-Lean comparison therefore includes a distinct representation
step:

```text
source extensive-local operator
        ↓
normal-ordered representation specification
        ↓
mixedNormalOrderedOperator
```

The source evidence and representation argument specifying this step belong in
the source-to-Lean map. The Lean theorem then checks the implication from the
supplied representation and its explicit hypotheses.

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

At the CP52 reading point, the theorem dependency report is:

```text
propext
Classical.choice
Quot.sound
```

The project proof layer uses the theorem signatures and these standard
Lean/mathlib foundations.

Placeholder audit:

```bash
grep -R -n -E '\bsorry\b|\badmit\b' \
  LeanGioia --include='*.lean'
```

At the CP52 reading point this returns an empty result.

## Documentation

- [`REPORT/README.md`](REPORT/README.md) — illustrated report and Figures A–D
- [`SPECIFICATION.md`](SPECIFICATION.md) — closed CP52 formalization specification
- [`docs/SOURCE_TO_LEAN.md`](docs/SOURCE_TO_LEAN.md) — source-to-formal correspondence
- [`docs/CHECKPOINT_INDEX.md`](docs/CHECKPOINT_INDEX.md) — proof-development map
- [`docs/THEOREM_MAP.md`](docs/THEOREM_MAP.md) — principal theorem dependencies
- [`docs/REPRODUCIBILITY.md`](docs/REPRODUCIBILITY.md) — build and audit commands
- [`docs/SCOPE.md`](docs/SCOPE.md) — formalized statements, supplied specifications,
  representation bridge, and physical-comparison layer

Individual `CHECKPOINT_*.md` files provide the detailed development record.

## Evidence discipline

A Lean theorem specifies a checked implication from stated hypotheses to its
conclusion.

For this repository, the evidence chain is:

```text
source specification
    → normal-ordered representation specification
    → mixedNormalOrderedOperator

geometry / separation specifications
    → PeriodicOverlapCreationModel
    → HigherCreationWitnessData
    → checked support-fiber aggregate-zero result
    → representation bridge
    → MixedRowOneCondition
    → vacuum_eigenstate_of_mixedRowOne
    → Corollary 1
    → physical comparison at specified reading points
```

The theorem signatures provide the authoritative reading point for the
formalized claims.
