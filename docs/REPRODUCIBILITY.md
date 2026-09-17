# Reproducibility

Run all commands from the repository root.

## Environment

Update dependencies:

```bash
lake update
```

## Full build

```bash
lake build
```

A successful full build is the repository-level verification reading point.

## Final CP52 file check

```bash
lake env lean LeanGioia/PeriodicOverlapAggregateClosed.lean
```

A silent return to the shell prompt records the file-level typecheck.

## Final CP52 target build

```bash
lake build LeanGioia.PeriodicOverlapAggregateClosed
```

## Theorem and axiom audit

```bash
cat > /tmp/cp52_audit.lean <<'EOF'
import LeanGioia.PeriodicOverlapAggregateClosed

#print LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
#print axioms LeanGioia.corollary_one_from_periodic_overlap_aggregate_closed
EOF

lake env lean /tmp/cp52_audit.lean
```

The CP52 theorem signature records the final representation condition as:

```lean
HigherCreationMixedSupportCovered term higherCreators
```

The CP52 frozen axiom reading point is:

```text
propext
Classical.choice
Quot.sound
```

## Placeholder audit

```bash
grep -R -n -E '\bsorry\b|\badmit\b' \
  LeanGioia --include='*.lean'
```

The CP52 frozen reading point produced an empty result.

## Git reading point

```bash
git status
git log -1 --oneline
```

The CP52 frozen reading point recorded:

```text
working tree clean
HEAD = main = origin/main = origin/HEAD
dd903c7 Add files via upload
```

## Build messages

The final builds may replay linter/style suggestions in earlier modules,
including unused `simp` arguments and `let`/`letI` suggestions. These can be
handled in a presentation cleanup pass while preserving the CP52 theorem
reading point.
