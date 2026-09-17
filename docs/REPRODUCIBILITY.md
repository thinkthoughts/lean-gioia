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

A silent return to the shell prompt means the file typechecks.

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

Audit questions:

1. Is `Function.Injective (fun k => (higherCreators k).toFinset)` absent from
   the final theorem signature?
2. Is `HigherCreationMixedSupportCovered term higherCreators` visible?
3. Does the axiom report contain only expected Lean/mathlib axioms rather than
   project-specific axioms?

At the CP52 frozen reading point, the axiom report was:

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

At the CP52 frozen reading point this produced no output.

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

## Known non-blocking warnings

The final builds may replay linter/style warnings in earlier modules, including
unused `simp` arguments and style suggestions. These warnings are distinct from
proof failures.

A warning-cleanup pass may be useful for presentation, but it is not part of
the CP52 mathematical closure.
