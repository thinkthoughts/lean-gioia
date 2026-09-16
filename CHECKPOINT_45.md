# Checkpoint 45 — Remaining-Hypothesis and Axiom Audit

## Status

**Target:** audit the public assumptions and foundational dependencies of the Checkpoint-44 end-to-end theorem before another hypothesis-reduction step.

**Audited theorem:** `LeanGioia.corollary_one_from_periodic_overlap_representation_closed`

**Checkpoint type:** documentation / audit reading point. CP45 intentionally introduces no new Lean theorem.

## Reading point

Checkpoint 44 reunited the closed periodic-overlap/locality branch with the reduced pure-creation representation branch. CP45 records what remains in that theorem interface now.

The Lake build completed successfully:

```text
Build completed successfully (8806 jobs).
```

The theorem was inspected with both `#print` and `#print axioms`.

## Verified dependency chain

```text
periodicOverlapModel_closed
        ↓
higherCreationFamily_toFinset_card_ge_two
        ↓
all_higherCreationWitnessData_of_finiteRange
        ↓
tableI_row_one_pure_creation_coefficients_zero
        ↓
corollary_one_from_representation_matches
        ↓
IsEigenstate
  (mixedNormalOrderedOperator Ω mixedCoeff term)
  (vacuumKet N) Ω
```

This confirms that periodic geometry, structural support reduction, higher-creation witness construction, Table-I-Row-1, and the reduced representation route are connected in the kernel-checked CP44 theorem.

## Public hypotheses remaining after CP44

### Geometric / locality premises

```lean
hNR : 3 * R < N
start : κ → Fin N
hcreators :
  ∀ k : κ,
    (higherCreators k).toFinset ⊆ cyclicBlock N R (start k)
```

The earlier temporary `OverlapOffsetBound` is not a public hypothesis.

### Structural higher-sector premises

```lean
hsupport : HigherCreationFamilyListSupport higherCreators
hNodup : ∀ k : κ, (higherCreators k).Nodup
```

CP40 derives `∀ k, 2 ≤ (higherCreators k).toFinset.card` internally. Thus `hatLeastTwo` is no longer independent caller-supplied data.

### Source / eigenstate premises

```lean
hSingleEig :
  IsEigenstate
    (singleCreationOperator singleCoeff)
    (wState N) singleEig

hHigherEig :
  IsEigenstate
    (higherCreationFamilyOperator higherCoeff higherCreators)
    (wState N) higherEig
```

These remain explicit inputs to the Table-I-Row-1 sector theorem. CP45 finds no basis for treating them as representation artifacts.

### Higher-family indexing premise

```lean
hinj :
  Function.Injective
    (fun k : κ => (higherCreators k).toFinset)
```

This feeds directly into `tableI_row_one_pure_creation_coefficients_zero`, rather than periodic-overlap geometry.

**CP45 decision:** investigate `hinj` next at its actual source in `HigherCreationComplete.lean` and `TableIRowOne.lean`.

### Mixed ↔ pure representation premise

```lean
hrep :
  PureCreationRepresentationMatches
    mixedCoeff term
    singleCoeff higherCoeff higherCreators
```

CP42 removed the caller-supplied classifier and coverage machinery of `PureCreationSectorBridge`. The remaining `hrep` still performs genuine representation work: a structurally higher mixed pure-creation term must be matched to some `k : κ` with matching creator list and coefficient.

CP45 therefore does not classify `hrep` as redundant.

### Mixed-expansion structural premise

```lean
hnonid : NonidentityNormalOrderedFamily term
```

This remains the structural premise consumed by the mixed-expansion vacuum-eigenstate theorem.

### Size premise

```lean
hN3 : 3 ≤ N
```

This remains visible in the sector/Table-I route and is separate from `3 * R < N`.

## Hypotheses already removed or internalized

By CP45, the public CP44 theorem no longer asks the caller for:

```text
OverlapOffsetBound
explicit three-R cover containment
hatLeastTwo / toFinset.card ≥ 2
HigherCreationWitnessData
PureCreationSectorBridge
classifier coverage for pure-creation terms
```

Those obligations are either proved internally or replaced by narrower structural/representation interfaces.

## Axiom audit

```lean
#print axioms LeanGioia.corollary_one_from_periodic_overlap_representation_closed
```

reported:

```text
[propext, Classical.choice, Quot.sound]
```

No project-specific axiom or unfinished proof assumption appears in the reported dependency set. These are foundational Lean/mathlib dependencies used by the formal development; CP45 records them explicitly rather than describing the theorem as axiom-free.

## CP45 conclusion

The CP44 theorem is a kernel-checked end-to-end reading point with its remaining assumptions visible at the public interface.

The next reduction target selected by this audit is:

```lean
Function.Injective
  (fun k => (higherCreators k).toFinset)
```

CP45 has **not** shown this hypothesis redundant. Its use is localized enough to inspect precisely, while `PureCreationRepresentationMatches` still visibly carries genuine external representation information.

## CP46 target

**Investigate higher-family injectivity at its source.**

Inspect:

```text
LeanGioia/HigherCreationComplete.lean
LeanGioia/TableIRowOne.lean
```

Determine exactly why creator-set injectivity is required. Reduce or reformulate `hinj` only if the existing proofs support that reduction. If injectivity is mathematically necessary for the current coefficient-separation argument, document that boundary rather than removing it artificially.

## Reproduction

```bash
lake build LeanGioia.PeriodicOverlapRepresentationClosed

cat > /tmp/LeanGioiaCP45Audit.lean <<'EOF'
import LeanGioia.PeriodicOverlapRepresentationClosed

#print LeanGioia.corollary_one_from_periodic_overlap_representation_closed
#print axioms LeanGioia.corollary_one_from_periodic_overlap_representation_closed
EOF

lake env lean /tmp/LeanGioiaCP45Audit.lean
```

Expected reading points are a successful build and:

```text
[propext, Classical.choice, Quot.sound]
```

## Checkpoint result

**CP45 PASS — remaining-hypothesis and axiom audit complete.**

No new `.lean` artifact is introduced. This checkpoint documents the verified CP44 state before CP46 changes any further theorem interface.
