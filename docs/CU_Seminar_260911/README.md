# CU Seminar — 260911

## Seminar

**Renormalization, symmetries, and anomalies:  
Principles for entangled quantum materials**

Lei Gioia  
Caltech → Boulder

## Reading Point

This directory records the seminar context that led to the
`lean-gioia` formalization project.

The talk connected:

- no-go theorems
- possible theories and model engineering
- topological responses
- quantum state preparation

with a focus on renormalization, symmetries, and anomalies in
entangled quantum materials.

## Seminar Questions

The talk identified several next-step questions around W states
and renormalization-group structure:

1. Is there an anomaly reason for the observed features?
2. Is the lowest excitation always a W-like state ("particle ansatz")?
3. Are these features understandable in the RG-of-symmetries framework?

These questions motivate the broader project, but they are not
claims of the initial Lean formalization.

## Formalization Boundary

The first Lean target is narrower:

> If the W state is an eigenstate of an extensive-local operator,
> then the vacuum state is also an eigenstate.

See [`../../SPEC.md`](../../SPEC.md) for the formalization
specification.

## Source Material

- `Gioia_Seminar_Pic.png` — opening seminar slide
- additional seminar slides may be added here as documentation

## Next Steps

1. Formalize the W state and vacuum state.
2. Specify extensive locality and bounded interaction range.
3. Formalize the operator-basis constraints.
4. Prove the W-state → vacuum-state eigenstate obstruction.
5. Compare the Lean statement directly with Corollary 1 of the
   source paper.
6. Only then consider the ground-state obstruction and the seminar's
   broader open questions.
