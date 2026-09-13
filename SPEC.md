# Formalization Specification 001

## Source
Gioia–Moudgalya–Motrunich,
Distinct Types of Parent Hamiltonians for Quantum States:
Insights from the W State as a Quantum Many-Body Scar.

## Scientific target
For a finite one-dimensional qubit chain, prove that if the
W state is an eigenstate of an extensive-local operator, then
the vacuum state is also an eigenstate.

## Leading assumptions
- finite N-qubit tensor-product Hilbert space
- bounded interaction range
- extensive-local operator
- W state is an eigenstate
- Hermiticity is not required for the primary result

## Lean target
Formalize the operator-basis/locality argument underlying
Corollary 1.

## Success criterion
Lean kernel verifies the theorem with no `sorry`.

## Deferred
- ground-state obstruction
- full parent-Hamiltonian decomposition
- type I/II/III classification
- asymptotic QMBS results
- momentum theorem
- RG/anomaly generalizations
