import LeanGioia.WState

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Hawkley
-/

/-!
# LeanGioia.Operator

Checkpoint 2 for Formalization 001.

This file introduces only the linear-operator and eigenstate layer needed
before formalizing locality.

The source paper studies extensive-local operators `G` satisfying

`G |W⟩ = λ |W⟩`

and proves that locality forces the vacuum `|0̄⟩` to be an eigenstate as
well.  We deliberately do not encode locality in this checkpoint.

A state is already represented in `LeanGioia.Basic` as a complex-valued
amplitude function on finite computational-basis configurations.  Here an
operator is a complex-linear map on that state space.
-/

namespace LeanGioia

/-- A complex-linear operator on the finite `N`-qubit state space. -/
abbrev Operator (N : ℕ) := State N →ₗ[ℂ] State N

/--
`ψ` is an eigenstate of `A` with eigenvalue `λ`.

This records the eigenvalue equation itself.  For the W state and vacuum
state used in the project, nonzeroness will be proved separately where
needed rather than built into this predicate.
-/
def IsEigenstate {N : ℕ} (A : Operator N) (ψ : State N) (λ : ℂ) : Prop :=
  A ψ = λ • ψ

/-- The identity operator on `N` qubits. -/
def identityOperator (N : ℕ) : Operator N :=
  LinearMap.id

@[simp]
theorem identityOperator_apply {N : ℕ} (ψ : State N) :
    identityOperator N ψ = ψ := by
  rfl

@[simp]
theorem identityOperator_eigenstate {N : ℕ} (ψ : State N) :
    IsEigenstate (identityOperator N) ψ 1 := by
  simp [IsEigenstate]

@[simp]
theorem zeroOperator_eigenstate {N : ℕ} (ψ : State N) :
    IsEigenstate (0 : Operator N) ψ 0 := by
  simp [IsEigenstate]

/--
The eigenvalue equation may be checked coefficient-by-coefficient in the
computational basis.
-/
theorem isEigenstate_iff_amplitudes {N : ℕ}
    (A : Operator N) (ψ : State N) (λ : ℂ) :
    IsEigenstate A ψ λ ↔
      ∀ b : Bitstring N, A ψ b = λ * ψ b := by
  constructor
  · intro h b
    have hb := congrFun h b
    simpa using hb
  · intro h
    apply funext
    intro b
    simpa using h b

/-- The vacuum is an eigenstate of the identity operator. -/
@[simp]
theorem vacuum_identity_eigenstate (N : ℕ) :
    IsEigenstate (identityOperator N) (vacuumState N) 1 := by
  simp

/-- The W state is an eigenstate of the identity operator. -/
@[simp]
theorem w_identity_eigenstate (N : ℕ) :
    IsEigenstate (identityOperator N) (wState N) 1 := by
  simp

end LeanGioia
