import Mathlib

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Hawkley
-/

/-!
# LeanGioia.Basic

Minimal finite-qubit state representation for the first `lean-gioia`
formalization checkpoint.
...
-/

namespace LeanGioia

/-- A computational-basis configuration of `N` qubits. -/
abbrev Bitstring (N : ℕ) := Fin N → Bool

/-- A finite `N`-qubit state, represented by its computational-basis amplitudes. -/
abbrev State (N : ℕ) := Bitstring N → ℂ

/-- The all-zero computational-basis configuration. -/
def vacuumBits (N : ℕ) : Bitstring N :=
  fun _ => false

/-- Computational-basis state concentrated at `b`. -/
def basisState {N : ℕ} (b : Bitstring N) : State N :=
  fun x => if x = b then 1 else 0

@[simp]
theorem basisState_apply_self {N : ℕ} (b : Bitstring N) :
    basisState b b = 1 := by
  simp [basisState]

@[simp]
theorem basisState_apply_ne {N : ℕ} {b x : Bitstring N} (h : x ≠ b) :
    basisState b x = 0 := by
  simp [basisState, h]

end LeanGioia
