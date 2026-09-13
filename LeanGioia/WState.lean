/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Hawkley
-/

/-!
# LeanGioia.WState

Checkpoint 1 for Formalization 001.

This file introduces:

* the vacuum state `|0̄⟩`,
* one-particle computational-basis configurations,
* one-particle basis states,
* the normalized W-state coefficient,
* the W state as the equal superposition of one-particle states.

The next checkpoint will add the operator language needed to state locality
and the eigenstate obstruction from Corollary 1 of the source paper.
-/

import LeanGioia.Basic

namespace LeanGioia

/-- The vacuum state `|0̄⟩ = |0⟩^{⊗ N}`. -/
def vacuumState (N : ℕ) : State N :=
  basisState (vacuumBits N)

/-- Bitstring containing exactly one excitation, at site `j`. -/
def singleExcitationBits {N : ℕ} (j : Fin N) : Bitstring N :=
  fun k => if k = j then true else false

/-- Computational-basis state with exactly one excitation, at site `j`. -/
def singleExcitationState {N : ℕ} (j : Fin N) : State N :=
  basisState (singleExcitationBits j)

/--
The coefficient `1 / √N` appearing in the normalized W state.

For `N = 0`, this definition evaluates using the field inverse of zero.
All physically relevant W-state statements will assume `0 < N`.
-/
noncomputable def wCoefficient (N : ℕ) : ℂ :=
  (((Real.sqrt (N : ℝ) : ℝ) : ℂ))⁻¹

/--
The `N`-qubit W state:
`|W⟩ = (1 / √N) ∑_j |1_j⟩`.

This definition is meaningful for every natural `N`; later physical
statements assume `0 < N`.
-/
noncomputable def wState (N : ℕ) : State N :=
  fun b =>
    wCoefficient N *
      ∑ j : Fin N, singleExcitationState j b

@[simp]
theorem vacuumState_apply_vacuum (N : ℕ) :
    vacuumState N (vacuumBits N) = 1 := by
  simp [vacuumState]

@[simp]
theorem singleExcitationState_apply_self {N : ℕ} (j : Fin N) :
    singleExcitationState j (singleExcitationBits j) = 1 := by
  simp [singleExcitationState]

theorem singleExcitationBits_ne_vacuum {N : ℕ} (j : Fin N) :
    singleExcitationBits j ≠ vacuumBits N := by
  intro h
  have hj := congrFun h j
  simp [singleExcitationBits, vacuumBits] at hj

@[simp]
theorem vacuumState_apply_singleExcitation {N : ℕ} (j : Fin N) :
    vacuumState N (singleExcitationBits j) = 0 := by
  simp [vacuumState, basisState, singleExcitationBits_ne_vacuum]

theorem singleExcitationBits_injective {N : ℕ} :
    Function.Injective (@singleExcitationBits N) := by
  intro i j hij
  by_contra hne
  have h := congrFun hij i
  simp [singleExcitationBits, hne] at h

@[simp]
theorem singleExcitationState_apply_other {N : ℕ} {i j : Fin N} (h : i ≠ j) :
    singleExcitationState i (singleExcitationBits j) = 0 := by
  apply basisState_apply_ne
  intro hbits
  exact h (singleExcitationBits_injective hbits.symm)

theorem wState_apply (N : ℕ) (b : Bitstring N) :
    wState N b =
      wCoefficient N *
        ∑ j : Fin N, singleExcitationState j b := by
  rfl

end LeanGioia
