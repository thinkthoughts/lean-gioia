import LeanGioia.Operator

/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Hawkley
-/

/-!
# LeanGioia.LocalOperators

Checkpoint 3 for Formalization 001: the first source-proof checkpoint.

The source paper expands an extensive-local operator in a normal-ordered
hard-core-boson basis

`(creation operators) * (annihilation operators)`.

For Corollary 1, the key local mechanism is that every surviving nonidentity
normal-ordered term contains at least one annihilation operator. Such a term
annihilates the vacuum.

This checkpoint formalizes that mechanism. It does **not** yet prove that
the W-eigenstate condition forces the pure-creation coefficients to vanish;
that coefficient constraint is the next checkpoint.
-/

namespace LeanGioia

/-- Replace the bit at site `j` by `v`. -/
def setBit {N : ℕ} (b : Bitstring N) (j : Fin N) (v : Bool) : Bitstring N :=
  Function.update b j v

@[simp]
theorem setBit_same {N : ℕ} (b : Bitstring N) (j : Fin N) (v : Bool) :
    setBit b j v j = v := by
  simp [setBit]

/--
Hard-core annihilation operator at site `j`.

On amplitudes, the output coefficient of a configuration with site `j`
empty is the input coefficient of the corresponding configuration with
site `j` occupied. Configurations already occupied at `j` receive zero.
-/
def annihilateAt {N : ℕ} (j : Fin N) : Operator N where
  toFun := fun ψ b =>
    if b j = false then ψ (setBit b j true) else 0
  map_add' := by
    intro ψ φ
    funext b
    by_cases h : b j = false <;> simp [h]
  map_smul' := by
    intro c ψ
    funext b
    by_cases h : b j = false <;> simp [h]

/--
Hard-core creation operator at site `j`.

On amplitudes, the output coefficient of a configuration with site `j`
occupied is the input coefficient of the corresponding configuration with
site `j` empty. Configurations empty at `j` receive zero.
-/
def createAt {N : ℕ} (j : Fin N) : Operator N where
  toFun := fun ψ b =>
    if b j = true then ψ (setBit b j false) else 0
  map_add' := by
    intro ψ φ
    funext b
    by_cases h : b j = true <;> simp [h]
  map_smul' := by
    intro c ψ
    funext b
    by_cases h : b j = true <;> simp [h]

/-- Setting any site to `true` cannot produce the vacuum configuration. -/
theorem setBit_true_ne_vacuum {N : ℕ} (b : Bitstring N) (j : Fin N) :
    setBit b j true ≠ vacuumBits N := by
  intro h
  have hj := congrFun h j
  simp [setBit, vacuumBits] at hj

/--
A single hard-core annihilation operator kills the vacuum.

This is the first lemma in the formalization that directly implements a
mechanism used in the source proof of Corollary 1.
-/
@[simp]
theorem annihilateAt_vacuum {N : ℕ} (j : Fin N) :
    annihilateAt j (vacuumState N) = 0 := by
  funext b
  by_cases h : b j = false
  · have hne : setBit b j true ≠ vacuumBits N :=
      setBit_true_ne_vacuum b j
    simp [annihilateAt, h, vacuumState, basisState, hne]
  · simp [annihilateAt, h]

/-- Composition of two operators, with `B` acting first. -/
def composeOperator {N : ℕ} (A B : Operator N) : Operator N :=
  A.comp B

@[simp]
theorem composeOperator_apply {N : ℕ} (A B : Operator N) (ψ : State N) :
    composeOperator A B ψ = A (B ψ) := by
  rfl

/-- Product of creation operators indexed by `js`. -/
def creationString {N : ℕ} : List (Fin N) → Operator N
  | [] => identityOperator N
  | j :: js => composeOperator (createAt j) (creationString js)

/--
Product of annihilation operators indexed by `ks`.

For a nonempty list, the head annihilator acts first; this is enough for the
vacuum-annihilation result needed below.
-/
def annihilationString {N : ℕ} : List (Fin N) → Operator N
  | [] => identityOperator N
  | k :: ks => composeOperator (annihilationString ks) (annihilateAt k)

/--
A normal-ordered operator string:
all creation operators are to the left of all annihilation operators.
-/
def normalOrderedString {N : ℕ}
    (creators annihilators : List (Fin N)) : Operator N :=
  composeOperator (creationString creators) (annihilationString annihilators)

/--
Any nonempty product of annihilation operators annihilates the vacuum.
-/
@[simp]
theorem annihilationString_vacuum {N : ℕ} (k : Fin N) (ks : List (Fin N)) :
    annihilationString (k :: ks) (vacuumState N) = 0 := by
  simp [annihilationString, annihilateAt_vacuum]

/--
Source-proof checkpoint:

Any normal-ordered operator string containing at least one annihilation
operator annihilates the vacuum, regardless of how many creation operators
occur to its left.
-/
theorem normalOrderedString_vacuum_of_annihilator {N : ℕ}
    (creators : List (Fin N)) (k : Fin N) (ks : List (Fin N)) :
    normalOrderedString creators (k :: ks) (vacuumState N) = 0 := by
  simp [normalOrderedString]

end LeanGioia
