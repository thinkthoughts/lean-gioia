import LeanGioia.LocalOperators

/-!
# LeanGioia.PureCreation

Checkpoint 4: the algebraic core of Appendix C.1.a.

The full paper argument also uses finite-range spatial separation to rule
out cancellation among distinct local pure-creation terms. That locality
step is deliberately deferred.
-/

namespace LeanGioia

/-- The W state has zero amplitude on the vacuum configuration. -/
@[simp]
theorem wState_apply_vacuum (N : ℕ) :
    wState N (vacuumBits N) = 0 := by
  classical
  rw [wState_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro j hj
  apply basisState_apply_ne
  exact (singleExcitationBits_ne_vacuum j).symm

/-- Removing the unique excitation from a single-excitation bitstring gives vacuum. -/
theorem setBit_singleExcitation_self_false {N : ℕ} (k : Fin N) :
    setBit (singleExcitationBits k) k false = vacuumBits N := by
  funext x
  by_cases hx : x = k
  · subst x
    simp [setBit, vacuumBits]
  · simp [setBit, singleExcitationBits, vacuumBits, hx]

/--
Any creation string acting on the W state has zero vacuum amplitude.

For the empty string this is just the fact that W has no vacuum component.
For a nonempty string, the outer creation operator itself gives zero on the
vacuum output configuration.
-/
theorem creationString_wState_zero_on_vacuum {N : ℕ} (js : List (Fin N)) :
    creationString js (wState N) (vacuumBits N) = 0 := by
  cases js with
  | nil =>
      simp [creationString]
  | cons j js =>
      simp [creationString, composeOperator, createAt, vacuumBits]

/--
A nonempty pure-creation string has zero amplitude on every one-particle
basis configuration after acting on the W state.
-/
theorem creationString_wState_zero_on_singleExcitation {N : ℕ}
    (j : Fin N) (js : List (Fin N)) (k : Fin N) :
    creationString (j :: js) (wState N) (singleExcitationBits k) = 0 := by
  simp only [creationString, composeOperator_apply]
  by_cases hjk : j = k
  · subst j
    have hbit : singleExcitationBits k k = true := by
      simp [singleExcitationBits]
    simp [createAt, hbit, setBit_singleExcitation_self_false,
      creationString_wState_zero_on_vacuum]
  · have hbit : singleExcitationBits k j = false := by
      simp [singleExcitationBits, hjk]
    simp [createAt, hbit]

/--
For positive system size, a nonempty pure-creation string cannot have the W
state as an eigenstate with a nonzero eigenvalue.

This is a single-string result, not yet the paper's full finite-range
coefficient-cancellation theorem.
-/
theorem pureCreation_not_w_eigenstate_nonzero {N : ℕ}
    (hN : 0 < N) (j : Fin N) (js : List (Fin N)) (eig : ℂ)
    (heig : eig ≠ 0)
    (hW : IsEigenstate (creationString (j :: js)) (wState N) eig) :
    False := by
  let k : Fin N := ⟨0, hN⟩
  have hamp :
      creationString (j :: js) (wState N) (singleExcitationBits k) =
        eig * wState N (singleExcitationBits k) := by
    exact (isEigenstate_iff_amplitudes
      (creationString (j :: js)) (wState N) eig).mp hW (singleExcitationBits k)
  have hleft :
      creationString (j :: js) (wState N) (singleExcitationBits k) = 0 :=
    creationString_wState_zero_on_singleExcitation j js k
  have hwcoeff :
      wState N (singleExcitationBits k) = wCoefficient N := by
    classical
    rw [wState_apply]
    have hsum :
        (∑ q : Fin N, singleExcitationState q (singleExcitationBits k)) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp
      · intro q hq hqk
        exact singleExcitationState_apply_other hqk
      · simp
    rw [hsum, mul_one]
  rw [hleft, hwcoeff] at hamp
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by
    positivity
  have hcoeff : wCoefficient N ≠ 0 := by
    simp [wCoefficient, hsqrt]
  have hz : eig * wCoefficient N = 0 := hamp.symm
  exact heig (mul_eq_zero.mp hz |>.resolve_right hcoeff)

end LeanGioia
