import LeanGioia.LocalOperators

/-!
# LeanGioia.PureCreation

Checkpoint 4: the algebraic core of Appendix C.1.a.

The full paper argument also uses finite-range spatial separation to rule
out cancellation among distinct local pure-creation terms.  That locality
step is deliberately deferred.
-/

namespace LeanGioia

/--
A nonempty pure-creation string has zero amplitude on every one-particle
basis configuration after acting on the W state.

Reason: the outermost creation operator either tries to create on the
already occupied site (giving zero) or requires an input configuration with
zero particles, while the W state has support only on one-particle basis
configurations.
-/
theorem creationString_wState_zero_on_singleExcitation {N : ℕ}
    (j : Fin N) (js : List (Fin N)) (k : Fin N) :
    creationString (j :: js) (wState N) (singleExcitationBits k) = 0 := by
  simp only [creationString, composeOperator_apply]
  by_cases hjk : j = k
  · subst j
    simp [createAt, singleExcitationBits]
  · have hfalse : (singleExcitationBits k) j = false := by
      simp [singleExcitationBits, hjk]
    simp [createAt, hfalse, setBit, wState_apply, singleExcitationState,
      basisState, singleExcitationBits, vacuumBits]

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
  have hamp := congrFun hW (singleExcitationBits k)
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
  rw [hleft] at hamp
  simp only [Pi.smul_apply, smul_eq_mul] at hamp
  rw [hwcoeff] at hamp
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by
    positivity
  have hcoeff : wCoefficient N ≠ 0 := by
    simp [wCoefficient, hsqrt]
  have hz : eig * wCoefficient N = 0 := hamp.symm
  exact heig (mul_eq_zero.mp hz |>.resolve_right hcoeff)

end LeanGioia
