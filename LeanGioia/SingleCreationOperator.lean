import LeanGioia.SingleCreation

/-!
# LeanGioia.SingleCreationOperator

Checkpoint 11: derive the three witness equations from an explicit
single-creation operator and the W-eigenstate condition.

For coefficients `c : Fin N → ℂ`, define

`G_c = ∑ j, c j • s†_j`.

Checkpoint 8 showed that at a two-particle basis configuration `{j,l}`,
only the creation operators at `j` and `l` contribute. Therefore, if
`G_c |W⟩ = eig |W⟩`, then the W amplitude at `{j,l}` vanishes and the
coefficient equation

`(c j + c l) * wCoefficient N = 0`

follows.

This file packages that calculation and constructs the
`ThreeSiteWitnessEquations` required by Checkpoint 10.
-/

namespace LeanGioia

/-- The explicit single-creation operator `G_c = ∑ j, c j • createAt j`. -/
noncomputable def singleCreationOperator {N : ℕ}
    (c : Fin N → ℂ) : Operator N :=
  ∑ j : Fin N, c j • createAt j

/--
For distinct `j` and `l`, the two-particle configuration `{j,l}` differs
from every single-excitation configuration.
-/
theorem twoExcitationBits_ne_singleExcitation {N : ℕ}
    {j l q : Fin N} (hjl : j ≠ l) :
    twoExcitationBits j l ≠ singleExcitationBits q := by
  intro hEq
  by_cases hqj : q = j
  · subst q
    have hAtL := congrFun hEq l
    have hleft : twoExcitationBits j l l = true := by
      simp
    rw [hleft] at hAtL
    simp [singleExcitationBits, hjl.symm] at hAtL
  · have hAtJ := congrFun hEq j
    have hleft : twoExcitationBits j l j = true := by
      simp
    rw [hleft] at hAtJ
    have hjq : j = q := by
      simpa [singleExcitationBits] using hAtJ
    exact hqj hjq.symm

/--
A two-particle basis configuration has zero W-state amplitude when its two
sites are distinct.
-/
theorem wState_twoExcitation_zero {N : ℕ}
    {j l : Fin N} (hjl : j ≠ l) :
    wState N (twoExcitationBits j l) = 0 := by
  classical
  rw [wState_apply]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro q hq
  apply basisState_apply_ne
  exact twoExcitationBits_ne_singleExcitation hjl

/--
Action of the explicit single-creation operator on the `{j,l}` witness.

For distinct `j` and `l`, only the terms at `j` and `l` survive.
-/
theorem singleCreationOperator_twoExcitation {N : ℕ}
    (c : Fin N → ℂ) {j l : Fin N} (hjl : j ≠ l) :
    singleCreationOperator c (wState N) (twoExcitationBits j l) =
      (c j + c l) * wCoefficient N := by
  classical
  rw [singleCreationOperator]
  simp only [Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  have hsplit :
      (∑ x : Fin N,
        c x * createAt x (wState N) (twoExcitationBits j l)) =
        (∑ x : Fin N, if x = j then c j * wCoefficient N else 0) +
        (∑ x : Fin N, if x = l then c l * wCoefficient N else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    by_cases hxj : x = j
    · subst x
      simp [hjl, createAt_wState_twoExcitation hjl]
    · by_cases hxl : x = l
      · subst x
        have hlj : l ≠ j := Ne.symm hjl
        have hamp :
            createAt l (wState N) (twoExcitationBits j l) =
              wCoefficient N := by
          simpa [twoExcitationBits, Finset.pair_comm] using
            (createAt_wState_twoExcitation hlj :
              createAt l (wState N) (twoExcitationBits l j) =
                wCoefficient N)
        simp [hxj, hamp]
      · simp [hxj, hxl,
          createAt_wState_twoExcitation_other hxj hxl]
  rw [hsplit]
  simp
  ring

/--
The W-eigenstate equation forces the pair witness equation at every pair of
distinct sites.
-/
theorem pair_witness_equation_of_eigenstate {N : ℕ}
    (c : Fin N → ℂ) (eig : ℂ)
    (hEig : IsEigenstate (singleCreationOperator c) (wState N) eig)
    {j l : Fin N} (hjl : j ≠ l) :
    (c j + c l) * wCoefficient N = 0 := by
  have hAmp :
      singleCreationOperator c (wState N) (twoExcitationBits j l) =
        eig * wState N (twoExcitationBits j l) :=
    (isEigenstate_iff_amplitudes
      (singleCreationOperator c) (wState N) eig).mp hEig
      (twoExcitationBits j l)
  rw [singleCreationOperator_twoExcitation c hjl,
      wState_twoExcitation_zero hjl, mul_zero] at hAmp
  exact hAmp

/--
From an explicit single-creation operator and three pairwise distinct sites,
the W-eigenstate condition produces the three witness equations used in
Checkpoint 10.
-/
theorem threeSiteWitnessEquations_of_eigenstate {N : ℕ}
    (c : Fin N → ℂ) (eig : ℂ)
    (hEig : IsEigenstate (singleCreationOperator c) (wState N) eig)
    {j l p : Fin N}
    (hjl : j ≠ l) (hjp : j ≠ p) (hlp : l ≠ p) :
    ThreeSiteWitnessEquations c j l p where
  jl := pair_witness_equation_of_eigenstate c eig hEig hjl
  jp := pair_witness_equation_of_eigenstate c eig hEig hjp
  lp := pair_witness_equation_of_eigenstate c eig hEig hlp

/--
End-to-end selected-coefficient conclusion for the explicit
single-creation operator.
-/
theorem single_creation_coefficient_zero_of_eigenstate {N : ℕ}
    (hN : 0 < N) (c : Fin N → ℂ) (eig : ℂ)
    (hEig : IsEigenstate (singleCreationOperator c) (wState N) eig)
    {j l p : Fin N}
    (hjl : j ≠ l) (hjp : j ≠ p) (hlp : l ≠ p) :
    c j = 0 := by
  apply single_creation_coefficient_zero hN c j l p
  exact threeSiteWitnessEquations_of_eigenstate
    c eig hEig hjl hjp hlp

end LeanGioia
