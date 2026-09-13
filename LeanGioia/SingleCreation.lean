import LeanGioia.ThreeSite

/-!
# LeanGioia.SingleCreation

Checkpoint 10: assembly of the `n = 1, m = 0` coefficient obstruction.

Appendix C.1.a shows that a single-creation coefficient `c_j` cannot remain
nonzero in an extensive-local operator having the W state as an eigenstate.
The source argument uses three sufficiently separated sites `j`, `l`, and
`p`, together with the three two-particle witness amplitudes.

Checkpoints 8 and 9 formalized the amplitude support and the three-site
coefficient algebra. This file packages those results into the paper-level
single-creation coefficient conclusion, while keeping the remaining
locality-to-amplitude derivation explicit as a hypothesis.
-/

namespace LeanGioia

/--
The three scaled two-particle witness equations needed for a selected site
`j`.
-/
structure ThreeSiteWitnessEquations {N : ℕ}
    (c : Fin N → ℂ) (j l p : Fin N) : Prop where
  jl : (c j + c l) * wCoefficient N = 0
  jp : (c j + c p) * wCoefficient N = 0
  lp : (c l + c p) * wCoefficient N = 0

/--
Once the three witness-amplitude equations have been obtained from locality
and the W-eigenstate condition, the selected coefficient must vanish.
-/
theorem single_creation_coefficient_zero {N : ℕ}
    (hN : 0 < N) (c : Fin N → ℂ) (j l p : Fin N)
    (h : ThreeSiteWitnessEquations c j l p) :
    c j = 0 := by
  exact three_site_scaled_amplitudes_force_zero
    hN c j l p h.jl h.jp h.lp

/--
If every site admits two auxiliary sites satisfying the three witness
equations, then every single-creation coefficient vanishes.
-/
theorem all_single_creation_coefficients_zero {N : ℕ}
    (hN : 0 < N) (c : Fin N → ℂ)
    (hwitness :
      ∀ j : Fin N,
        ∃ l p : Fin N, ThreeSiteWitnessEquations c j l p) :
    ∀ j : Fin N, c j = 0 := by
  intro j
  obtain ⟨l, p, h⟩ := hwitness j
  exact single_creation_coefficient_zero hN c j l p h

/--
Equivalent function-level statement.
-/
theorem single_creation_coefficients_eq_zero {N : ℕ}
    (hN : 0 < N) (c : Fin N → ℂ)
    (hwitness :
      ∀ j : Fin N,
        ∃ l p : Fin N, ThreeSiteWitnessEquations c j l p) :
    c = 0 := by
  funext j
  exact all_single_creation_coefficients_zero hN c hwitness j

/--
Paper-facing predicate for the single-creation sector.
-/
def SingleCreationForbidden {N : ℕ} (c : Fin N → ℂ) : Prop :=
  ∀ j : Fin N, c j = 0

/--
Checkpoint-10 paper-facing conclusion.
-/
theorem single_creation_forbidden_of_three_site_witnesses {N : ℕ}
    (hN : 0 < N) (c : Fin N → ℂ)
    (hwitness :
      ∀ j : Fin N,
        ∃ l p : Fin N, ThreeSiteWitnessEquations c j l p) :
    SingleCreationForbidden c := by
  exact all_single_creation_coefficients_zero hN c hwitness

end LeanGioia
