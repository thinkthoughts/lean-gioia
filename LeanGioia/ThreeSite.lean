import LeanGioia.Amplitudes

/-!
# LeanGioia.ThreeSite

Checkpoint 9: the three-site consistency argument from Appendix C.1.a.

For the `n = 1, m = 0` pure-creation sector, the source paper argues as
follows.  Starting from a coefficient `c_j`, cancellation of the
two-particle amplitude on `{j,l}` requires a compensating coefficient at
`l`; cancellation on `{j,p}` requires a corresponding coefficient at `p`.
But then the `{l,p}` amplitude must also cancel.  The three pairwise
conditions force the original coefficient to vanish.

Checkpoint 8 formalized the pair-amplitude support statement.  This file
formalizes the coefficient-consistency step itself.
-/

namespace LeanGioia

/--
Pairwise cancellation condition for single-site creation coefficients.

At a two-particle witness `{a,b}`, Checkpoint 8 shows that among
single-site creation terms only the terms at `a` and `b` contribute.
After factoring out the common nonzero W-state normalization coefficient,
vanishing of that witness amplitude gives `c a + c b = 0`.
-/
def PairCancellation {N : ℕ} (c : Fin N → ℂ) (a b : Fin N) : Prop :=
  c a + c b = 0

/--
The three-site consistency obstruction.

If the `{j,l}`, `{j,p}`, and `{l,p}` two-particle witness amplitudes all
cancel, then the coefficient at `j` must vanish.
-/
theorem three_site_consistency_forces_zero {N : ℕ}
    (c : Fin N → ℂ) (j l p : Fin N)
    (hjl : PairCancellation c j l)
    (hjp : PairCancellation c j p)
    (hlp : PairCancellation c l p) :
    c j = 0 := by
  have hsum : (2 : ℂ) * c j = 0 := by
    calc
      (2 : ℂ) * c j =
          (c j + c l) + (c j + c p) - (c l + c p) := by
            ring
      _ = 0 := by
        rw [show c j + c l = 0 from hjl,
            show c j + c p = 0 from hjp,
            show c l + c p = 0 from hlp]
        ring
  have htwo : (2 : ℂ) ≠ 0 := by
    norm_num
  exact (mul_eq_zero.mp hsum).resolve_left htwo

/--
Under the same three pairwise cancellation conditions, all three
coefficients vanish.
-/
theorem three_site_consistency_forces_all_zero {N : ℕ}
    (c : Fin N → ℂ) (j l p : Fin N)
    (hjl : PairCancellation c j l)
    (hjp : PairCancellation c j p)
    (hlp : PairCancellation c l p) :
    c j = 0 ∧ c l = 0 ∧ c p = 0 := by
  have hj : c j = 0 :=
    three_site_consistency_forces_zero c j l p hjl hjp hlp
  have hl : c l = 0 := by
    have h := hjl
    rw [PairCancellation, hj, zero_add] at h
    exact h
  have hp : c p = 0 := by
    have h := hjp
    rw [PairCancellation, hj, zero_add] at h
    exact h
  exact ⟨hj, hl, hp⟩

/--
Amplitude form of the pair-cancellation condition.

For positive system size the W normalization coefficient is nonzero, so if
`(c a + c b) * wCoefficient N = 0`, then the pair coefficients must cancel.
-/
theorem pairCancellation_of_scaled_amplitude_zero {N : ℕ}
    (hN : 0 < N) (c : Fin N → ℂ) (a b : Fin N)
    (hamp : (c a + c b) * wCoefficient N = 0) :
    PairCancellation c a b := by
  have hsqrt : Real.sqrt (N : ℝ) ≠ 0 := by
    positivity
  have hcoeff : wCoefficient N ≠ 0 := by
    simp [wCoefficient, hsqrt]
  exact (mul_eq_zero.mp hamp).resolve_right hcoeff

/--
Paper-style three-site conclusion stated from the three scaled witness
amplitude equations.
-/
theorem three_site_scaled_amplitudes_force_zero {N : ℕ}
    (hN : 0 < N) (c : Fin N → ℂ) (j l p : Fin N)
    (hjl : (c j + c l) * wCoefficient N = 0)
    (hjp : (c j + c p) * wCoefficient N = 0)
    (hlp : (c l + c p) * wCoefficient N = 0) :
    c j = 0 := by
  apply three_site_consistency_forces_zero c j l p
  · exact pairCancellation_of_scaled_amplitude_zero hN c j l hjl
  · exact pairCancellation_of_scaled_amplitude_zero hN c j p hjp
  · exact pairCancellation_of_scaled_amplitude_zero hN c l p hlp

end LeanGioia
