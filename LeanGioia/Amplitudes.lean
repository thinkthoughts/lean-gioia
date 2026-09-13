import LeanGioia.SupportWitness

/-!
# LeanGioia.Amplitudes

Checkpoint 8: explicit pure-creation amplitudes.

Appendix C.1.a treats the single-creation case separately. For distinct
sites `j` and `l`, the term `s†_j` acting on the W state contributes to the
two-particle basis configuration with occupations at `{j,l}`. At that same
configuration, a different single-site creation operator can contribute
only if it creates at `l`.

This checkpoint formalizes that amplitude pattern directly.
-/

namespace LeanGioia

/-- Two-particle computational-basis configuration with sites `j` and `l` occupied. -/
def twoExcitationBits {N : ℕ} (j l : Fin N) : Bitstring N :=
  occupiedBits ({j, l} : Finset (Fin N))

@[simp]
theorem twoExcitationBits_left {N : ℕ} (j l : Fin N) :
    twoExcitationBits j l j = true := by
  simp [twoExcitationBits, occupiedBits]

@[simp]
theorem twoExcitationBits_right {N : ℕ} (j l : Fin N) :
    twoExcitationBits j l l = true := by
  simp [twoExcitationBits, occupiedBits]

/--
Removing the occupation at `j` from the `{j,l}` configuration leaves the
single excitation at `l`, provided `j ≠ l`.
-/
theorem setBit_twoExcitation_left_false {N : ℕ} {j l : Fin N}
    (hjl : j ≠ l) :
    setBit (twoExcitationBits j l) j false = singleExcitationBits l := by
  funext x
  by_cases hxj : x = j
  · subst x
    simp [setBit, twoExcitationBits, singleExcitationBits, hjl]
  · by_cases hxl : x = l
    · subst x
      simp [setBit, twoExcitationBits, occupiedBits, singleExcitationBits, hxj]
    · simp [setBit, twoExcitationBits, occupiedBits, singleExcitationBits,
        hxj, hxl]

/--
The W amplitude on a single-excitation basis configuration is exactly the
normalization coefficient.
-/
theorem wState_apply_singleExcitation {N : ℕ} (l : Fin N) :
    wState N (singleExcitationBits l) = wCoefficient N := by
  classical
  rw [wState_apply]
  have hsum :
      (∑ q : Fin N, singleExcitationState q (singleExcitationBits l)) = 1 := by
    rw [Finset.sum_eq_single l]
    · simp
    · intro q hq hql
      exact singleExcitationState_apply_other hql
    · simp
  rw [hsum, mul_one]

/--
Selected-term amplitude for the single-creation case:

for `j ≠ l`, creating at `j` from the W state has amplitude
`wCoefficient N` on the two-particle configuration `{j,l}`.
-/
theorem createAt_wState_twoExcitation {N : ℕ}
    {j l : Fin N} (hjl : j ≠ l) :
    createAt j (wState N) (twoExcitationBits j l) = wCoefficient N := by
  change
    (if twoExcitationBits j l j = true
      then wState N (setBit (twoExcitationBits j l) j false)
      else 0) = wCoefficient N
  rw [if_pos (twoExcitationBits_left j l)]
  rw [setBit_twoExcitation_left_false hjl]
  exact wState_apply_singleExcitation l

/--
A third single-site creation operator cannot contribute to the `{j,l}`
amplitude unless it acts at `j` or `l`.
-/
theorem createAt_wState_twoExcitation_other {N : ℕ}
    {j l k : Fin N} (hkj : k ≠ j) (hkl : k ≠ l) :
    createAt k (wState N) (twoExcitationBits j l) = 0 := by
  change
    (if twoExcitationBits j l k = true
      then wState N (setBit (twoExcitationBits j l) k false)
      else 0) = 0
  have hbit : twoExcitationBits j l k = false := by
    simp [twoExcitationBits, occupiedBits, hkj, hkl]
  rw [if_neg]
  simpa using hbit

/--
At the `{j,l}` witness, among single-site creation operators only the
operators at `j` and `l` can contribute.
-/
theorem singleCreation_competitor_restricted {N : ℕ}
    {j l k : Fin N} (hk : k ≠ j ∧ k ≠ l) :
    createAt k (wState N) (twoExcitationBits j l) = 0 :=
  createAt_wState_twoExcitation_other hk.1 hk.2

end LeanGioia
