import LeanGioia.HigherCreationContribution

/-!
# LeanGioia.HigherCreationComplete

Checkpoint 16: assemble the `n ≥ 2, m = 0` coefficient obstruction.

For a finite family of pure-creation strings, select one term `i₀` with
creator set `A` of cardinality at least two and choose a distant witness
site `l`.

Checkpoints 13–15 give:

* the selected term has nonzero amplitude on the witness `A ∪ {l}`;
* any competing term with nonzero amplitude on that witness determines a
  representation of the same witness set;
* locality uniqueness forces that competitor to have the same creator set.

If creator sets label the family injectively, every other family member has
zero amplitude on the selected witness.  The W-eigenstate equation then
forces the selected coefficient to vanish.
-/

namespace LeanGioia

/-- A finite linear combination of pure-creation strings. -/
noncomputable def higherCreationFamilyOperator
    {N : ℕ} {ι : Type} [Fintype ι]
    (coeff : ι → ℂ) (creators : ι → List (Fin N)) :
    Operator N :=
  ∑ i : ι, coeff i • creationString (creators i)

/--
At the selected higher-particle witness, every competing family member with
a different index has zero amplitude, provided locality uniqueness applies
and creator sets identify family members injectively.
-/
theorem competing_higherCreation_amplitude_zero
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (creators : ι → List (Fin N))
    (i₀ i : ι) (l : Fin N)
    (hcard : 2 ≤ (creators i₀).toFinset.card)
    (hl : l ∉ creators i₀)
    (hlocal :
      ∀ i : ι,
        SeparatedLocalCompetitor
          (creators i₀).toFinset l (creators i).toFinset)
    (hinj :
      Function.Injective (fun i : ι => (creators i).toFinset))
    (hne : i ≠ i₀) :
    creationString (creators i) (wState N)
      (higherCreationWitnessBits (creators i₀) l) = 0 := by
  by_contra hnonzero
  obtain ⟨q, hrep⟩ :=
    creationString_nonzero_represents_higherCreationWitness
      (creators i₀) (creators i) l hnonzero
  have hsets :
      (creators i).toFinset = (creators i₀).toFinset :=
    higherCreationWitness_creatorSet_unique
      (creators i₀).toFinset
      (creators i).toFinset
      l q
      hcard
      (by simpa using hl)
      (hlocal i)
      hrep
  exact hne (hinj hsets)

/--
The finite family acts on the selected witness exactly as its selected term.
-/
theorem higherCreationFamilyOperator_selected_witness
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (coeff : ι → ℂ) (creators : ι → List (Fin N))
    (i₀ : ι) (l : Fin N)
    (hcard : 2 ≤ (creators i₀).toFinset.card)
    (hl : l ∉ creators i₀)
    (hlocal :
      ∀ i : ι,
        SeparatedLocalCompetitor
          (creators i₀).toFinset l (creators i).toFinset)
    (hinj :
      Function.Injective (fun i : ι => (creators i).toFinset)) :
    higherCreationFamilyOperator coeff creators (wState N)
      (higherCreationWitnessBits (creators i₀) l) =
      coeff i₀ *
        creationString (creators i₀) (wState N)
          (higherCreationWitnessBits (creators i₀) l) := by
  classical
  rw [higherCreationFamilyOperator]
  simp only [Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i₀]
  · rfl
  · intro i hi hne
    rw [competing_higherCreation_amplitude_zero
      creators i₀ i l hcard hl hlocal hinj hne, mul_zero]
  · simp

/--
The selected higher-creation witness lies outside the W sector.
-/
theorem selected_higherCreation_witness_wState_zero
    {N : ℕ} {ι : Type}
    (creators : ι → List (Fin N))
    (i₀ : ι) (l : Fin N)
    (hcard : 2 ≤ (creators i₀).toFinset.card)
    (hnodup : (creators i₀).Nodup)
    (hl : l ∉ creators i₀) :
    wState N (higherCreationWitnessBits (creators i₀) l) = 0 := by
  cases hjs : creators i₀ with
  | nil =>
      rw [hjs] at hcard
      simp at hcard
  | cons j js =>
      rw [hjs] at hnodup hl
      simpa [hjs] using
        (wState_higherCreationWitness_zero
          (j := j) (js := js) (l := l) hnodup hl)

/--
Checkpoint-16 assembly theorem.

In a finite pure-creation family whose creator sets are unique labels, if a
selected term has at least two distinct creator sites, admits a separated
witness site, and the W state is an eigenstate of the family operator, then
the selected coefficient is zero.
-/
theorem higher_creation_coefficient_zero_of_eigenstate
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 0 < N)
    (coeff : ι → ℂ) (creators : ι → List (Fin N))
    (eig : ℂ)
    (hEig :
      IsEigenstate
        (higherCreationFamilyOperator coeff creators)
        (wState N) eig)
    (i₀ : ι) (l : Fin N)
    (hcard : 2 ≤ (creators i₀).toFinset.card)
    (hnodup : (creators i₀).Nodup)
    (hl : l ∉ creators i₀)
    (hlocal :
      ∀ i : ι,
        SeparatedLocalCompetitor
          (creators i₀).toFinset l (creators i).toFinset)
    (hinj :
      Function.Injective (fun i : ι => (creators i).toFinset)) :
    coeff i₀ = 0 := by
  let b := higherCreationWitnessBits (creators i₀) l
  have hAmp :
      higherCreationFamilyOperator coeff creators (wState N) b =
        eig * wState N b :=
    (isEigenstate_iff_amplitudes
      (higherCreationFamilyOperator coeff creators)
      (wState N) eig).mp hEig b
  have hfamily :
      higherCreationFamilyOperator coeff creators (wState N) b =
        coeff i₀ * creationString (creators i₀) (wState N) b := by
    simpa [b] using
      higherCreationFamilyOperator_selected_witness
        coeff creators i₀ l hcard hl hlocal hinj
  have hW : wState N b = 0 := by
    simpa [b] using
      selected_higherCreation_witness_wState_zero
        creators i₀ l hcard hnodup hl
  have htarget :
      creationString (creators i₀) (wState N) b ≠ 0 := by
    simpa [b] using
      creationString_higherCreationWitness_nonzero
        hN (creators i₀) l hnodup hl
  rw [hfamily, hW, mul_zero] at hAmp
  exact (mul_eq_zero.mp hAmp).resolve_right htarget

end LeanGioia
