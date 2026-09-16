import LeanGioia.HigherCreationSupportAggregation

/-!
# LeanGioia.HigherCreationAggregateZero

Checkpoint 50: replace external-index coefficient isolation by
creator-support aggregate coefficient isolation.

The existing higher-creation proof uses locality to show that any family term
with nonzero amplitude on the selected witness has the same finite creator
support as the selected term. It then uses injectivity of the external support
map to conclude that the competing index equals the selected index.

CP47--49 make that final injectivity step unnecessary:
* CP47 defines support fibers and aggregate coefficients;
* CP48 proves equal duplicate-free support gives equal `creationString`;
* CP49 aggregates operator contributions inside one support fiber.

CP50 isolates the whole selected support fiber. Terms outside the fiber have
zero amplitude on the selected witness by locality. Terms inside the fiber
combine into the support aggregate coefficient. The W-eigenstate equation
then forces that aggregate coefficient to vanish.

The conclusion is aggregate coefficient zero, not per-external-index
coefficient zero.
-/

namespace LeanGioia

/-- A term outside the selected creator-support fiber has zero amplitude on
the selected higher-creation witness. -/
theorem higherCreation_amplitude_zero_of_not_mem_supportFiber
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (creators : ι → List (Fin N))
    (i₀ i : ι) (l : Fin N)
    (hcard : 2 ≤ (creators i₀).toFinset.card)
    (hl : l ∉ creators i₀)
    (hlocal :
      ∀ i : ι,
        SeparatedLocalCompetitor
          (creators i₀).toFinset l (creators i).toFinset)
    (hout :
      i ∉ higherCreationSupportFiber creators (creators i₀).toFinset) :
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
  have hin :
      i ∈ higherCreationSupportFiber creators (creators i₀).toFinset := by
    simpa [higherCreationSupportFiber] using hsets
  exact hout hin

/-- At the selected witness, the full family reduces to the aggregate
coefficient of the selected support times one representative amplitude. -/
theorem higherCreationFamilyOperator_selected_witness_aggregate
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (coeff : ι → ℂ)
    (creators : ι → List (Fin N))
    (hNodup : ∀ i : ι, (creators i).Nodup)
    (i₀ : ι) (l : Fin N)
    (hcard : 2 ≤ (creators i₀).toFinset.card)
    (hl : l ∉ creators i₀)
    (hlocal :
      ∀ i : ι,
        SeparatedLocalCompetitor
          (creators i₀).toFinset l (creators i).toFinset) :
    higherCreationFamilyOperator coeff creators (wState N)
        (higherCreationWitnessBits (creators i₀) l) =
      higherCreationAggregateCoeff
          coeff creators (creators i₀).toFinset *
        creationString (creators i₀) (wState N)
          (higherCreationWitnessBits (creators i₀) l) := by
  classical
  rw [higherCreationFamilyOperator]
  simp only [Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [← Finset.sum_filter]
  · calc
      (∑ i ∈ higherCreationSupportFiber creators (creators i₀).toFinset,
          coeff i *
            creationString (creators i) (wState N)
              (higherCreationWitnessBits (creators i₀) l)) =
        (∑ i ∈ higherCreationSupportFiber creators (creators i₀).toFinset,
            coeff i) *
          creationString (creators i₀) (wState N)
            (higherCreationWitnessBits (creators i₀) l) := by
              rw [Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              rw [creationString_eq_of_mem_higherCreationSupportFiber
                creators hNodup i₀ i hi]
      _ =
        higherCreationAggregateCoeff
            coeff creators (creators i₀).toFinset *
          creationString (creators i₀) (wState N)
            (higherCreationWitnessBits (creators i₀) l) := by
              rfl
  · intro i hi
    rw [higherCreation_amplitude_zero_of_not_mem_supportFiber
      creators i₀ i l hcard hl hlocal hi, mul_zero]

/-- CP50: the aggregate coefficient of the selected creator support vanishes
under the W-eigenstate and selected-witness hypotheses, without support-map
injectivity. -/
theorem higherCreation_aggregate_coefficient_zero_of_eigenstate
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 0 < N)
    (coeff : ι → ℂ)
    (creators : ι → List (Fin N))
    (eig : ℂ)
    (hEig :
      IsEigenstate
        (higherCreationFamilyOperator coeff creators)
        (wState N) eig)
    (hNodup : ∀ i : ι, (creators i).Nodup)
    (i₀ : ι) (l : Fin N)
    (hcard : 2 ≤ (creators i₀).toFinset.card)
    (hl : l ∉ creators i₀)
    (hlocal :
      ∀ i : ι,
        SeparatedLocalCompetitor
          (creators i₀).toFinset l (creators i).toFinset) :
    higherCreationAggregateCoeff
      coeff creators (creators i₀).toFinset = 0 := by
  let b := higherCreationWitnessBits (creators i₀) l
  have hAmp :
      higherCreationFamilyOperator coeff creators (wState N) b =
        eig * wState N b :=
    (isEigenstate_iff_amplitudes
      (higherCreationFamilyOperator coeff creators)
      (wState N) eig).mp hEig b
  have hfamily :
      higherCreationFamilyOperator coeff creators (wState N) b =
        higherCreationAggregateCoeff
            coeff creators (creators i₀).toFinset *
          creationString (creators i₀) (wState N) b := by
    simpa [b] using
      higherCreationFamilyOperator_selected_witness_aggregate
        coeff creators hNodup i₀ l hcard hl hlocal
  have hW : wState N b = 0 := by
    simpa [b] using
      selected_higherCreation_witness_wState_zero
        creators i₀ l hcard (hNodup i₀) hl
  have htarget :
      creationString (creators i₀) (wState N) b ≠ 0 := by
    simpa [b] using
      creationString_higherCreationWitness_nonzero
        hN (creators i₀) l (hNodup i₀) hl
  rw [hfamily, hW, mul_zero] at hAmp
  exact (mul_eq_zero.mp hAmp).resolve_right htarget

/-- Family-level CP50 conclusion for every creator support represented by the
external family. -/
theorem all_higherCreation_aggregate_coefficients_zero_of_eigenstate
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 0 < N)
    (coeff : ι → ℂ)
    (creators : ι → List (Fin N))
    (eig : ℂ)
    (hEig :
      IsEigenstate
        (higherCreationFamilyOperator coeff creators)
        (wState N) eig)
    (hNodup : ∀ i : ι, (creators i).Nodup)
    (hwitness :
      ∀ i : ι, HigherCreationWitnessData creators i) :
    ∀ i : ι,
      higherCreationAggregateCoeff
        coeff creators (creators i).toFinset = 0 := by
  intro i
  let w := hwitness i
  exact higherCreation_aggregate_coefficient_zero_of_eigenstate
    hN coeff creators eig hEig hNodup
    i w.witnessSite
    w.atLeastTwo
    w.witnessOutside
    w.locality

end LeanGioia
