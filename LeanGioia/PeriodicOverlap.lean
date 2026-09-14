import LeanGioia.PeriodicRange

/-!
# LeanGioia.PeriodicOverlap

Checkpoint 24: remove the remaining overlap-localization assumption.

A `3R` interaction block beginning at the same left endpoint as the
selected range-`R` block does not, in general, contain every overlapping
range-`R` block: a competitor may begin to the left.

We therefore define the exact periodic overlap hull.  This makes the
locality implication a theorem rather than a model field.
-/

namespace LeanGioia

/--
The exact periodic interaction hull of the selected range-`R` block.
-/
def overlapInteraction
    (N R : Nat) (selectedStart : Fin N) : Finset (Fin N) :=
  Finset.univ.filter fun x =>
    ∃ competitorStart : Fin N,
      ¬ Disjoint
        (cyclicBlock N R competitorStart)
        (cyclicBlock N R selectedStart) ∧
      x ∈ cyclicBlock N R competitorStart

/--
Every selected-block site lies in its overlap interaction hull.
-/
theorem cyclicBlock_subset_overlapInteraction
    {N R : Nat} (selectedStart : Fin N) :
    cyclicBlock N R selectedStart ⊆
      overlapInteraction N R selectedStart := by
  intro x hx
  simp only [overlapInteraction, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨selectedStart, ?_, hx⟩
  intro hdis
  exact (Finset.disjoint_left.mp hdis) hx hx

/--
Any overlapping range-`R` cyclic block is contained in the exact overlap
interaction hull.
-/
theorem cyclicBlock_subset_overlapInteraction_of_overlap
    {N R : Nat} {selectedStart competitorStart : Fin N}
    (hoverlap :
      ¬ Disjoint
        (cyclicBlock N R competitorStart)
        (cyclicBlock N R selectedStart)) :
    cyclicBlock N R competitorStart ⊆
      overlapInteraction N R selectedStart := by
  intro x hx
  simp only [overlapInteraction, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨competitorStart, hoverlap, hx⟩

/--
Periodic range data with overlap localization derived automatically.

The sole remaining geometric input is that the exact overlap hull leaves
at least one site outside it.
-/
structure PeriodicOverlapCreationModel
    (N R : Nat) (ι : Type) [Fintype ι]
    (creators : ι → List (Fin N)) where
  start : ι → Fin N

  creators_in_support :
    ∀ i : ι,
      (creators i).toFinset ⊆ cyclicBlock N R (start i)

  interaction_card_lt :
    ∀ i : ι,
      (overlapInteraction N R (start i)).card < N

/--
The exact periodic-overlap model supplies the abstract finite-range model
from Checkpoint 22 without an `overlap_localizes` assumption.
-/
noncomputable def PeriodicOverlapCreationModel.toFiniteRange
    {N R : Nat} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : PeriodicOverlapCreationModel N R ι creators) :
    FiniteRangeCreationModel N ι creators where
  support := fun i =>
    cyclicBlock N R (M.start i)

  interaction := fun i =>
    overlapInteraction N R (M.start i)

  creators_subset := by
    intro i
    exact M.creators_in_support i

  selected_subset_interaction := by
    intro i
    exact cyclicBlock_subset_overlapInteraction (M.start i)

  overlap_support_subset_interaction := by
    intro i k hoverlap
    exact cyclicBlock_subset_overlapInteraction_of_overlap hoverlap

  interaction_card_lt := by
    intro i
    exact M.interaction_card_lt i

/--
Generate all higher-creation witness data from exact periodic-overlap
geometry.
-/
noncomputable def all_higherCreationWitnessData_of_periodicOverlap
    {N R : Nat} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (M : PeriodicOverlapCreationModel N R ι creators)
    (hatLeastTwo :
      ∀ i : ι, 2 ≤ (creators i).toFinset.card)
    (hNodup :
      ∀ i : ι, (creators i).Nodup) :
    ∀ i : ι, HigherCreationWitnessData creators i :=
  all_higherCreationWitnessData_of_finiteRange
    M.toFiniteRange
    hatLeastTwo
    hNodup

/--
Checkpoint-24 end-to-end Corollary-1 assembly.

The overlap-localization implication is now derived directly from the
exact periodic interaction hull.
-/
theorem corollary_one_from_periodicOverlap_creation_model
    {N R : Nat} {ι κ : Type}
    [Fintype ι]
    [Fintype κ] [DecidableEq κ]
    (hN3 : 3 ≤ N)
    (Ω : ℂ)
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (hnonid : NonidentityNormalOrderedFamily term)
    (singleCoeff : Fin N → ℂ)
    (singleEig : ℂ)
    (hSingleEig :
      IsEigenstate
        (singleCreationOperator singleCoeff)
        (wState N) singleEig)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (higherEig : ℂ)
    (hHigherEig :
      IsEigenstate
        (higherCreationFamilyOperator higherCoeff higherCreators)
        (wState N) higherEig)
    (hinj :
      Function.Injective
        (fun k : κ => (higherCreators k).toFinset))
    (M :
      PeriodicOverlapCreationModel
        N R κ higherCreators)
    (hatLeastTwo :
      ∀ k : κ,
        2 ≤ (higherCreators k).toFinset.card)
    (hNodup :
      ∀ k : κ,
        (higherCreators k).Nodup)
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by
  exact corollary_one_from_finiteRange_creation_model
    hN3 Ω
    mixedCoeff term hnonid
    singleCoeff singleEig hSingleEig
    higherCoeff higherCreators higherEig hHigherEig
    hinj
    M.toFiniteRange
    hatLeastTwo hNodup
    hbridge

end LeanGioia
