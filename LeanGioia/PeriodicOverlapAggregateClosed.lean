import LeanGioia.PureCreationAggregateRepresentation
import LeanGioia.PeriodicOverlapReduced

/-!
# LeanGioia.PeriodicOverlapAggregateClosed

Checkpoint 52: final reduced periodic-overlap assembly.

This file closes the CP47--CP51 support-aggregate route against the existing
closed periodic-overlap geometry. No creator-support injectivity hypothesis
occurs in the final theorem.
-/

namespace LeanGioia

/--
Every higher pure-creation mixed term has support represented by the external
higher-creation family. This is coverage, not injectivity.
-/
def HigherCreationMixedSupportCovered
    {N : Nat} {ι κ : Type}
    (term : ι → NormalOrderedTerm N)
    (higherCreators : κ → List (Fin N)) : Prop :=
  ∀ i : ι,
    (term i).annihilators = [] →
    2 ≤ (term i).creators.length →
    ∃ k : κ,
      (term i).creators.toFinset = (higherCreators k).toFinset

/--
Aggregate zero on represented higher-family supports extends to every higher
pure-creation support occurring in the mixed expansion, provided that support
is covered by the external family.
-/
theorem aggregateZero_on_mixed_higher_support
    {N : Nat} {ι κ : Type}
    [Fintype κ] [DecidableEq κ]
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (term : ι → NormalOrderedTerm N)
    (hAggregate :
      ∀ k : κ,
        higherCreationAggregateCoeff
          higherCoeff higherCreators (higherCreators k).toFinset = 0)
    (hcovered :
      HigherCreationMixedSupportCovered term higherCreators) :
    ∀ i : ι,
      (term i).annihilators = [] →
      2 ≤ (term i).creators.length →
      higherCreationAggregateCoeff
        higherCoeff higherCreators (term i).creators.toFinset = 0 := by
  intro i hann hlen
  obtain ⟨k, hk⟩ := hcovered i hann hlen
  rw [hk]
  exact hAggregate k

/--
CP52 final reduced periodic-overlap assembly.

The closed periodic-overlap model supplies separated witness data; CP50 gives
aggregate zero on represented higher supports; support coverage transfers that
result to mixed higher supports; and the existing mixed Row-1 theorem closes
Corollary 1.

Unlike the historical CP44 route, this theorem has no support-map injectivity
hypothesis.
-/
theorem corollary_one_from_periodic_overlap_aggregate_closed
    {N R : Nat} {ι κ : Type}
    [Fintype ι]
    [Fintype κ] [DecidableEq κ]
    (hN3 : 3 ≤ N)
    (hNR : 3 * R < N)
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
    (start : κ → Fin N)
    (hcreators :
      ∀ k : κ,
        (higherCreators k).toFinset ⊆
          cyclicBlock N R (start k))
    (hsupport :
      HigherCreationFamilyListSupport higherCreators)
    (hNodup :
      ∀ k : κ, (higherCreators k).Nodup)
    (hcovered :
      HigherCreationMixedSupportCovered term higherCreators)
    (hrep :
      PureCreationAggregateRepresentationMatches
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by

  let M :
      PeriodicOverlapCreationModel N R κ higherCreators :=
    periodicOverlapModel_closed
      start hcreators hNR

  have hatLeastTwo :
      ∀ k : κ, 2 ≤ (higherCreators k).toFinset.card :=
    higherCreationFamily_toFinset_card_ge_two
      higherCreators hsupport hNodup

  let hwitness :
      ∀ k : κ, HigherCreationWitnessData higherCreators k :=
    all_higherCreationWitnessData_of_finiteRange
      M.toFiniteRange
      hatLeastTwo
      hNodup

  have hSingleZero :
      singleCoeff = 0 :=
    single_creation_coefficients_zero_of_eigenstate
      hN3 singleCoeff singleEig hSingleEig

  have hAggregateRepresented :
      ∀ k : κ,
        higherCreationAggregateCoeff
          higherCoeff higherCreators (higherCreators k).toFinset = 0 :=
    all_higherCreation_aggregate_coefficients_zero_of_eigenstate
      (by omega)
      higherCoeff higherCreators higherEig hHigherEig
      hNodup hwitness

  have hMixedAggregate :
      ∀ i : ι,
        (term i).annihilators = [] →
        2 ≤ (term i).creators.length →
        higherCreationAggregateCoeff
          higherCoeff higherCreators (term i).creators.toFinset = 0 :=
    aggregateZero_on_mixed_higher_support
      higherCoeff higherCreators term
      hAggregateRepresented hcovered

  have hmixed :
      MixedRowOneCondition mixedCoeff term := by
    intro i hann hcre
    rcases pureCreationTerm_single_or_length_ge_two hann hcre with
      hsingle | hhigher
    · obtain ⟨j, hj⟩ := hsingle
      have hcoeff : mixedCoeff i = singleCoeff j :=
        hrep.single_match i j hann hj
      have hz : singleCoeff j = 0 := by
        have hfun := congrFun hSingleZero j
        simpa using hfun
      calc
        mixedCoeff i = singleCoeff j := hcoeff
        _ = 0 := hz
    · have hcoeff :
          mixedCoeff i =
            higherCreationAggregateCoeff
              higherCoeff higherCreators (term i).creators.toFinset :=
        hrep.higher_match i hann hhigher
      calc
        mixedCoeff i =
            higherCreationAggregateCoeff
              higherCoeff higherCreators (term i).creators.toFinset := hcoeff
        _ = 0 := hMixedAggregate i hann hhigher

  exact
    vacuum_eigenstate_of_mixedRowOne
      Ω mixedCoeff term hmixed hnonid

end LeanGioia
