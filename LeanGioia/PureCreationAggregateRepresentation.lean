import LeanGioia.HigherCreationAggregateZero
import LeanGioia.PureCreationRepresentation

/-!
# LeanGioia.PureCreationAggregateRepresentation

Checkpoint 51: integrate the support-aggregate higher-creation conclusion with
the mixed normal-ordered representation boundary.

CP42 represented a higher pure-creation mixed term by an individual external
higher-family index `k`, with coefficient equality

`mixedCoeff i = higherCoeff k`.

That interface is appropriate for the earlier injective-support route, where
each external higher coefficient is proved zero individually.

CP47--CP50 establish a representation-invariant alternative. Higher-family
terms with equal finite creator support determine the same creation-string
operator, so the coefficient visible to the operator is the aggregate
coefficient over the corresponding support fiber. CP50 proves that aggregate
coefficient vanishes under the separated-witness hypotheses, without requiring
injectivity of the creator-support map.

CP51 introduces a parallel representation interface whose higher branch matches
a mixed coefficient directly to that support aggregate. It then transports
single-coefficient zero plus higher support-aggregate zero to the existing
`MixedRowOneCondition`, and hence to the existing mixed-expansion Corollary-1
theorem.

This is an integration checkpoint. It deliberately leaves the historical
`TableIRowOneConclusion` and `PureCreationRepresentationMatches` interfaces
unchanged.
-/

namespace LeanGioia

/--
Representation data for the support-aggregate higher-creation route.

The single-creation branch retains the CP42 coefficient match.

The higher-creation branch matches a mixed coefficient to the aggregate
coefficient of the finite creator support carried by that mixed term, rather
than to an arbitrarily selected member of an external support fiber.
-/
structure PureCreationAggregateRepresentationMatches
    {N : Nat} {ι κ : Type}
    [Fintype κ] [DecidableEq κ]
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N)) : Prop where
  single_match :
    ∀ (i : ι) (j : Fin N),
      (term i).annihilators = [] →
      (term i).creators = [j] →
      mixedCoeff i = singleCoeff j
  higher_match :
    ∀ i : ι,
      (term i).annihilators = [] →
      2 ≤ (term i).creators.length →
      mixedCoeff i =
        higherCreationAggregateCoeff
          higherCoeff higherCreators (term i).creators.toFinset

/--
Support-aggregate Row-1 data.

This is intentionally parallel to, rather than a replacement for,
`TableIRowOneConclusion`.

The higher field records the representation-invariant conclusion established
by the CP47--CP50 route.
-/
structure AggregateTableIRowOneConclusion
    {N : Nat} {κ : Type}
    [Fintype κ] [DecidableEq κ]
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N)) : Prop where
  singleZero : singleCoeff = 0
  higherAggregateZero :
    ∀ k : κ,
      higherCreationAggregateCoeff
        higherCoeff higherCreators (higherCreators k).toFinset = 0

/--
CP51 representation transport.

If the single-creation coefficients vanish and every finite support has zero
aggregate coefficient, then the aggregate representation interface implies
the existing mixed Row-1 condition.
-/
theorem mixedRowOneCondition_of_aggregate_representation_matches
    {N : Nat} {ι κ : Type}
    [Fintype κ] [DecidableEq κ]
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (hSingleZero : singleCoeff = 0)
    (hAggregateZero :
      ∀ S : Finset (Fin N),
        higherCreationAggregateCoeff higherCoeff higherCreators S = 0)
    (hrep :
      PureCreationAggregateRepresentationMatches
        mixedCoeff term singleCoeff higherCoeff higherCreators) :
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
      _ = 0 := hAggregateZero (term i).creators.toFinset

/--
CP51 Corollary-1 integration at the support-aggregate representation boundary.

No higher-support injectivity hypothesis occurs in this theorem.
-/
theorem corollary_one_from_aggregate_representation_matches
    {N : Nat} {ι κ : Type}
    [Fintype ι]
    [Fintype κ] [DecidableEq κ]
    (Ω : ℂ)
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (hnonid : NonidentityNormalOrderedFamily term)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (hSingleZero : singleCoeff = 0)
    (hAggregateZero :
      ∀ S : Finset (Fin N),
        higherCreationAggregateCoeff higherCoeff higherCreators S = 0)
    (hrep :
      PureCreationAggregateRepresentationMatches
        mixedCoeff term singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by
  have hmixed :
      MixedRowOneCondition mixedCoeff term :=
    mixedRowOneCondition_of_aggregate_representation_matches
      mixedCoeff term
      singleCoeff higherCoeff higherCreators
      hSingleZero hAggregateZero hrep

  exact
    vacuum_eigenstate_of_mixedRowOne
      Ω mixedCoeff term hmixed hnonid

end LeanGioia
