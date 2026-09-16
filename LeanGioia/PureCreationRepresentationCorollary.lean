import LeanGioia.PureCreationRepresentation

/-!
# LeanGioia.PureCreationRepresentationCorollary

Checkpoint 43: propagate the reduced pure-creation representation interface
from Checkpoint 42 to the finite mixed-expansion Corollary-1 conclusion.

Checkpoint 42 derives `MixedRowOneCondition` from intrinsic creator-list
classification plus `PureCreationRepresentationMatches`.  The existing mixed
expansion theorem then turns that Row-1 condition, together with the
nonidentity condition, into the vacuum eigenstate conclusion.

This checkpoint is a representation-reduction propagation checkpoint.  It
does not alter the periodic-overlap geometry or reconstruct the external
higher-family indexing data.
-/

namespace LeanGioia

/--
Checkpoint-43 Corollary-1 assembly using the reduced representation interface
from Checkpoint 42 rather than `PureCreationSectorBridge`.
-/
theorem corollary_one_from_representation_matches
    {N : Nat} {ι κ : Type}
    [Fintype ι]
    (Ω : ℂ)
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (hnonid : NonidentityNormalOrderedFamily term)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (hrow : TableIRowOneConclusion singleCoeff higherCoeff)
    (hrep :
      PureCreationRepresentationMatches
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by
  have hmixed :
      MixedRowOneCondition mixedCoeff term :=
    mixedRowOneCondition_of_representation_matches
      mixedCoeff term
      singleCoeff higherCoeff higherCreators
      hrow hrep

  exact
    vacuum_eigenstate_of_mixedRowOne
      Ω mixedCoeff term hmixed hnonid

end LeanGioia
