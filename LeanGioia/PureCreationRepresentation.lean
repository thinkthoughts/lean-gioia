import LeanGioia.PureCreationClassification

/-!
# LeanGioia.PureCreationRepresentation

Checkpoint 42: reduce the mixed-expansion representation boundary after the
intrinsic single-versus-higher classification of Checkpoint 38.

This is a representation-hypothesis reduction checkpoint. It bypasses the
packaged classifier for the Row-1 argument and retains only the representation
facts that remain external.
-/

namespace LeanGioia

/--
Representation data remaining after creator-list shape classification has
been made intrinsic. There is no classifier and no separate coverage field.
-/
structure PureCreationRepresentationMatches
    {N : Nat} {ι κ : Type}
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
      ∃ k : κ,
        (term i).creators = higherCreators k ∧
        mixedCoeff i = higherCoeff k

/--
CP42: intrinsic classification plus branch-specific representation matches
derives the mixed Table-I-Row-1 condition directly.
-/
theorem mixedRowOneCondition_of_representation_matches
    {N : Nat} {ι κ : Type}
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (hrow : TableIRowOneConclusion singleCoeff higherCoeff)
    (hrep :
      PureCreationRepresentationMatches
        mixedCoeff term singleCoeff higherCoeff higherCreators) :
    MixedRowOneCondition mixedCoeff term := by
  intro i hann hcre
  rcases pureCreationTerm_single_or_length_ge_two hann hcre with hsingle | hhigher
  · obtain ⟨j, hj⟩ := hsingle
    have hcoeff : mixedCoeff i = singleCoeff j :=
      hrep.single_match i j hann hj
    have hz : singleCoeff j = 0 := by
      have hfun := congrFun hrow.singleZero j
      simpa using hfun
    calc
      mixedCoeff i = singleCoeff j := hcoeff
      _ = 0 := hz
  · obtain ⟨k, _hcreators, hcoeff⟩ :=
      hrep.higher_match i hann hhigher
    have hz : higherCoeff k = 0 := by
      have hfun := congrFun hrow.higherZero k
      simpa using hfun
    calc
      mixedCoeff i = higherCoeff k := hcoeff
      _ = 0 := hz

end LeanGioia
