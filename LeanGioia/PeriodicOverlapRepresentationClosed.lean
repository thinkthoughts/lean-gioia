import LeanGioia.PeriodicOverlapReduced
import LeanGioia.PureCreationRepresentationCorollary

/-!
# LeanGioia.PeriodicOverlapRepresentationClosed

Checkpoint 44: reunify the closed periodic-overlap/locality branch with the
reduced pure-creation representation branch.

The periodic-overlap model supplies `HigherCreationWitnessData`; the verified
single- and higher-creation sector theorems then give
`TableIRowOneConclusion`.  Checkpoints 42 and 43 allow that conclusion to
reach the mixed-expansion Corollary-1 theorem through
`PureCreationRepresentationMatches`, without `PureCreationSectorBridge`.

This is an end-to-end reunification checkpoint.
-/

namespace LeanGioia

/--
Checkpoint-44 end-to-end reunification.

Under the closed periodic-overlap model, structural higher-family list support
and nodup creator lists provide the witness data required by Table I Row 1.
The resulting sector coefficient conclusion is then transported to the mixed
normal-ordered expansion through `PureCreationRepresentationMatches`.
-/
theorem corollary_one_from_periodic_overlap_representation_closed
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
    (hinj :
      Function.Injective
        (fun k : κ => (higherCreators k).toFinset))
    (start : κ → Fin N)
    (hcreators :
      ∀ k : κ,
        (higherCreators k).toFinset ⊆
          cyclicBlock N R (start k))
    (hsupport :
      HigherCreationFamilyListSupport higherCreators)
    (hNodup :
      ∀ k : κ, (higherCreators k).Nodup)
    (hrep :
      PureCreationRepresentationMatches
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

  have hrow :
      TableIRowOneConclusion singleCoeff higherCoeff :=
    tableI_row_one_pure_creation_coefficients_zero
      hN3
      singleCoeff singleEig hSingleEig
      higherCoeff higherCreators higherEig hHigherEig
      hinj hwitness

  exact
    corollary_one_from_representation_matches
      Ω mixedCoeff term hnonid
      singleCoeff higherCoeff higherCreators
      hrow hrep

end LeanGioia
