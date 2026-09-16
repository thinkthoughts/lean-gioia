import LeanGioia.PureCreationFamilySupport
import LeanGioia.PeriodicOverlapClosed

/-!
# LeanGioia.PeriodicOverlapReduced

Checkpoint 41: propagate the Checkpoint-40 family-support reduction through
the closed periodic-overlap route.

This checkpoint replaces the separate `toFinset.card ≥ 2` input to the
Corollary-1 assembly by `HigherCreationFamilyListSupport` plus `Nodup`.
The higher-family index type, creator-set injectivity, eigenstate data, and
`PureCreationSectorBridge` remain explicit representation inputs.
-/

namespace LeanGioia

/--
Checkpoint-41 propagation of the reduced higher-family support hypothesis
through the closed periodic-overlap Corollary-1 route.
-/
theorem corollary_one_from_periodic_overlap_list_support
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
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by
  have hatLeastTwo :
      ∀ k : κ, 2 ≤ (higherCreators k).toFinset.card :=
    higherCreationFamily_toFinset_card_ge_two
      higherCreators hsupport hNodup
  exact
    corollary_one_from_periodic_overlap_closed
      hN3 hNR Ω
      mixedCoeff term hnonid
      singleCoeff singleEig hSingleEig
      higherCoeff higherCreators higherEig hHigherEig
      hinj start hcreators
      hatLeastTwo hNodup hbridge

end LeanGioia
