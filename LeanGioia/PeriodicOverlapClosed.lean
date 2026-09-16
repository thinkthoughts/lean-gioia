import LeanGioia.OverlapCoverBridge
import LeanGioia.PeriodicOverlapContainment

/-!
# LeanGioia.PeriodicOverlapClosed

Checkpoint 35: close the periodic-overlap model and Corollary-1 assembly.

Checkpoint 34 discharged the remaining periodic arithmetic specification:
under `3 * R < N`, every exact overlap hull is contained in the explicit
`3R` interaction cover, and hence has cardinality strictly below `N`.

This checkpoint removes `OverlapOffsetBound` from the public model
construction and end-to-end Corollary-1 theorem.

The resulting chain now requires only the geometric scale condition

`3 * R < N`

together with creator support in range-`R` cyclic blocks.
-/

namespace LeanGioia

/--
Construct the periodic-overlap creation model directly from creator
support and the closed overlap-cardinality theorem.

No separate `OverlapOffsetBound` hypothesis remains.
-/
noncomputable def periodicOverlapModel_closed
    {N R : Nat} {ι : Type} [Fintype ι]
    {creators : ι → List (Fin N)}
    (start : ι → Fin N)
    (hcreators :
      ∀ i : ι,
        (creators i).toFinset ⊆
          cyclicBlock N R (start i))
    (hNR : 3 * R < N) :
    PeriodicOverlapCreationModel N R ι creators where

  start := start

  creators_in_support := by
    intro i
    exact hcreators i

  interaction_card_lt := by
    intro i
    exact
      overlapInteraction_card_lt_closed
        hNR
        (start i)

/--
Checkpoint-35 end-to-end closure.

Under the scale condition `3 * R < N`, creator support in range-`R`
cyclic blocks is sufficient to construct the exact periodic-overlap
model and discharge Corollary 1.

The temporary arithmetic hypothesis `OverlapOffsetBound` has disappeared
from the theorem interface.
-/
theorem corollary_one_from_periodic_overlap_closed
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
        (higherCreationFamilyOperator
          higherCoeff higherCreators)
        (wState N) higherEig)
    (hinj :
      Function.Injective
        (fun k : κ =>
          (higherCreators k).toFinset))
    (start : κ → Fin N)
    (hcreators :
      ∀ k : κ,
        (higherCreators k).toFinset ⊆
          cyclicBlock N R (start k))
    (hatLeastTwo :
      ∀ k : κ,
        2 ≤
          (higherCreators k).toFinset.card)
    (hNodup :
      ∀ k : κ,
        (higherCreators k).Nodup)
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff
        higherCoeff
        higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator
        Ω mixedCoeff term)
      (vacuumKet N) Ω := by

  let M :
      PeriodicOverlapCreationModel
        N R κ higherCreators :=
    periodicOverlapModel_closed
      start
      hcreators
      hNR

  exact
    corollary_one_from_periodicOverlap_creation_model
      hN3 Ω
      mixedCoeff term hnonid
      singleCoeff singleEig hSingleEig
      higherCoeff higherCreators
        higherEig hHigherEig
      hinj
      M
      hatLeastTwo hNodup
      hbridge

end LeanGioia
