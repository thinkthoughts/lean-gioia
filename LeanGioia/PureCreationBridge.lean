import LeanGioia.MixedExpansion

/-!
# LeanGioia.PureCreationBridge

Checkpoint 21: derive the mixed Table-I-Row-1 condition from the
already-verified single-creation and higher-creation sector theorems.

Checkpoint 17 packages the two pure-creation sector conclusions:

* one creator: every coefficient vanishes;
* two or more creators: every coefficient vanishes, under the explicit
  separated-witness/locality hypotheses.

Checkpoint 20 uses the mixed-expansion condition

`annihilators = [] ∧ creators ≠ [] → coefficient = 0`

to derive Corollary 1.

This file supplies the missing representation bridge between those two
levels.
-/

namespace LeanGioia

/--
A pure-creation term in the mixed expansion is represented either by the
single-creation sector or by the higher-creation sector.
-/
inductive PureCreationSector (N : ℕ) (κ : Type)
  | single : Fin N → PureCreationSector N κ
  | higher : κ → PureCreationSector N κ

/-- Creator list represented by a pure-creation sector label. -/
def PureCreationSector.creatorList
    {N : ℕ} {κ : Type}
    (higherCreators : κ → List (Fin N)) :
    PureCreationSector N κ → List (Fin N)
  | .single j => [j]
  | .higher k => higherCreators k

/-- Coefficient represented by a pure-creation sector label. -/
def PureCreationSector.coefficient
    {N : ℕ} {κ : Type}
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ) :
    PureCreationSector N κ → ℂ
  | .single j => singleCoeff j
  | .higher k => higherCoeff k

/--
Representation data identifying every nonidentity pure-creation term in a
mixed normal-ordered expansion with one of the two already-formalized
pure-creation sectors.

The two `match` fields ensure that the bridge preserves both the creator
list and its coefficient; `coverage` says every mixed term with no
annihilators and at least one creator is represented.
-/
structure PureCreationSectorBridge
    {N : ℕ} {ι κ : Type}
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N)) where
  classify : ι → Option (PureCreationSector N κ)
  coverage :
    ∀ i : ι,
      (term i).annihilators = [] →
      (term i).creators ≠ [] →
      ∃ s : PureCreationSector N κ, classify i = some s
  creators_match :
    ∀ (i : ι) (s : PureCreationSector N κ),
      classify i = some s →
      (term i).creators =
        PureCreationSector.creatorList higherCreators s
  coefficient_match :
    ∀ (i : ι) (s : PureCreationSector N κ),
      classify i = some s →
      mixedCoeff i =
        PureCreationSector.coefficient singleCoeff higherCoeff s

/--
A packaged Table-I-Row-1 sector conclusion mechanically implies the mixed
Row-1 condition once the representation bridge is supplied.
-/
theorem mixedRowOneCondition_of_sector_conclusion
    {N : ℕ} {ι κ : Type}
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (higherCreators : κ → List (Fin N))
    (hrow : TableIRowOneConclusion singleCoeff higherCoeff)
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    MixedRowOneCondition mixedCoeff term := by
  intro i hann hcre
  obtain ⟨s, hs⟩ := hbridge.coverage i hann hcre
  have hcoeff :=
    hbridge.coefficient_match i s hs
  cases s with
  | single j =>
      have hz : singleCoeff j = 0 := by
        have hfun := congrFun hrow.singleZero j
        simpa using hfun
      calc
        mixedCoeff i = singleCoeff j := by
          simpa [PureCreationSector.coefficient] using hcoeff
        _ = 0 := hz
  | higher k =>
      have hz : higherCoeff k = 0 := by
        have hfun := congrFun hrow.higherZero k
        simpa using hfun
      calc
        mixedCoeff i = higherCoeff k := by
          simpa [PureCreationSector.coefficient] using hcoeff
        _ = 0 := hz

/--
Use the actual verified sector theorems from Checkpoint 17 to derive the
mixed Table-I-Row-1 coefficient condition.
-/
theorem mixedRowOneCondition_of_verified_pure_creation_sectors
    {N : ℕ} {ι κ : Type}
    [Fintype κ] [DecidableEq κ]
    (hN3 : 3 ≤ N)
    (mixedCoeff : ι → ℂ)
    (term : ι → NormalOrderedTerm N)
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
    (hwitness :
      ∀ k : κ, HigherCreationWitnessData higherCreators k)
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    MixedRowOneCondition mixedCoeff term := by
  have hrow :
      TableIRowOneConclusion singleCoeff higherCoeff :=
    tableI_row_one_pure_creation_coefficients_zero
      hN3
      singleCoeff singleEig hSingleEig
      higherCoeff higherCreators higherEig hHigherEig
      hinj hwitness
  exact mixedRowOneCondition_of_sector_conclusion
    mixedCoeff term
    singleCoeff higherCoeff higherCreators
    hrow hbridge

/--
Checkpoint-21 end-to-end assembly at the current locality boundary.

The verified W-eigenstate results for both pure-creation sectors now feed
the finite mixed expansion directly.  Together with the nonidentity
condition from Checkpoint 20, Lean concludes that the vacuum is an
eigenstate with eigenvalue equal to the identity coefficient `Ω`.
-/
theorem corollary_one_from_verified_pure_creation_sectors
    {N : ℕ} {ι κ : Type}
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
    (hwitness :
      ∀ k : κ, HigherCreationWitnessData higherCreators k)
    (hbridge :
      PureCreationSectorBridge
        mixedCoeff term
        singleCoeff higherCoeff higherCreators) :
    IsEigenstate
      (mixedNormalOrderedOperator Ω mixedCoeff term)
      (vacuumKet N) Ω := by
  have hrow :
      MixedRowOneCondition mixedCoeff term :=
    mixedRowOneCondition_of_verified_pure_creation_sectors
      hN3
      mixedCoeff term
      singleCoeff singleEig hSingleEig
      higherCoeff higherCreators higherEig hHigherEig
      hinj hwitness hbridge
  exact vacuum_eigenstate_of_mixedRowOne
    Ω mixedCoeff term hrow hnonid

end LeanGioia
