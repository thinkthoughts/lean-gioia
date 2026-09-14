import LeanGioia.HigherCreationComplete

/-!
# LeanGioia.TableIRowOne

Checkpoint 17: package the two pure-creation branches corresponding to the
first row of Table I.

The source paper's first Table I row states that coefficients of
pure-creation operator strings vanish:

`n ≥ 1, m = 0  ⟹  c_{j₁...jₙ} = 0`.

The formalization has established the two cases separately:

* `n = 1`: closed end-to-end for the explicit single-creation operator;
* `n ≥ 2`: closed at coefficient level under explicit separated-witness /
  locality hypotheses.

This file packages those two verified branches without claiming that they
have already been embedded into one complete mixed-range operator expansion.
-/

namespace LeanGioia

/--
Per-index locality/witness data needed by the currently formalized
`n ≥ 2, m = 0` branch.
-/
structure HigherCreationWitnessData
    {N : ℕ} {ι : Type} [Fintype ι]
    (creators : ι → List (Fin N)) (i : ι) where
  witnessSite : Fin N
  atLeastTwo : 2 ≤ (creators i).toFinset.card
  nodup : (creators i).Nodup
  witnessOutside : witnessSite ∉ creators i
  locality :
    ∀ k : ι,
      SeparatedLocalCompetitor
        (creators i).toFinset witnessSite (creators k).toFinset

/--
If every higher-creation family member has suitable separated-witness
locality data, then every coefficient in that family vanishes.
-/
theorem all_higher_creation_coefficients_zero_of_eigenstate
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 0 < N)
    (coeff : ι → ℂ) (creators : ι → List (Fin N))
    (eig : ℂ)
    (hEig :
      IsEigenstate
        (higherCreationFamilyOperator coeff creators)
        (wState N) eig)
    (hinj :
      Function.Injective (fun i : ι => (creators i).toFinset))
    (hwitness :
      ∀ i : ι, HigherCreationWitnessData creators i) :
    ∀ i : ι, coeff i = 0 := by
  intro i
  let w := hwitness i
  exact higher_creation_coefficient_zero_of_eigenstate
    hN coeff creators eig hEig
    i w.witnessSite
    w.atLeastTwo
    w.nodup
    w.witnessOutside
    w.locality
    hinj

/--
Function-level form of the `n ≥ 2` pure-creation coefficient conclusion.
-/
theorem higher_creation_coefficients_eq_zero_of_eigenstate
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN : 0 < N)
    (coeff : ι → ℂ) (creators : ι → List (Fin N))
    (eig : ℂ)
    (hEig :
      IsEigenstate
        (higherCreationFamilyOperator coeff creators)
        (wState N) eig)
    (hinj :
      Function.Injective (fun i : ι => (creators i).toFinset))
    (hwitness :
      ∀ i : ι, HigherCreationWitnessData creators i) :
    coeff = 0 := by
  funext i
  exact all_higher_creation_coefficients_zero_of_eigenstate
    hN coeff creators eig hEig hinj hwitness i

/--
Paper-facing package for the two pure-creation branches currently verified.

`singleZero` is the `n = 1, m = 0` conclusion.
`higherZero` is the `n ≥ 2, m = 0` conclusion.
-/
structure TableIRowOneConclusion
    {N : ℕ} {ι : Type}
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : ι → ℂ) : Prop where
  singleZero : singleCoeff = 0
  higherZero : higherCoeff = 0

/--
Checkpoint-17 assembly theorem.

This packages both pure-creation branches as the coefficient conclusion
stated in the first row of Table I, while preserving the current formal
boundary for the higher-creation locality hypotheses.
-/
theorem tableI_row_one_pure_creation_coefficients_zero
    {N : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (hN3 : 3 ≤ N)
    (singleCoeff : Fin N → ℂ)
    (singleEig : ℂ)
    (hSingleEig :
      IsEigenstate
        (singleCreationOperator singleCoeff)
        (wState N) singleEig)
    (higherCoeff : ι → ℂ)
    (creators : ι → List (Fin N))
    (higherEig : ℂ)
    (hHigherEig :
      IsEigenstate
        (higherCreationFamilyOperator higherCoeff creators)
        (wState N) higherEig)
    (hinj :
      Function.Injective (fun i : ι => (creators i).toFinset))
    (hwitness :
      ∀ i : ι, HigherCreationWitnessData creators i) :
    TableIRowOneConclusion singleCoeff higherCoeff := by
  constructor
  · exact single_creation_coefficients_zero_of_eigenstate
      hN3 singleCoeff singleEig hSingleEig
  · exact higher_creation_coefficients_eq_zero_of_eigenstate
      (by omega) higherCoeff creators higherEig hHigherEig hinj hwitness

end LeanGioia
