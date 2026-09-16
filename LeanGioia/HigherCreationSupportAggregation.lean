import LeanGioia.CreationStringSupport

/-!
# LeanGioia.HigherCreationSupportAggregation

Checkpoint 49: aggregate higher-creation operator contributions inside one
finite creator-support fiber.

CP47 introduced `higherCreationSupportFiber` and
`higherCreationAggregateCoeff`.  CP48 proved that duplicate-free creator
lists with equal `List.toFinset` support determine the same `creationString`
operator.

CP49 connects those two results at the operator level.  If `i₀` is a family
index and every creator list is duplicate-free, then every term in the support
fiber over `(creators i₀).toFinset` has the same creation-string operator as
the selected representative `i₀`.  Consequently, the sum of all operator
contributions in that fiber equals the aggregate coefficient of the fiber
times the representative creation string.

This is a support-fiber aggregation checkpoint.  It does not yet regroup the
entire `higherCreationFamilyOperator` over all distinct supports, and it does
not yet remove creator-support injectivity from the higher-creation
coefficient theorem.
-/

namespace LeanGioia

/--
Membership in the support fiber over `creators i₀` identifies the finite
creator support of `i` with that of `i₀`.
-/
theorem toFinset_eq_of_mem_higherCreationSupportFiber
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (creators : ι → List (Fin N))
    (i₀ i : ι)
    (hi :
      i ∈ higherCreationSupportFiber creators (creators i₀).toFinset) :
    (creators i).toFinset = (creators i₀).toFinset := by
  simpa [higherCreationSupportFiber] using hi

/--
All duplicate-free creator lists in the support fiber over `i₀` determine the
same creation-string operator as the selected representative `i₀`.
-/
theorem creationString_eq_of_mem_higherCreationSupportFiber
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (creators : ι → List (Fin N))
    (hNodup : ∀ i : ι, (creators i).Nodup)
    (i₀ i : ι)
    (hi :
      i ∈ higherCreationSupportFiber creators (creators i₀).toFinset) :
    creationString (creators i) =
      creationString (creators i₀) := by
  apply creationString_eq_of_toFinset_eq
    (hNodup i)
    (hNodup i₀)
  exact toFinset_eq_of_mem_higherCreationSupportFiber creators i₀ i hi

/--
Checkpoint-49 support-fiber operator aggregation.

The operator contribution from every external family index in the support
fiber of `i₀` can be collected into one scalar coefficient multiplying the
representative creation string at `i₀`.

No creator-support injectivity hypothesis is required.
-/
theorem sum_higherCreationSupportFiber_eq_aggregate_smul
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (coeff : ι → ℂ)
    (creators : ι → List (Fin N))
    (hNodup : ∀ i : ι, (creators i).Nodup)
    (i₀ : ι) :
    (∑ i ∈ higherCreationSupportFiber creators (creators i₀).toFinset,
        coeff i • creationString (creators i)) =
      higherCreationAggregateCoeff
          coeff creators (creators i₀).toFinset •
        creationString (creators i₀) := by
  classical
  rw [higherCreationAggregateCoeff]
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [creationString_eq_of_mem_higherCreationSupportFiber
    creators hNodup i₀ i hi]

end LeanGioia
