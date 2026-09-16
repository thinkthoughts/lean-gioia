import LeanGioia.HigherCreationComplete

/-!
# LeanGioia.HigherCreationSupportFiber

Checkpoint 47: make duplicate higher-creation support labels explicit.

Checkpoint 46 identified the exact role of creator-support injectivity:
the current coefficient-isolation proof turns equality of creator supports
into equality of external family indices.

This checkpoint introduces the support fiber of an external higher-creation
family and the coefficient aggregated over that fiber.  It then proves that,
under the existing injectivity hypothesis, the fiber over the support of a
selected index is the singleton containing that index, so the aggregate
coefficient reduces to the selected coefficient.

Thus the current injective formulation is exhibited as the singleton-fiber
special case of a support-aggregated representation.
-/

namespace LeanGioia

/--
External family indices whose creator lists determine the finite support `S`.
-/
def higherCreationSupportFiber
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (creators : ι → List (Fin N))
    (S : Finset (Fin N)) : Finset ι :=
  Finset.univ.filter fun i => (creators i).toFinset = S

/--
The coefficient carried collectively by all external family indices with
creator support `S`.
-/
noncomputable def higherCreationAggregateCoeff
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (coeff : ι → ℂ)
    (creators : ι → List (Fin N))
    (S : Finset (Fin N)) : ℂ :=
  ∑ i ∈ higherCreationSupportFiber creators S, coeff i

/--
Every family index lies in the fiber over its own creator support.
-/
theorem mem_higherCreationSupportFiber_self
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (creators : ι → List (Fin N))
    (i : ι) :
    i ∈ higherCreationSupportFiber creators (creators i).toFinset := by
  simp [higherCreationSupportFiber]

/--
If creator supports label the external family injectively, the fiber over the
support of `i` is exactly the singleton `{i}`.
-/
theorem higherCreationSupportFiber_eq_singleton_of_injective
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (creators : ι → List (Fin N))
    (hinj :
      Function.Injective
        (fun i : ι => (creators i).toFinset))
    (i : ι) :
    higherCreationSupportFiber creators (creators i).toFinset = {i} := by
  ext j
  simp [higherCreationSupportFiber, hinj.eq_iff]

/--
Under support injectivity, aggregation over the support of a selected index
recovers exactly its individual coefficient.
-/
theorem higherCreationAggregateCoeff_eq_of_injective
    {N : Nat} {ι : Type} [Fintype ι] [DecidableEq ι]
    (coeff : ι → ℂ)
    (creators : ι → List (Fin N))
    (hinj :
      Function.Injective
        (fun i : ι => (creators i).toFinset))
    (i : ι) :
    higherCreationAggregateCoeff
      coeff creators (creators i).toFinset = coeff i := by
  rw [higherCreationAggregateCoeff,
    higherCreationSupportFiber_eq_singleton_of_injective creators hinj i]
  simp

end LeanGioia
