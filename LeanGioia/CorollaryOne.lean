import LeanGioia.TableIRowOne

/-!
# LeanGioia.CorollaryOne

Checkpoint 18: vacuum-eigenstate assembly toward Corollary 1.

The source paper states:

> If `|W⟩` is an eigenstate of an extensive-local operator, then `|0̄⟩`
> is also an eigenstate.

The proof route is:

1. Table I Row 1 excludes every nontrivial pure-creation term.
2. Hence every remaining nonidentity normal-ordered term contains at least
   one annihilation operator.
3. Such terms annihilate the vacuum.
4. Therefore only the identity coefficient acts nontrivially on the vacuum.

The current repository has formalized Step 1 sector-by-sector.  This file
packages Steps 3–4 at the operator-expansion boundary, while keeping the
remaining "complete mixed expansion" bridge explicit.
-/

namespace LeanGioia

/-- The computational-basis vacuum state `|0̄⟩`. -/
def vacuumKet (N : ℕ) : State N :=
  basisState (vacuumBits N)

/--
An operator term is vacuum-annihilating if it sends the vacuum ket to zero.
This is the property supplied by normal-ordered terms containing at least
one annihilation operator.
-/
def VacuumAnnihilating {N : ℕ} (T : Operator N) : Prop :=
  T (vacuumKet N) = 0

/-- A finite sum of nonidentity terms that each annihilate the vacuum. -/
noncomputable def vacuumAnnihilatingFamilyOperator
    {N : ℕ} {ι : Type} [Fintype ι]
    (coeff : ι → ℂ) (term : ι → Operator N) :
    Operator N :=
  ∑ i : ι, coeff i • term i

/--
A finite linear combination of vacuum-annihilating terms also annihilates
the vacuum.
-/
theorem vacuumAnnihilatingFamilyOperator_apply_vacuum
    {N : ℕ} {ι : Type} [Fintype ι]
    (coeff : ι → ℂ) (term : ι → Operator N)
    (hterm : ∀ i : ι, VacuumAnnihilating (term i)) :
    vacuumAnnihilatingFamilyOperator coeff term (vacuumKet N) = 0 := by
  classical
  rw [vacuumAnnihilatingFamilyOperator]
  simp only [Finset.sum_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i hi
  rw [hterm i, mul_zero]

/--
Operator form matching the Corollary 1 conclusion after pure-creation terms
have been removed:

`G = Ω 1 + remainder`

where the remainder consists entirely of terms that annihilate the vacuum.
-/
noncomputable def corollaryOneOperator
    {N : ℕ} {ι : Type} [Fintype ι]
    (Ω : ℂ) (coeff : ι → ℂ) (term : ι → Operator N) :
    Operator N :=
  Ω • identityOperator N + vacuumAnnihilatingFamilyOperator coeff term

/--
The vacuum is an eigenstate of the Corollary-1-form operator, with
eigenvalue equal to the identity coefficient `Ω`.
-/
theorem vacuum_eigenstate_of_no_pure_creation_remainder
    {N : ℕ} {ι : Type} [Fintype ι]
    (Ω : ℂ) (coeff : ι → ℂ) (term : ι → Operator N)
    (hterm : ∀ i : ι, VacuumAnnihilating (term i)) :
    IsEigenstate
      (corollaryOneOperator Ω coeff term)
      (vacuumKet N) Ω := by
  apply (isEigenstate_iff_amplitudes
    (corollaryOneOperator Ω coeff term) (vacuumKet N) Ω).2
  intro b
  rw [corollaryOneOperator]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul]
  have hrem :
      vacuumAnnihilatingFamilyOperator coeff term (vacuumKet N) b = 0 := by
    have hz :=
      vacuumAnnihilatingFamilyOperator_apply_vacuum coeff term hterm
    exact congrFun hz b
  rw [hrem, add_zero]
  rfl

/--
Data boundary for the current formal route to Corollary 1.

`rowOne` records the verified exclusion of pure-creation coefficients.
`remainingTermsVacuumZero` records the next basis-level fact: every
remaining nonidentity term annihilates the vacuum.
-/
structure CorollaryOneExpansion
    {N : ℕ} {ι : Type} {κ : Type}
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (term : ι → Operator N) : Prop where
  rowOne : TableIRowOneConclusion singleCoeff higherCoeff
  remainingTermsVacuumZero : ∀ i : ι, VacuumAnnihilating (term i)

/--
Checkpoint-18 paper-facing assembly.

Given the already-formalized Table-I-Row-1 conclusion and an expansion of
all remaining nonidentity terms into vacuum-annihilating operators, the
vacuum is an eigenstate with eigenvalue `Ω`.
-/
theorem corollary_one_at_expansion_boundary
    {N : ℕ} {ι κ : Type} [Fintype ι]
    (Ω : ℂ)
    (singleCoeff : Fin N → ℂ)
    (higherCoeff : κ → ℂ)
    (coeff : ι → ℂ)
    (term : ι → Operator N)
    (hexp :
      CorollaryOneExpansion singleCoeff higherCoeff term) :
    IsEigenstate
      (corollaryOneOperator Ω coeff term)
      (vacuumKet N) Ω := by
  exact vacuum_eigenstate_of_no_pure_creation_remainder
    Ω coeff term hexp.remainingTermsVacuumZero

end LeanGioia
